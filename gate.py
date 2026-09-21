#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gate.py —— iptv-api 结果质量守门（放在仓库根目录，紧随 iptv-api 生成结果之后运行）

为什么需要它
------------
iptv-api 的测速（utils/speed.py 的 get_result）用 asyncio.gather 并发下载 5 个分片，
却把各分片耗时"相加"当作总时间。带宽受限时每路只拿到 B/5，代入推导：

    total_size = 5S,  total_time = 5 x (5S/B) = 25S/B
    speed = total_size / total_time = B/5        <- 恒定低估 5 倍

配合 min_speed = 0.5，等于实际要求 2.5 MB/s ≈ 20 Mbps，会误杀大量够用的源；
同时低码率源因分片小、更容易在 4s 超时内下完而获得奖励 —— 池子被推向低画质。
本脚本改用 headroom = 媒体时长 / 下载耗时，直接回答"下载能不能跟上播放"。

实测效果（对 nid12345/iptv-api 的 output/result.m3u 随机抽 60 条）：
    仅 13 条可播（21.7%），47 条不可用（78.3%）

两种模式
--------
  --no-network   只做结构性过滤：协议 / 域名集中度 / 每频道条数 / 去重。
                 可在 GitHub Actions（runner 在海外）安全运行。
  默认           完整质量探测。**必须在国内网络运行**（本机 / OpenWrt），
                 否则海外链路会把国内源大面积误判为不可用。

用法
----
  # 本机（推荐，每天定时，完整探测）
  python3 gate.py --src output/result.m3u --dst output/gated.m3u \
                  --min-headroom 1.5 --max-per-channel 6 --report gate_report.json

  # GitHub Actions（海外，仅结构性过滤）
  python3 gate.py --src output/result.m3u --dst output/gated.m3u --no-network
"""

from __future__ import annotations

import argparse
import json
import re
import ssl
import statistics
import sys
import threading
import time
import urllib.error
import urllib.request
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import urljoin, urlsplit

BAD_SCHEMES = ("rtmp://", "rtsp://", "rtp://", "udp://", "mms://")
DEFAULT_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")


# --------------------------------------------------------------------------
# 解析 / 工具
# --------------------------------------------------------------------------
def parse_playlist(path):
    """读订阅文件，返回 (items, fmt)，fmt ∈ {'m3u', 'txt'}。

    两种格式都支持，并**保持原格式输出**（下游 Worker/播放器无需改动）：
      M3U：  #EXTM3U / #EXTINF:-1 ...,频道名 / 下一行 URL
      TXT：  组名,#genre#  /  频道名,URL        （DIYP / TVBox / iptv-api 的 txt 结果）

    items 元素: {'extinf','name','url','group'}
    """
    out, extinf, group = [], None, ""
    fmt = None
    with open(path, encoding="utf-8", errors="ignore") as f:
        for raw in f:
            line = raw.rstrip("\r\n")
            s = line.strip()
            if not s:
                continue
            if s.startswith("#EXTM3U"):
                fmt = fmt or "m3u"
                continue
            if s.startswith("#EXTINF"):
                fmt = "m3u"
                extinf = line
                continue
            if s.startswith("#"):
                continue
            if extinf is not None:
                out.append({"extinf": extinf,
                            "name": extinf.split(",")[-1].strip(),
                            "url": s, "group": group})
                extinf = None
                continue
            # TXT 分组行：组名,#genre#   （注意：不以 # 开头）
            if s.endswith("#genre#"):
                fmt = "txt"
                group = s[: -len("#genre#")].rstrip(",").strip()
                continue
            if "," in s and "://" in s:
                head, _, tail = s.rpartition(",")
                tail = tail.strip()
                if tail.startswith(("http", "rtmp", "rtsp", "rtp", "udp")):
                    fmt = fmt or "txt"
                    nm = head.strip() or f"ch{len(out) + 1}"
                    out.append({"extinf": f"#EXTINF:-1,{nm}", "name": nm,
                                "url": tail, "group": group})
    return out, (fmt or "m3u")


def write_playlist(path, items, fmt):
    """按输入时的格式写回，保证下游无需任何改动"""
    with open(path, "w", encoding="utf-8") as f:
        if fmt == "txt":
            cur = None
            for x in items:
                g = x.get("group") or "未分组"
                if g != cur:
                    cur = g
                    f.write(f"{g},#genre#\n")
                f.write(f"{x['name']},{x['url']}\n")
        else:
            f.write("#EXTM3U\n")
            for x in items:
                f.write(x["extinf"] + "\n")
                f.write(x["url"] + "\n")


def host_of(url):
    try:
        return (urlsplit(url).hostname or "").lower()
    except Exception:
        return ""


def scheme_of(url):
    return url.split("://", 1)[0].lower() if "://" in url else ""


# --------------------------------------------------------------------------
# 探测（精简版 HLS 质量探测，含 BYTERANGE 支持）
# --------------------------------------------------------------------------
def make_opener(insecure):
    handlers = [urllib.request.ProxyHandler({})]
    ctx = ssl.create_default_context()
    if insecure:
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
    handlers.append(urllib.request.HTTPSHandler(context=ctx))
    return urllib.request.build_opener(*handlers)


def _fetch_impl(url, opener, ua, timeout, referer=None, byte_range=None):
    r = {"ok": False, "bytes": 0, "ms": None, "status": None,
         "final": url, "data": b"", "err": ""}
    h = {"User-Agent": ua, "Accept": "*/*", "Accept-Encoding": "identity"}
    if referer:
        h["Referer"] = referer
    limit = None
    if byte_range:
        ln, off = byte_range
        h["Range"] = f"bytes={off}-{off + ln - 1}"
        limit = ln + 65536
    t0 = time.perf_counter()
    try:
        with opener.open(urllib.request.Request(url, headers=h), timeout=timeout) as resp:
            first = resp.read(min(8192, limit) if limit else 8192)
            rest = resp.read(max(0, limit - len(first))) if limit else resp.read()
            r["data"] = first + rest
            r["bytes"] = len(first) + len(rest)
            r["ms"] = (time.perf_counter() - t0) * 1000.0
            r["status"] = getattr(resp, "status", 200)
            r["final"] = resp.geturl()
            r["ok"] = True
    except Exception as e:  # noqa: BLE001
        r["ms"] = (time.perf_counter() - t0) * 1000.0
        r["err"] = f"{type(e).__name__}: {str(e)[:90]}"
    return r


def fetch(url, opener, ua, timeout, referer=None, byte_range=None, hard_timeout=None):
    """带硬超时的包装 —— `urllib` 的 timeout 不约束 DNS 解析。

    实测 531 条源里有 11 条会让 getaddrinfo 挂住，把整个任务从 15 分钟
    拖到 45 分钟以上。守护线程兜底后，超时的源直接判失败，不拖累整体。
    """
    hard = hard_timeout if hard_timeout else max(timeout * 2 + 6, 20.0)
    box = {}

    def runner():
        try:
            box.update(_fetch_impl(url, opener, ua, timeout, referer, byte_range))
        except Exception as e:  # noqa: BLE001
            box["err"] = f"{type(e).__name__}: {str(e)[:90]}"

    th = threading.Thread(target=runner, daemon=True)
    th.start()
    th.join(hard)
    if th.is_alive():
        return {"ok": False, "bytes": 0, "ms": hard * 1000.0, "status": None,
                "final": url, "data": b"",
                "err": f"硬超时 (>{hard:.0f}s)"}
    return box or {"ok": False, "bytes": 0, "ms": None, "status": None,
                   "final": url, "data": b"", "err": "未返回结果"}


def parse_attrs(line):
    body = line.split(":", 1)[1] if ":" in line else ""
    return {m.group(1).upper(): m.group(2).strip('"')
            for m in re.finditer(r'([A-Za-z0-9\-]+)=("[^"]*"|[^,]*)', body)}


def parse_master(text):
    out, lines = [], text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("#EXT-X-STREAM-INF"):
            for j in range(i + 1, len(lines)):
                cand = lines[j].strip()
                if cand and not cand.startswith("#"):
                    a = parse_attrs(line)
                    a["URI"] = cand
                    out.append(a)
                    break
    return out


def pick_variant(variants, max_bandwidth=0):
    """最高分辨率优先，同分辨率优先 AAC（避免选中 Dolby 导致老设备无声）"""
    def area(v):
        m = re.match(r"(\d+)\s*x\s*(\d+)", v.get("RESOLUTION") or "")
        return int(m.group(1)) * int(m.group(2)) if m else 0

    def arank(v):
        c = (v.get("CODECS") or "").lower()
        return 3 if "mp4a" in c else (1 if ("ac-3" in c or "ec-3" in c) else 2)

    pool = variants
    if max_bandwidth:
        allow = [v for v in variants if int(v.get("BANDWIDTH") or 0) <= max_bandwidth]
        if allow:
            pool = allow
    best = max(area(v) for v in pool)
    at = [v for v in pool if area(v) == best] or pool
    at.sort(key=lambda v: (arank(v), int(v.get("BANDWIDTH") or 0)))
    return at[-1]


def parse_media(text):
    """返回 (target, segs)，segs 元素 {'dur','uri','range'}；支持 EXT-X-BYTERANGE"""
    target, segs, pending = None, [], None
    br_len = br_off = None
    last_end = {}

    def flush(uri):
        nonlocal br_len, br_off
        rng = None
        if br_len is not None:
            off = br_off if br_off is not None else last_end.get(uri, 0)
            last_end[uri] = off + br_len
            rng = (br_len, off)
        segs.append({"dur": pending, "uri": uri, "range": rng})
        br_len = br_off = None

    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("#EXT-X-TARGETDURATION:"):
            try:
                target = float(line.split(":", 1)[1])
            except ValueError:
                pass
        elif line.startswith("#EXTINF:"):
            try:
                pending = float(line[len("#EXTINF:"):].split(",")[0])
            except ValueError:
                pending = None
        elif line.startswith("#EXT-X-BYTERANGE:"):
            spec = line.split(":", 1)[1].strip()
            try:
                if "@" in spec:
                    a, b = spec.split("@", 1)
                    br_len, br_off = int(a), int(b)
                else:
                    br_len, br_off = int(spec), None
            except ValueError:
                br_len = br_off = None
        elif line and not line.startswith("#"):
            flush(line)
            pending = None
    return target, segs


def probe(url, opener, ua, timeout, segments, referer=None, budget=25.0):
    """返回 {'ok','headroom','kbps','reason'}"""
    res = {"ok": False, "headroom": None, "kbps": None, "reason": ""}
    t0 = time.perf_counter()
    pl = fetch(url, opener, ua, timeout, referer)
    if not pl["ok"]:
        res["reason"] = pl["err"]
        return res
    text = pl["data"].decode("utf-8", "ignore")
    if "#EXTM3U" not in text[:400]:
        res["reason"] = "非 m3u8 内容"
        return res

    media_url, media_text = pl["final"], text
    vs = parse_master(text)
    if vs:
        ch = pick_variant(vs)
        media_url = urljoin(pl["final"], ch["URI"])
        sub = fetch(media_url, opener, ua, timeout, referer)
        if not sub["ok"]:
            res["reason"] = "变体拉取失败: " + sub["err"]
            return res
        media_text, media_url = sub["data"].decode("utf-8", "ignore"), sub["final"]

    target, segs = parse_media(media_text)
    if not segs:
        res["reason"] = "无分片"
        return res

    n_ok, wall, secs, bytes_ = 0, 0.0, 0.0, 0
    for s in segs[:segments]:
        if time.perf_counter() - t0 > budget:
            break
        sg = fetch(urljoin(media_url, s["uri"]), opener, ua, timeout, referer, s["range"])
        if not sg["ok"] or sg["bytes"] == 0:
            continue
        n_ok += 1
        wall += sg["ms"] / 1000.0
        bytes_ += sg["bytes"]
        secs += s["dur"] if s["dur"] and s["dur"] > 0 else (target or 0)
    if n_ok == 0 or wall <= 0:
        res["reason"] = "分片全部下载失败"
        return res

    res["ok"] = True
    res["headroom"] = secs / wall
    if secs > 0:
        res["kbps"] = round(bytes_ * 8 / secs / 1000)
    return res


# --------------------------------------------------------------------------
# 过滤阶段
# --------------------------------------------------------------------------
def stage_scheme(items, report):
    kept = [x for x in items if not x["url"].lower().startswith(BAD_SCHEMES)]
    report["dropped_protocol"] = len(items) - len(kept)
    return kept


def stage_dedupe(items, report):
    seen, kept = set(), []
    for x in items:
        k = (x["name"], x["url"])
        if k in seen:
            continue
        seen.add(k)
        kept.append(x)
    report["dropped_duplicate"] = len(items) - len(kept)
    return kept


def stage_cap_host(items, ratio, report):
    """限制单域名占比，消除"看似 20 个源、其实同一个上游"的假冗余。

    返回 (kept, dropped)，dropped 保留下来用于"频道保底"补回。
    """
    cap = max(1, int(len(items) * ratio))
    used, kept, dropped = Counter(), [], []
    for x in items:
        h = host_of(x["url"])
        if used[h] >= cap:
            dropped.append(x)
            continue
        used[h] += 1
        kept.append(x)
    report["dropped_host_cap"] = len(dropped)
    report["host_cap_per_domain"] = cap
    return kept, dropped


# --------------------------------------------------------------------------
# 主流程
# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="iptv-api 结果质量守门")
    ap.add_argument("--src", required=True, help="输入 m3u（iptv-api 的 output/result.m3u）")
    ap.add_argument("--dst", required=True, help="输出 m3u（TVBox/MyTV 订阅指向它）")
    ap.add_argument("--no-network", action="store_true",
                    help="只做结构性过滤（GitHub Actions 用）")
    ap.add_argument("--min-headroom", type=float, default=1.5,
                    help="最低下载余量，低于此值判定为会卡（默认 1.5）")
    ap.add_argument("--min-kbps", type=int, default=0,
                    help="最低码率，用于剔除混入的纯音频流（0=不启用）")
    ap.add_argument("--max-per-channel", type=int, default=6,
                    help="每频道最多保留几个源（默认 6）")
    ap.add_argument("--min-per-channel", type=int, default=1,
                    help="每频道至少保留几个（不足则放宽阈值，默认 1）")
    ap.add_argument("--host-ratio", type=float, default=0.15,
                    help="单域名最多占总条数比例（默认 0.15）")
    ap.add_argument("--segments", type=int, default=3, help="每个源下载几个分片（默认 3）")
    ap.add_argument("--timeout", type=float, default=8.0, help="单请求超时秒数")
    ap.add_argument("--budget", type=float, default=25.0, help="单源探测时间预算秒数")
    ap.add_argument("--jobs", type=int, default=8, help="并发数")
    ap.add_argument("--limit", type=int, default=0, help="只探测前 N 条（0=全部，用于试跑）")
    ap.add_argument("--ua", default=DEFAULT_UA)
    ap.add_argument("--referer", default=None)
    ap.add_argument("--insecure", action="store_true")
    ap.add_argument("--report", default=None, help="输出 JSON 报告的路径")
    opts = ap.parse_args()

    report = {"src": opts.src, "dst": opts.dst, "mode": "no-network" if opts.no_network else "full"}
    items, fmt = parse_playlist(opts.src)
    report["format"] = fmt
    report["input_items"] = len(items)
    report["input_hosts"] = len({host_of(x["url"]) for x in items})
    if not items:
        print("输入为空，拒绝写出（空结果保护）", file=sys.stderr)
        return 2

    # 阶段 1-3：结构性过滤
    items = stage_scheme(items, report)
    items = stage_dedupe(items, report)

    # 阶段 4：网络探测
    if opts.no_network:
        report["probe"] = "skipped"
        for x in items:
            x["headroom"] = None
            x["kbps"] = None
            x["rank"] = 0.0
    else:
        if opts.limit:
            items = items[: opts.limit]
        report["probed"] = len(items)
        opener = make_opener(opts.insecure)
        print(f"探测 {len(items)} 条（并发 {opts.jobs}，分片 {opts.segments}）...", file=sys.stderr)
        t0 = time.time()
        with ThreadPoolExecutor(max_workers=max(1, opts.jobs)) as ex:
            futs = {ex.submit(probe, x["url"], opener, opts.ua, opts.timeout,
                              opts.segments, opts.referer, opts.budget): x for x in items}
            for i, fut in enumerate(as_completed(futs), 1):
                x = futs[fut]
                try:
                    r = fut.result()
                except Exception as e:  # noqa: BLE001
                    r = {"ok": False, "headroom": None, "kbps": None, "reason": str(e)[:80]}
                x["headroom"], x["kbps"] = r["headroom"], r["kbps"]
                x["alive"], x["reason"] = r["ok"], r["reason"]
                x["rank"] = (r["headroom"] or 0.0)
                if i % 100 == 0 or i == len(futs):
                    print(f"  进度 {i}/{len(futs)}", file=sys.stderr)
        report["probe_seconds"] = round(time.time() - t0, 1)
        alive = sum(1 for x in items if x.get("alive"))
        report["probe_alive"] = alive
        report["probe_alive_ratio"] = round(alive / len(items), 4) if items else 0

    # 阶段 5：域名集中度（按质量优先保留）
    items.sort(key=lambda x: -x["rank"])
    kept, dropped = stage_cap_host(items, opts.host_ratio, report)

    # 频道保底：仅当某频道在 kept 中一条不剩时，从其被剔除的源里补回最好的几条。
    # 可用性优先于集中度 —— 宁可某频道略超占比，也不能让整个频道从订阅里消失。
    have = {x["name"] for x in kept}
    by_drop = defaultdict(list)
    for x in dropped:
        by_drop[x["name"]].append(x)
    restored = []
    for chan, lst in by_drop.items():
        if chan not in have:
            restored.extend(lst[: max(1, opts.min_per_channel)])
    report["restored_channels"] = len({x["name"] for x in restored})
    report["restored_items"] = len(restored)
    items = kept + restored

    # 阶段 6：每频道配额
    by_chan = defaultdict(list)
    for x in items:
        by_chan[x["name"]].append(x)

    gated, warn = [], []
    for chan, lst in by_chan.items():
        if opts.no_network:
            pick = lst[: opts.max_per_channel]
        else:
            good = [x for x in lst
                    if x.get("alive") and (x["headroom"] or 0) >= opts.min_headroom
                    and (opts.min_kbps == 0 or (x["kbps"] or 0) >= opts.min_kbps)]
            if len(good) < opts.min_per_channel:
                fallback = [x for x in lst if x.get("alive")]
                if not fallback:
                    # 全部不可达：保留原样 1 条，避免把条目信息（如 iptv-api 写入的
                    # "更新时间"版本标记）直接从订阅里抹掉
                    warn.append({"channel": chan, "issue": "无可播源，保留原样 1 条"})
                    gated.extend(lst[:1])
                    continue
                if len(good) < opts.min_per_channel:
                    warn.append({"channel": chan,
                                 "issue": f"仅 {len(fallback)} 条可播，已放宽阈值保留最好的",
                                 "best_headroom": round(fallback[0]["headroom"] or 0, 2)})
                good = fallback[: max(opts.min_per_channel, len(good))]
            pick = good[: opts.max_per_channel]
        gated.extend(pick)

    gated.sort(key=lambda x: (x.get("group", ""), x["name"], -x["rank"]))
    report["output_items"] = len(gated)
    report["output_channels"] = len({x["name"] for x in gated})
    report["output_hosts"] = len({host_of(x["url"]) for x in gated})
    report["warnings"] = warn[:40]
    report["warnings_total"] = len(warn)

    if not gated:
        print("过滤后为空，拒绝写出（避免空文件覆盖可用结果）", file=sys.stderr)
        return 3

    write_playlist(opts.dst, gated, fmt)

    print(f"输入 {report['input_items']} 条 -> 输出 {report['output_items']} 条"
          f"（{report['output_channels']} 个频道）")
    print(f"  协议剔除 {report['dropped_protocol']}  重复剔除 {report['dropped_duplicate']}"
          f"  域名封顶剔除 {report['dropped_host_cap']}（上限 {report['host_cap_per_domain']}/域名，"
          f"保底补回 {report['restored_items']} 条 / {report['restored_channels']} 个频道）")
    if report.get("probe") != "skipped":
        print(f"  实测可播 {report['probe_alive']}/{report['probed']}"
              f"（{report['probe_alive_ratio']*100:.1f}%）")
    if warn:
        print(f"  ! {len(warn)} 个频道存在风险，样本：")
        for w in warn[:5]:
            print(f"      {w['channel']}: {w['issue']}")

    if opts.report:
        with open(opts.report, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        print(f"报告已写入 {opts.report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
