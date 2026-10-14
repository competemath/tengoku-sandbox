#!/usr/bin/env python3
"""What the runner looked like while a job ran: disk, memory, the biggest processes, and the kernel's out-of-memory kills.

The queue and the nightly have each died of the runner itself (no space left on the device, a process killed for memory) and each time the
cause had to be found by running probe jobs. This leaves the evidence behind in the job: a sample every TELEMETRY_INTERVAL seconds (default 20) in
telemetry.jsonl in the working directory, and a short summary for the job's page.

  runner_telemetry.py watch [--max N]   append a sample per interval until killed (or N samples)
  runner_telemetry.py summary           print the summary of telemetry.jsonl as markdown; never fails (no samples: says so)

No command takes a path: the file is the working directory's telemetry.jsonl.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

LOG = Path("telemetry.jsonl")
OOM = re.compile(r"out of memory|killed process|oom-kill", re.IGNORECASE)
GB = 1024**3


def meminfo() -> dict[str, int]:
    """/proc/meminfo in MB (empty where there is none: the sample then has no memory figures)."""
    try:
        text = Path("/proc/meminfo").read_text(encoding="utf-8")
    except OSError:
        return {}
    kb = {m.group(1): int(m.group(2)) for m in re.finditer(r"^(\w+):\s+(\d+) kB", text, re.M)}
    total, avail = kb.get("MemTotal", 0), kb.get("MemAvailable", 0)
    return {
        "mem_used_mb": (total - avail) // 1024,
        "mem_avail_mb": avail // 1024,
        "swap_used_mb": (kb.get("SwapTotal", 0) - kb.get("SwapFree", 0)) // 1024,
    }


def top_processes(n: int = 3) -> list[str]:
    """The n biggest processes by resident memory, as 'name=MB'."""
    r = subprocess.run(["ps", "-eo", "rss,comm"], capture_output=True, text=True, check=False)
    rows = []
    for line in r.stdout.splitlines()[1:]:
        rss, _, name = line.strip().partition(" ")
        if rss.isdigit():
            rows.append((int(rss), name.strip().rsplit("/", 1)[-1]))
    return [f"{name}={rss // 1024}" for rss, name in sorted(rows, reverse=True)[:n]]


def sample() -> dict:
    d = shutil.disk_usage("/")
    return {
        "t": int(time.time()),
        "disk_used_gb": round((d.total - d.free) / GB, 1),
        "disk_free_gb": round(d.free / GB, 1),
        **meminfo(),
        "top": top_processes(),
    }


def oom_lines() -> list[str]:
    """The kernel's out-of-memory lines (the runner lets `sudo` read the ring buffer; elsewhere there are none)."""
    for cmd in (["sudo", "-n", "dmesg"], ["dmesg"]):
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=15, check=False)
        except (OSError, subprocess.TimeoutExpired):
            continue
        if r.returncode == 0:
            return [ln.strip() for ln in r.stdout.splitlines() if OOM.search(ln)]
    return []


def watch(interval: float, limit: int | None) -> None:
    n = 0
    while limit is None or n < limit:
        with LOG.open("a", encoding="utf-8") as f:
            f.write(json.dumps(sample()) + "\n")
        n += 1
        if limit is None or n < limit:
            time.sleep(interval)


def summarize(rows: list[dict], oom: list[str]) -> str:
    """Markdown for the job's page: the extremes, and what was running when the disk was fullest."""
    if not rows:
        return "### Runner telemetry\n\nno samples were taken\n"
    minutes = max(0, (rows[-1]["t"] - rows[0]["t"]) // 60)
    fullest = min(rows, key=lambda r: r["disk_free_gb"])
    out = [
        "### Runner telemetry",
        "",
        f"{len(rows)} samples over {minutes} min",
        "",
        f"- disk: the most used was {max(r['disk_used_gb'] for r in rows)} GB, the least free {fullest['disk_free_gb']} GB (biggest then: {', '.join(fullest.get('top', [])) or 'unknown'})",
    ]
    if any("mem_used_mb" in r for r in rows):
        have = [r for r in rows if "mem_used_mb" in r]
        out.append(
            f"- memory: the most used was {max(r['mem_used_mb'] for r in have)} MB, the least available {min(r['mem_avail_mb'] for r in have)} MB, swap at most {max(r['swap_used_mb'] for r in have)} MB"
        )
    out.append(f"- out-of-memory kills in the kernel log: {len(oom)}")
    out.extend(f"  - `{ln[:200]}`" for ln in oom[:3])
    return "\n".join(out) + "\n"


def read_rows() -> list[dict]:
    rows = []
    try:
        for ln in LOG.read_text(encoding="utf-8").splitlines():
            try:
                rows.append(json.loads(ln))
            except ValueError:
                continue  # a sample cut short by the job ending
    except OSError:
        pass
    return rows


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    w = sub.add_parser("watch")
    w.add_argument("--max", type=int, default=None, help="stop after this many samples")
    sub.add_parser("summary")
    a = ap.parse_args(argv)
    if a.cmd == "watch":
        watch(float(os.environ.get("TELEMETRY_INTERVAL") or 20), a.max)
    else:
        sys.stdout.write(summarize(read_rows(), oom_lines()))


if __name__ == "__main__":
    main()
