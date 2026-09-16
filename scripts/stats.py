#!/usr/bin/env python3
"""Write data/stats.json: what the tree holds, per library and tier.

    scripts/stats.py [--out data/stats.json]

The site's stat pills read this file straight from GitHub (raw, ISR-cached),
so no database is involved in showing what Tengoku contains. Run by the
promote loop before every commit and by the nightly build.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

TIERS = ("trusted", "staging", "tentative")
PROMOTED_RE = re.compile(rb'"promoted_at"\s*:\s*"([^"]+)"')


def count_lines(path: Path) -> int:
    n = 0
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            n += chunk.count(b"\n")
    return n


def last_promoted(path: Path) -> str | None:
    best = None
    with path.open("rb") as f:
        for line in f:
            m = PROMOTED_RE.search(line)
            if m:
                v = m.group(1).decode()
                if best is None or v > best:
                    best = v
    return best


def collect(root: Path) -> dict:
    libraries: dict[str, dict] = {}
    for tier in TIERS:
        for p in sorted((root / "data" / tier).glob("*.jsonl")):
            lib = libraries.setdefault(p.stem, {t: 0 for t in TIERS})
            lib[tier] = count_lines(p)
            if tier == "trusted":
                lp = last_promoted(p)
                if lp:
                    lib["last_promoted_at"] = lp
    totals = {t: sum(l[t] for l in libraries.values()) for t in TIERS}
    totals["all"] = sum(totals.values())
    return {"totals": totals, "libraries": libraries, "library_count": len(libraries)}


def git(root: Path, *args: str) -> str:
    try:
        return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, timeout=30).stdout.strip()
    except Exception:
        return ""


def build(root: Path) -> dict:
    s = collect(root)
    s.update(
        {
            "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "tree_commit": git(root, "rev-parse", "HEAD"),
            "toolchain": (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else "",
            "last_promoted_at": max((l.get("last_promoted_at", "") for l in s["libraries"].values()), default="") or None,
        }
    )
    return s


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    root = Path(a.root)
    stats = build(root)
    out = Path(a.out) if a.out else root / "data" / "stats.json"
    out.write_text(json.dumps(stats, indent=2, sort_keys=True) + "\n")
    t = stats["totals"]
    print(
        f"{out}: {t['all']} records ({t['trusted']} trusted, {t['staging']} staging, {t['tentative']} tentative) in {stats['library_count']} libraries"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
# touched
