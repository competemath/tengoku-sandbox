#!/usr/bin/env python3
"""merge.py --round K --out DIR SHARD_DIR... — the findings of a round's shards, merged into one report (the jinshi workflow's last job).

Each SHARD_DIR is a run.py output directory (modules.txt, <check>.jsonl, timings.json); the merged DIR gets every <check>.jsonl
concatenated, modules.txt in order, and summary.md computed by run.py's summarize over the whole round.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import summarize  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--round", type=int, default=0)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("shards", nargs="+", type=Path)
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    modules: list[str] = []
    results: dict[str, list[dict]] = {}
    timings: dict[str, float] = {}
    for d in a.shards:
        if (d / "modules.txt").is_file():
            modules += (d / "modules.txt").read_text().split()
        for f in sorted(d.glob("*.jsonl")):
            fs = [json.loads(line) for line in f.read_text(encoding="utf-8").splitlines() if line.strip()]
            results.setdefault(f.stem, []).extend(fs)
        t = d / "timings.json"
        if t.is_file():
            for k, v in json.loads(t.read_text()).items():
                timings[k] = timings.get(k, 0) + v
    modules = sorted(set(modules))
    (a.out / "modules.txt").write_text("\n".join(modules) + "\n")
    for check, fs in results.items():
        with (a.out / f"{check}.jsonl").open("w", encoding="utf-8") as fh:
            for f in fs:
                fh.write(json.dumps(f, ensure_ascii=False) + "\n")
    lines = summarize(a.round, modules, results, timings)
    (a.out / "summary.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines[:10]))
    print(f"merged {len(a.shards)} shards: {len(modules)} modules, {sum(len(v) for v in results.values())} findings")
    return 0


if __name__ == "__main__":
    sys.exit(main())
