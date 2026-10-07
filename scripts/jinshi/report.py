#!/usr/bin/env python3
"""report.py DIR [--check C] [--library L] [--severity S] [--top N] — read a round's findings (a run.py or merge.py output directory).

Prints: findings per library and check (fail/warn/info), the modules with the most fail+warn, and, with --check or --library, the
findings themselves (severity, module, name, detail), most severe first. A library is the second component of the module name
(`Tengoku.Seed.Algebra…` is `Seed/Algebra`, `Tengoku.Compfiles.…` is `Compfiles`).
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path

SEV = {"fail": 0, "warn": 1, "info": 2}


def library(module: str) -> str:
    parts = module.split(".")
    if len(parts) < 2:
        return module or "(none)"
    if parts[1] == "Seed":
        return "Seed/" + (parts[2] if len(parts) > 2 else "")
    return parts[1]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("dir", type=Path)
    ap.add_argument("--check")
    ap.add_argument("--library")
    ap.add_argument("--severity", choices=list(SEV))
    ap.add_argument("--top", type=int, default=15)
    a = ap.parse_args()
    findings = []
    for f in sorted(a.dir.glob("*.jsonl")):
        for line in f.read_text(encoding="utf-8").splitlines():
            if line.strip():
                d = json.loads(line)
                if d.get("check") != "summary":
                    findings.append(d)
    modules = (a.dir / "modules.txt").read_text().split() if (a.dir / "modules.txt").is_file() else []
    print(f"{len(findings)} findings over {len(modules)} modules\n")
    table: dict[tuple[str, str], Counter] = defaultdict(Counter)
    for d in findings:
        table[(library(d["module"]), d["check"])][d["severity"]] += 1
    checks = sorted({c for _, c in table})
    libs = sorted({lib for lib, _ in table})
    print("| library | " + " | ".join(checks) + " |")
    print("|---|" + "---|" * len(checks))
    for lib in libs:
        cells = []
        for c in checks:
            n = table.get((lib, c), Counter())
            cells.append(f"{n['fail']}/{n['warn']}/{n['info']}" if n else "")
        print(f"| {lib} | " + " | ".join(cells) + " |")
    print("\n(cells: fail/warn/info)\n")
    per_module = Counter(d["module"] for d in findings if d["severity"] in ("fail", "warn"))
    print(f"modules with the most fail+warn (top {a.top}):")
    for m, n in per_module.most_common(a.top):
        print(f"  {n:4d}  {m}")
    if a.check or a.library or a.severity:
        sel = [
            d
            for d in findings
            if (not a.check or d["check"] == a.check)
            and (not a.library or library(d["module"]) == a.library)
            and (not a.severity or d["severity"] == a.severity)
        ]
        sel.sort(key=lambda d: (SEV[d["severity"]], d["module"], d["name"]))
        print(f"\n{len(sel)} findings selected:")
        for d in sel[: a.top * 10]:
            print(f"  [{d['severity']}] {d['check']} {d['module']} {d['name']} :: {d['detail'][:220]}")
    return 0


if __name__ == "__main__":
    exit(main())
