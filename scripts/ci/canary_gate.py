#!/usr/bin/env python3
"""canary_gate.py DIR — the compiled-tier content lint as a yes/no on a directory of .lean files, for the wounder's canaries.

Exit 0: every file passes the allow-list that a staging or trusted record must pass (scripts/ci/allowlist.py, the same
function lint_banked.py applies to the lines a PR adds). Exit 1: a file does not; the reasons are printed. Exit 2: the
directory is unreadable. `import` lines are dropped first, as lint_banked.py does for modules (the generator supplies
imports; a record may not contain one). This is only the static layer: whether the gate that compiles and checks axioms
agrees is another layer (tengoku-wounder `--layer`). Standard library only; reads files, runs nothing."""

from __future__ import annotations

import re
import sys
from pathlib import Path

from _git import load_schema
from allowlist import violations

IMPORT_START = re.compile(r"^\s*import\b")


def check(directory: Path) -> list[str]:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    keywords = set(load_schema("command-keywords.json")["commands"])
    out: list[str] = []
    files = sorted(directory.glob("*.lean"))
    if not files:
        return ["no .lean files to check"]
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        body = "\n".join(ln for ln in text.split("\n") if not IMPORT_START.match(ln))
        out += [f"{path.name}: {v}" for v in violations(body, allowed, keywords)]
    return out


def main(argv: list[str]) -> int:
    if len(argv) != 2 or not Path(argv[1]).is_dir():
        print("usage: canary_gate.py DIR", file=sys.stderr)
        return 2
    problems = check(Path(argv[1]))
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
