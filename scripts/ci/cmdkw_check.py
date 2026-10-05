#!/usr/bin/env python3
"""cmdkw_check.py [LIST.json] — the command keywords Lean reports (tools/CommandKeywords.lean, on stdin, one per line) against schemas/command-keywords.json.

The content lint (scripts/ci/allowlist.py) reads a word at column 0 as a command only if it is on that list, so a keyword the seed added since the list was made
would be read as a continuation. This says which words are new and which are gone, and exits 1 when they differ: regenerate the list (the command is in the message).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from _git import ROOT

REGENERATE = "lake env lean --run tools/CommandKeywords.lean | python3 scripts/ci/cmdkw_check.py --write"


def compare(reported: set[str], listed: set[str]) -> tuple[list[str], list[str]]:
    """(new: Lean has it, the list does not; gone: the list has it, Lean no longer does)."""
    return sorted(reported - listed), sorted(listed - reported)


def main(argv: list[str]) -> int:
    write = "--write" in argv
    paths = [a for a in argv if not a.startswith("--")]
    path = Path(paths[0]) if paths else ROOT / "schemas" / "command-keywords.json"
    reported = {ln.strip() for ln in sys.stdin.read().splitlines() if ln.strip()}
    if len(reported) < 100:
        print(
            f"Lean reported {len(reported)} command keywords: that is not the tree's command grammar (the program failed, or nothing was loaded)"
        )
        return 2
    doc = json.loads(path.read_text(encoding="utf-8"))
    new, gone = compare(reported, set(doc["commands"]))
    if write:
        doc["commands"] = sorted(reported)
        path.write_text(json.dumps(doc, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        print(f"{path}: {len(reported)} command keywords written (new: {new}, gone: {gone})")
        return 0
    if new or gone:
        print(
            f"::error::the tree's command keywords changed since {path.name} was made: new {new}, gone {gone}. A keyword that is missing from the list is read as a continuation "
            f"by the lint, so the list must be current. Regenerate: {REGENERATE}"
        )
        return 1
    print(f"command keywords: the tree's {len(reported)} are the ones the lint reads")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
