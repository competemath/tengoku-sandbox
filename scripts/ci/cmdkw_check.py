#!/usr/bin/env python3
"""cmdkw_check.py [--emit] — the command keywords Lean reports (tools/CommandKeywords.lean, on stdin, one per line) against schemas/command-keywords.json.

The content lint (scripts/ci/allowlist.py) reads a word at column 0 as a command only if it is on that list, so a keyword the seed added since the list was made
would be read as a continuation. This says which words are new and which are gone, and exits 1 when they differ: regenerate the list (the command is in the message).
It never writes a file: `--emit` prints the regenerated list on stdout for the caller to put in place (Sonar S2083 flagged the write: the list was read from a file and
written back, and the analyzer takes `json.loads` of a file for an untrusted source).
"""

from __future__ import annotations

import json
import sys

from _git import ROOT

LIST = ROOT / "schemas" / "command-keywords.json"  # the repository's own list: never a path from the command line
REGENERATE = 'kw=$(mktemp schemas/.kw.XXXXXX) && lake env lean --run tools/CommandKeywords.lean | python3 scripts/ci/cmdkw_check.py --emit > "$kw" && mv "$kw" schemas/command-keywords.json'


def compare(reported: set[str], listed: set[str]) -> tuple[list[str], list[str]]:
    """(new: Lean has it, the list does not; gone: the list has it, Lean no longer does)."""
    return sorted(reported - listed), sorted(listed - reported)


def main(argv: list[str]) -> int:
    emit = "--emit" in argv
    if [a for a in argv if a != "--emit"]:
        print("cmdkw_check.py reads schemas/command-keywords.json and takes no path (the only option is --emit)")
        return 2
    reported = {ln.strip() for ln in sys.stdin.read().splitlines() if ln.strip()}
    if len(reported) < 100:
        print(
            f"Lean reported {len(reported)} command keywords: that is not the tree's command grammar (the program failed, or nothing was loaded)"
        )
        return 2
    doc = json.loads(LIST.read_text(encoding="utf-8"))
    new, gone = compare(reported, set(doc["commands"]))
    if emit:
        print(json.dumps({**doc, "commands": sorted(reported)}, ensure_ascii=False, indent=1))
        return 0
    if new or gone:
        print(
            f"::error::the tree's command keywords changed since {LIST.name} was made: new {new}, gone {gone}. A keyword that is missing from the list is read as a continuation "
            f"by the lint, so the list must be current. Regenerate: {REGENERATE}"
        )
        return 1
    print(f"command keywords: the tree's {len(reported)} are the ones the lint reads")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
