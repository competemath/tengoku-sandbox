#!/usr/bin/env python3
"""lake_cache.py — the pure half of the queue's use of Lake's own artifact cache (`lake build -o`, `lake cache stage`, `lake cache unstage`).

Lake keys every build output by a hash of all its inputs, so a seeded or restored output is used only when the sources on disk hash to it: a wrong
label can cost a rebuild, never a wrong artifact. What Lake does not do is move a group's outputs between runners through a store that is free:
a GitHub release holds at most 1000 assets of under 2 GiB each, and a group has hundreds of outputs, so the outputs of ONE group travel as ONE
asset, `d-<commit>.tar.zst`: the staging directory of `lake cache stage`, packed. The helpers here decide three things, with no network and no Lean:

  plan   --revs <file> --assets <file>              the delta assets to apply, oldest first: the merges between the nightly base and this group
                                                     (`git rev-list --reverse <base>..<head>`) that published one. A merge with no delta
                                                     (nothing new, or its upload never happened) is skipped: Lake compiles what it cannot restore.
  diff   --out <file> --had <file>... --to <file>   this group's OWN new mappings: the lines of its `lake build -o` file that no earlier file
                                                     (the base's, the deltas') has. Line 1 is the file's header (a schema date) and stays line 1:
                                                     `lake cache stage` refuses a mappings file without it.
  check  --targets <file> --log <file> [--fail]     the modules the group's build COMPILED that are not its targets: restores that missed.

Prints one JSON object (or, for plan, one asset per line).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

DELTA = re.compile(r"^d-([0-9a-f]{40})\.tar\.zst$")
BUILT = re.compile(r"\bBuilt\s+(\S+)")


def read_lines(path: str) -> list[str]:
    return [ln.strip() for ln in Path(path).read_text(encoding="utf-8").splitlines() if ln.strip()]


def plan(revs: list[str], assets: list[str]) -> list[str]:
    """The `d-<rev>.tar.zst` assets for the revisions in `revs` (oldest first) that exist; nothing else in the release is named by a revision."""
    have = {m.group(1): a for a in assets if (m := DELTA.match(a))}
    return [have[r] for r in revs if r in have]


def diff(out: list[str], had: set[str]) -> list[str]:
    """The header and the mappings of `out` that `had` does not contain, in order, without repeats. `out` is a mappings file's lines, header first."""
    if not out:
        raise ValueError("an empty mappings file has no header")
    header, body = out[0], out[1:]
    seen: set[str] = set()
    new = []
    for ln in body:
        if ln not in had and ln not in seen:
            seen.add(ln)
            new.append(ln)
    return [header, *new]


def compiled(log: str) -> set[str]:
    """Modules a Lake build log says it built (a module that was only replayed or restored is not built)."""
    return {m.group(1) for m in BUILT.finditer(log)}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--revs", required=True)
    p.add_argument("--assets", required=True)
    d = sub.add_parser("diff")
    d.add_argument("--out", required=True)
    d.add_argument("--had", nargs="+", required=True)
    d.add_argument("--to", required=True)
    c = sub.add_parser("check")
    c.add_argument("--targets", required=True)
    c.add_argument("--log", required=True)
    c.add_argument("--fail", action="store_true")
    a = ap.parse_args(argv)

    if a.cmd == "plan":
        for name in plan(read_lines(a.revs), read_lines(a.assets)):
            print(name)
        return 0
    if a.cmd == "diff":
        had: set[str] = set()
        for f in a.had:
            had.update(read_lines(f))
        out = read_lines(a.out)
        rows = diff(out, had)
        Path(a.to).write_text("".join(ln + "\n" for ln in rows), encoding="utf-8")
        print(json.dumps({"build": len(out) - 1, "known": len(out) - len(rows), "new": len(rows) - 1}))
        return 0
    targets = set(read_lines(a.targets))
    built = compiled(Path(a.log).read_text(encoding="utf-8", errors="replace"))
    missed = sorted(built - targets)
    print(json.dumps({"targets": len(targets), "compiled": len(built), "misses": len(missed), "first": missed[:5]}))
    return 1 if (a.fail and missed) else 0


if __name__ == "__main__":
    sys.exit(main())
