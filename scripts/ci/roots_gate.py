#!/usr/bin/env python3
"""roots_gate.py < LEAKSCAN.TXT — a group that puts a declaration into the root namespace does not merge, once the tree has none.

`tengoku-leakscan` (TengokuLeak.lean) lists a `root: NAME` line for every declaration of the scanned modules that sits in the root namespace (one-component name). Such a name is tied
to no library: after `open Polynomial` a bare `X` or `C` has two readings (`_root_.X` of a library and `Polynomial.X`), and a second library declaring the same root name fails to import
(2026-11-12: formal-forbidden-matrix `X`, `C`; compfiles `Usa1980P3` compiles in its own library and fails in the combined `Tengoku.All`; 62 libraries declare 7,300 root names).
The factory qualifies them itself (emissary-archangel `scope_rewrite.py --qualify-roots`, merged 2026-11-12: `Tengoku.<Library>.<name>`), so a bundle arrives without any; this gate holds the
merge queue to it for every later group, whatever produced it.

TENGOKU_ROOTS_REQUIRED is the repository variable: `1` fails a group that has a `root:` line, anything else only reports them (the libraries merged before the factory qualified roots keep
theirs until the tree's own fix of them has merged: the variable is turned on after that).

Exit status: 0 nothing to report or not required; 1 required and at least one root name. The report goes to stdout (and the step summary).
"""

from __future__ import annotations

import os
import re
import sys

ROOT_LINE = re.compile(r"^root: (.+?)\s*$")  # a name Lean prints with guillemets (`«foo bar»`) has a space in it
SUMMARY = re.compile(r"^roots: (\d+) declarations")  # the scanner's own count, printed first: a report without it is not a report


def root_lines(report: str) -> list[str]:
    """the names of the `root: NAME` lines of a leakscan report, in order (a name twice is two lines)"""
    return [m.group(1) for ln in report.splitlines() if (m := ROOT_LINE.match(ln))]


def roots_of(report: str) -> list[str]:
    """the same, each name once"""
    return list(dict.fromkeys(root_lines(report)))


def judge(report: str, required: bool, shown: int = 20) -> tuple[int, str]:
    """(exit status, message). A report that is not the scanner's whole report (no summary line: it crashed; fewer `root:` lines than the summary says: it was cut)
    cannot show that a group has no root, so it fails a required gate: the gate does not open when the scanner does not run."""
    summary = next((int(m.group(1)) for ln in report.splitlines() if (m := SUMMARY.match(ln))), None)
    lines = root_lines(report)
    if summary is None or summary != len(lines):
        why = (
            "the leak report has no `roots:` summary line (the scanner did not finish)"
            if summary is None
            else f"the leak report counts {summary} root declaration(s) and lists {len(lines)}"
        )
        return (1 if required else 0), f"roots: not checked: {why}" + (
            "\nerror: roots are required and the group cannot be shown to have none" if required else " (TENGOKU_ROOTS_REQUIRED is not 1)"
        )
    roots = roots_of(report)
    if not roots:
        return 0, "roots: none of the group's declarations is in the root namespace"
    head = (
        f"roots: {len(roots)} declaration(s) of the group are in the root namespace: "
        + ", ".join(roots[:shown])
        + (" …" if len(roots) > shown else "")
    )
    if not required:
        return 0, head + " (reported only: TENGOKU_ROOTS_REQUIRED is not 1)"
    return 1, (
        head
        + "\nerror: a declaration in the root namespace is a name nothing ties to its library: after `open Polynomial` a bare `C` is `_root_.C` or `Polynomial.C`, and a second library with the same name "
        "does not import. Qualify it with the library's namespace (`Tengoku.<Library>.<name>`): the factory's `scope_rewrite.py --qualify-roots` does it for a bundle."
    )


def main() -> int:
    """the leak report on stdin (`roots_gate.py < leakscan.txt`: no path to read, nothing to traverse)"""
    code, msg = judge(sys.stdin.read(), os.environ.get("TENGOKU_ROOTS_REQUIRED") == "1")
    print(msg)
    return code


if __name__ == "__main__":
    sys.exit(main())
