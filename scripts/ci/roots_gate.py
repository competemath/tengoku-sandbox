#!/usr/bin/env python3
"""roots_gate.py < LEAKSCAN.TXT — a group that puts a declaration into the root namespace does not merge, once the tree has none.

`tengoku-leakscan` (TengokuLeak.lean) lists a `root: NAME` line for every declaration of the scanned modules that sits in the root namespace (one-component name). Such a name is tied
to no library: after `open Polynomial` a bare `X` or `C` has two readings (`_root_.X` of a library and `Polynomial.X`), and a second library declaring the same root name fails to import
(2026-11-12: formal-forbidden-matrix `X`, `C`; compfiles `Usa1980P3` compiles in its own library and fails in the combined `Tengoku.All`; 62 libraries declare 7,300 root names).
The factory qualifies them itself (emissary-archangel `scope_rewrite.py --qualify-roots`, merged 2026-11-12: `Tengoku.<Library>.<name>`), so a bundle arrives without any; this gate holds the
merge queue to it for every later group, whatever produced it.

TENGOKU_ROOTS_REQUIRED is the repository variable: `1` fails a group that has a `root:` line, anything else only reports them (the libraries merged before the factory qualified roots keep
theirs until the tree's own fix of them has merged: the variable is turned on after that).

An auto-generated instance name (a global instance of the shape `instFooBar`, which the scanner reports as `root-instance:`) is listed, not refused (auto_named): nobody writes it and no text declares it. Exit status: 0 nothing to report or not required; 1 required and at least one root name that is not one. The report goes to stdout (and the step summary).
"""

from __future__ import annotations

import os
import re
import sys

INSTANCE_PREFIX = "root-instance: "  # the scanner says which root names are global instances (TengokuLeak.lean)
ROOT_PREFIX = "root: "  # a name Lean prints with guillemets (`«foo bar»`) has a space in it: everything after the prefix is the name
SUMMARY = re.compile(r"^roots: (\d+) declarations")  # the scanner's own count, printed first: a report without it is not a report


def root_lines(report: str) -> list[str]:
    """the names of the `root: NAME` lines of a leakscan report, in order (a name twice is two lines)"""
    names = (ln[len(ROOT_PREFIX) :].strip() for ln in report.splitlines() if ln.startswith(ROOT_PREFIX))
    return [n for n in names if n]


def instance_lines(report: str) -> set[str]:
    """the names the scanner reports as global instances among the roots (`root-instance: NAME`)"""
    return {ln[len(INSTANCE_PREFIX) :].strip() for ln in report.splitlines() if ln.startswith(INSTANCE_PREFIX)}


def roots_of(report: str) -> list[str]:
    """the same, each name once"""
    return list(dict.fromkeys(root_lines(report)))


def auto_named(name: str, instances: set[str]) -> bool:
    """A name Lean generated for an anonymous instance: it is a global instance (the scanner says so) and has the shape Lean gives (`inst` and a capital: `instFooBar`). Nobody writes such a
    name and the roots class cannot rename it (no text declares it), so it is listed and not refused; a name of that shape on something that is no instance, or a name that is not of that
    shape on an instance (`inst_x`, `instance`, `instantiate`), is an ordinary root."""
    return name in instances and len(name) > 4 and name.startswith("inst") and name[4].isupper()


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
    names = roots_of(report)
    instances = instance_lines(report)
    auto = [n for n in names if auto_named(n, instances)]
    roots = [n for n in names if not auto_named(n, instances)]
    exempt = (
        f" ({len(auto)} auto-generated instance name(s) are exempt: {', '.join(auto[:5])}{' …' if len(auto) > 5 else ''})" if auto else ""
    )
    if not roots:
        return 0, "roots: none of the group's declarations is in the root namespace" + exempt
    head = (
        f"roots: {len(roots)} declaration(s) of the group are in the root namespace: "
        + ", ".join(roots[:shown])
        + (" …" if len(roots) > shown else "")
        + exempt
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
