#!/usr/bin/env python3
"""axioms_check.py — the merge queue's axiom check over a group's candidate modules.

  axioms_check.py MODULE...      from the repository root, after `lake build tengoku-axioms`

Each run of tengoku-axioms imports the whole tree (about a minute), so the modules go in as few runs as possible:
first all of them in one. Candidates are generated one file at a time, so two can declare the same thing (a file's
module and the Deps module another file's records carry) and cannot be imported together. A run that fails that
way is split in half and each half is checked, up to AXIOMS_JOBS runs at a time, until every part imports: a few
clashes cost a few extra runs, not one run per module (which took 45 minutes on a staging group and made the queue
time out). A module that cannot be imported even alone, or a declaration with a non-standard axiom, fails the check.
Every run's output is printed (the workflow appends it to build.log, which the ejection comment reads).
"""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
import threading

CLASH = "environment already contains"
TOOL = shlex.split(os.environ.get("AXIOMS_TOOL", "lake env .lake/build/bin/tengoku-axioms"))
JOBS = max(1, int(os.environ.get("AXIOMS_JOBS", "3")))
RUN_TIMEOUT = int(
    os.environ.get("AXIOMS_RUN_TIMEOUT", "1200")
)  # one run takes about a minute; a stuck one must not hold the queue  # each run holds the tree in memory; the runner has 16 GB

slots = threading.Semaphore(JOBS)
lock = threading.Lock()
runs = 0


def run(mods: list[str]) -> tuple[int, str]:
    global runs
    with slots:
        try:
            p = subprocess.run(TOOL + [a for m in mods for a in ("--module", m)], capture_output=True, text=True, timeout=RUN_TIMEOUT)
        except subprocess.TimeoutExpired as e:
            out = (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            return 124, f"{out}error: the axiom check of {len(mods)} module(s) did not finish in {RUN_TIMEOUT} s\n"
        finally:
            with lock:
                runs += 1
    return p.returncode, p.stdout + p.stderr


def check(mods: list[str]) -> bool:
    rc, out = run(mods)
    if rc != 0 and CLASH in out and len(mods) > 1:
        half = len(mods) // 2
        first: list[bool] = []
        t = threading.Thread(target=lambda: first.append(check(mods[:half])))
        t.start()
        second = check(mods[half:])
        t.join()
        return bool(first) and first[0] and second
    with lock:
        print(f"-- {len(mods)} module(s): {' '.join(mods[:3])}{' …' if len(mods) > 3 else ''}")
        print(out, end="" if out.endswith("\n") or not out else "\n")
    return rc == 0


def main(argv: list[str]) -> int:
    mods = [m for m in argv if m]
    if not mods:
        print("usage: axioms_check.py MODULE...", file=sys.stderr)
        return 2
    ok = check(mods)
    print(f"axiom check: {len(mods)} modules in {runs} run(s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
