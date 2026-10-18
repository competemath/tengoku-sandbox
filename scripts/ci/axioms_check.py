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

Splitting alone degenerates when many modules clash (a staging group of 659 records: 227 candidates, dozens of runs,
still unfinished after an hour), so the modules are first sorted into groups that cannot clash: a module's closure is
the names it declares plus those of the library modules it imports (transitively); two modules clash when a name is
declared by different modules in their closures. Each group is then one run, and the split remains only as the
safety net for a clash this reading misses.
"""

from __future__ import annotations

import os
import re
import shlex
import signal
import subprocess
import sys
import threading
from pathlib import Path

CLASH = "environment already contains"
TOOL = shlex.split(os.environ.get("AXIOMS_TOOL", "lake env .lake/build/bin/tengoku-axioms"))
JOBS = max(1, int(os.environ.get("AXIOMS_JOBS", "3")))
RUN_TIMEOUT = int(
    os.environ.get("AXIOMS_RUN_TIMEOUT", "1200")
)  # one run takes about a minute; a stuck one must not hold the queue  # each run holds the tree in memory; the runner has 16 GB

IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(\S+)", re.M)
ROOT = Path(os.environ.get("TENGOKU_CI_ROOT", "."))

slots = threading.Semaphore(JOBS)
lock = threading.Lock()
runs = 0


def run(mods: list[str]) -> tuple[int, str]:
    global runs
    with slots:
        # its own process group: `lake env` starts the checker as a child, and a timeout must stop both (killing only
        # lake leaves the checker running, holding the pipes and the runner's memory)
        p = subprocess.Popen(
            TOOL + [a for m in mods for a in ("--module", m)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        try:
            out, _ = p.communicate(timeout=RUN_TIMEOUT)
            rc = p.returncode
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            out, _ = p.communicate()
            rc, out = 124, f"{out or ''}error: the axiom check of {len(mods)} module(s) did not finish in {RUN_TIMEOUT} s\n"
        finally:
            with lock:
                runs += 1
    return rc, out or ""


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


def module_text(mod: str) -> str | None:
    f = ROOT / Path(*mod.split(".")).with_suffix(".lean")
    return f.read_text(encoding="utf-8", errors="ignore") if f.is_file() else None


def plan_groups(mods: list[str]) -> list[list[str]]:
    """The modules sorted into as few groups as the reading allows, no two clashing modules in one group."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from _git import declared_names

    names_of: dict[str, set[str]] = {}
    imports_of: dict[str, list[str]] = {}

    def load(mod: str) -> None:
        if mod in names_of:
            return
        text = module_text(mod)
        names_of[mod] = declared_names(text) if text else set()
        imports_of[mod] = IMPORT_RE.findall(text) if text else []

    def closure(mod: str) -> dict[str, str]:
        """name -> the module that declares it, over the module and the library modules it imports."""
        lib = ".".join(mod.split(".")[:2])  # Tengoku.<Library>: the seed and the trusted tree are shared by every run
        out: dict[str, str] = {}
        todo, seen = [mod], set()
        while todo:
            m = todo.pop()
            if m in seen:
                continue
            seen.add(m)
            load(m)
            for n in names_of[m]:
                out.setdefault(n, m)
            todo += [i for i in imports_of[m] if i.startswith(lib + ".")]
        return out

    closures = {m: closure(m) for m in mods}
    clash = {m: set() for m in mods}
    owners: dict[str, dict[str, set[str]]] = {}  # name -> declaring module -> targets whose closure has it from there
    for m, c in closures.items():
        for n, where in c.items():
            owners.setdefault(n, {}).setdefault(where, set()).add(m)
    for by_module in owners.values():
        if len(by_module) > 1:
            sets = list(by_module.values())
            for i, a in enumerate(sets):
                for b in sets[i + 1 :]:
                    for x in a:
                        clash[x] |= b
                    for y in b:
                        clash[y] |= a
    groups: list[list[str]] = []
    for m in sorted(mods, key=lambda m: -len(clash[m])):  # the most constrained first; otherwise the order given
        for g in groups:
            if not any(o in clash[m] for o in g):
                g.append(m)
                break
        else:
            groups.append([m])
    return groups


def main(argv: list[str]) -> int:
    mods = [m for m in argv if m]
    if not mods:
        print("usage: axioms_check.py MODULE...", file=sys.stderr)
        return 2
    groups = plan_groups(mods)
    results: list[bool] = []
    threads = [threading.Thread(target=lambda g=g: results.append(check(g))) for g in groups]
    for th in threads:
        th.start()
    for th in threads:
        th.join()
    print(f"axiom check: {len(mods)} modules in {len(groups)} group(s), {runs} run(s)")
    return 0 if len(results) == len(groups) and all(results) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
