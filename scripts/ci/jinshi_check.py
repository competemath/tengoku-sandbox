#!/usr/bin/env python3
"""jinshi_check.py <base> <head> — Jinshi's advisory, low-memory per-PR check (docs/jinshi.md): examines exactly the
Tengoku modules this PR adds or changes, the same candidate modules the merge queue itself would build
(scripts/ci/queue_targets.py), one tengoku-jinshi process per module so nothing from an earlier module's own
Mathlib dependency closure stays resident while the next one loads. Memory stays bounded by whichever single
changed file's own import closure is largest, never by the size of the tree.

Compiling these candidates runs the PR's own Lean, quite possibly for the first time ever: this script is meant to
run only inside the same sealed sandbox (no network, no token reachable) pr-gate.yml's `vacuity` job already uses
for exactly that reason — see .github/workflows/jinshi-pr.yml, which wraps it in `unshare --net --pid`.

Excluded from the default check set: `mutants` (writes its own oleans and shells out to leanchecker/lean4lean/
nanoda per mutant — that cost belongs to a maintainer's dispatched round, not a routine PR) and `entailed` (its
library-search index is built once per PROCESS over the whole imported corpus; rebuilding it per changed file
here would cost real time for no added signal a round wouldn't already give better). Both stay available there,
unaffected by this script. `JINSHI_PR_CHECKS` overrides the default comma-separated list.

Exit code: 1 only on a fail-severity finding, the only severity Jinshi itself calls soundness-sensitive; warn/info
are printed but never fail the job — the same severity contract every other Jinshi examination already has.
`JINSHI_PR_TARGETS=<file>` (one module per line) replaces the queue_targets.py call, for tests."""

from __future__ import annotations

import json
import os
import subprocess
import sys

from _git import ROOT, fail

EXE = ROOT / ".lake" / "build" / "bin" / "tengoku-jinshi"
# Exactly the examinations main's TengokuJinshi.lean registers today: `arithUniverse`, `importance`, `lineage`,
# `necessity` and `nested` are still only on jinshi/wave2-main (not yet merged) and would make the executable
# reject this list outright ("unknown examination") — add each here the same day it lands on main.
DEFAULT_CHECKS = (
    "tcb,shadow,nearname,arith,dossier,content,decide,duplicate,"
    "instdrift,unusedhyp,roundtrip,forensics"
)
CHECKS = os.environ.get("JINSHI_PR_CHECKS", DEFAULT_CHECKS)


def candidate_targets(base: str, head: str) -> list[str]:
    targets_file = os.environ.get("JINSHI_PR_TARGETS")
    if targets_file:
        return [ln.strip() for ln in open(targets_file, encoding="utf-8") if ln.strip()]
    r = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "ci" / "queue_targets.py"), base, head],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        fail(f"could not determine the PR's candidate modules:\n{r.stderr[-1500:]}")
    return [line.strip() for line in r.stdout.splitlines() if line.strip() and line.startswith("Tengoku.")]


def build(targets: list[str]) -> bool:
    r = subprocess.run(["lake", "build", *targets], cwd=ROOT, capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        # A candidate that does not build cannot be examined; the merge queue already reports why a build fails.
        print("jinshi: the candidate modules did not build, so nothing was examined (the merge queue reports build errors):")
        print((r.stdout + r.stderr)[-1200:])
        return False
    return True


def examine(module: str) -> list[dict]:
    """one process, one module: whatever it imports is all that is ever resident at once."""
    try:
        r = subprocess.run(
            ["lake", "env", str(EXE), "--module", module, "--check", CHECKS],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=900,
        )
    except subprocess.TimeoutExpired:
        return [
            {
                "check": "jinshi",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": "tengoku-jinshi exceeded 900s on this module alone",
            }
        ]
    if r.returncode != 0:
        return [
            {
                "check": "jinshi",
                "severity": "warn",
                "module": module,
                "name": "",
                "line": None,
                "detail": f"tengoku-jinshi failed on this module alone (exit {r.returncode}): {(r.stderr or r.stdout)[-600:]}",
            }
        ]
    return [f for f in (json.loads(ln) for ln in r.stdout.splitlines() if ln.strip()) if f.get("check") != "summary"]


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: jinshi_check.py <base> <head>", file=sys.stderr)
        return 2
    base, head = argv
    targets = candidate_targets(base, head)
    if not targets:
        print("jinshi OK: this PR adds or changes no Tengoku module")
        return 0

    if not build(targets):
        return 0

    print(f"jinshi: {len(targets)} candidate module(s), checks: {CHECKS}")
    findings: list[dict] = []
    for m in targets:
        findings += examine(m)

    fails = [f for f in findings if f["severity"] == "fail"]
    warns = [f for f in findings if f["severity"] == "warn"]
    infos = [f for f in findings if f["severity"] == "info"]
    print(f"\n{len(findings)} finding(s): {len(fails)} fail, {len(warns)} warn, {len(infos)} info\n")
    for f in fails + warns:
        print(f"[{f['severity']}] {f['check']} {f['module']} {f['name']}: {f['detail'][:300]}")

    if fails:
        fail(f"jinshi: {len(fails)} fail-severity finding(s) on this PR's own changes (see above)")
    print("jinshi OK: no fail-severity finding on this PR's own changes")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
