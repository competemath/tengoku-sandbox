#!/usr/bin/env python3
"""selftest.py — the Jinshi examinations on their fixtures (docs/jinshi.md, "Running").

Compiles tools/jinshi/fixtures/Cases.lean against Lean's own library (no tree, no cache), runs the environment examinations
(tengoku-jinshi, built by `lake build tengoku-jinshi`) and the autoImplicit re-elaboration on it, and compares the findings with
tools/jinshi/fixtures/expected.tsv: every planted fault is found (check, severity, name, and a word of the detail), and nothing
is reported about a declaration the table does not name. Then the replay: tools/jinshi/fixtures/Forged.lean, a proof of False that
skipped the kernel (it compiles, and Lean reports no axioms), must be refused by leanchecker, and by lean4lean when JINSHI_LEAN4LEAN
names its binary; Cases.lean must be accepted by both. Exit 1 on any difference, with the lines that differ.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIX = ROOT / "tools" / "jinshi" / "fixtures"
MODULE = "JinshiFixtures.Cases"

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import autoimplicit_findings, lean4lean_finding, replay_finding  # noqa: E402


def sh(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def main() -> int:
    exe = ROOT / ".lake" / "build" / "bin" / "tengoku-jinshi"
    if not exe.is_file():
        print("build the examinations first: lake build tengoku-jinshi", file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "JinshiFixtures"
        out.mkdir()
        # the fixture, compiled as the module JinshiFixtures.Cases (-o writes the .olean; imports come from LEAN_PATH, Init only)
        r = sh(["lake", "env", "lean", "-o", str(out / "Cases.olean"), "-i", str(out / "Cases.ilean"), str(FIX / "Cases.lean")])
        if r.returncode:
            print(r.stdout + r.stderr)
            return 2
        env = dict(
            os.environ, LEAN_PATH=os.pathsep.join(p for p in [sh(["lake", "env", "printenv", "LEAN_PATH"]).stdout.strip(), tmp] if p)
        )
        r = subprocess.run([str(exe), "--module", MODULE, "--seed", "Init"], cwd=ROOT, capture_output=True, text=True, env=env)
        if r.returncode:
            print(r.stdout + r.stderr)
            return 2
        found = [json.loads(line) for line in r.stdout.splitlines() if line.strip()]
        found = [f for f in found if f["check"] != "summary"]
        # the autoImplicit re-elaboration, through the same code the round driver uses
        found += autoimplicit_findings(FIX / "Cases.lean", MODULE, lake=True)
        # the replay: the forged module is refused, the honest one accepted, by every kernel at hand
        r = sh(["lake", "env", "lean", "-o", str(out / "Forged.olean"), str(FIX / "Forged.lean")])
        if r.returncode:
            print(r.stdout + r.stderr)
            return 2
        os.environ["LEAN_PATH"] = env["LEAN_PATH"]
        replay = {}
        for name, fn in (("replay", replay_finding), ("lean4lean", lean4lean_finding)):
            if name == "lean4lean" and not os.environ.get("JINSHI_LEAN4LEAN"):
                print("lean4lean: JINSHI_LEAN4LEAN is not set, its replay is not tested here")
                continue
            replay[name] = {"forged": fn("JinshiFixtures.Forged"), "honest": fn(MODULE)}

    expected = []
    for line in (FIX / "expected.tsv").read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        check, sev, name, word = line.split("\t")
        expected.append((check, sev, name, word))
    problems = []
    for check, sev, name, word in expected:
        hits = [f for f in found if f["check"] == check and f["name"] == name]
        if not any(f["severity"] == sev and word in f["detail"] for f in hits):
            problems.append(
                f"MISSING  {check}/{sev} {name} (detail containing {word!r}); got: {[(f['severity'], f['detail'][:80]) for f in hits]}"
            )
    named = {name for _, _, name, _ in expected}
    for f in found:
        if f["name"] not in named:
            problems.append(f"UNEXPECTED {f['check']}/{f['severity']} {f['name']}: {f['detail'][:120]}")
        elif not any(f["check"] == c and f["severity"] == s and w in f["detail"] for c, s, n, w in expected if n == f["name"]):
            problems.append(f"EXTRA    {f['check']}/{f['severity']} {f['name']}: {f['detail'][:120]}")
    for name, got in replay.items():
        if not any(f["severity"] == "fail" for f in got["forged"]):
            problems.append(f"MISSING  {name}/fail JinshiFixtures.Forged: the forged proof of False was NOT refused; got {got['forged']}")
        if got["honest"]:
            problems.append(f"EXTRA    {name} on {MODULE}: {got['honest']}")
        print(
            f"{name}: the forged module {'refused' if got['forged'] else 'ACCEPTED'}, the honest module {'accepted' if not got['honest'] else 'REFUSED'}"
        )
    for p in problems:
        print(p)
    print(f"jinshi selftest: {len(found)} findings, {len(expected)} expected, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
