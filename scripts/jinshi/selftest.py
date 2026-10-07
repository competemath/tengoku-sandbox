#!/usr/bin/env python3
"""selftest.py — the Jinshi examinations on their fixtures (docs/jinshi.md, "Running").

Every tools/jinshi/fixtures/<Name>.lean that has a <Name>.expected.tsv beside it is compiled against Lean's own library (no tree,
no cache) as the module JinshiFixtures.<Name>, the environment examinations (tengoku-jinshi, built by `lake build tengoku-jinshi`)
and the autoImplicit re-elaboration run on it, and the findings are compared with the table: every planted fault is found
(check, severity, name, and a word of the detail), and nothing is reported about a declaration the table does not name. Then
the replay: tools/jinshi/fixtures/Forged.lean, a proof of False that skipped the kernel (it compiles, and Lean reports no
axioms), must be refused by leanchecker, and by lean4lean when JINSHI_LEAN4LEAN names its binary; every other fixture must be
accepted by both. Exit 1 on any difference, with the lines that differ.

A new examination brings its own fixture and table (one file each, no shared file to edit); a fixture may be restricted to its
own examination with a first line `-- jinshi: only <check>[,<check>]` (other examinations' findings on it are then not judged).
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIX = ROOT / "tools" / "jinshi" / "fixtures"
ONLY = re.compile(r"^--[ \t]*jinshi:[ \t]*only[ \t]+([\w, \t]+?)[ \t]*$", re.M)

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run import autoimplicit_findings, lean4lean_finding, replay_finding  # noqa: E402


def sh(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def read_expected(path: Path) -> list[tuple[str, str, str, str]]:
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        check, sev, name, word = line.split("\t")
        out.append((check, sev, name, word))
    return out


def main() -> int:
    exe = ROOT / ".lake" / "build" / "bin" / "tengoku-jinshi"
    if not exe.is_file():
        print("build the examinations first: lake build tengoku-jinshi", file=sys.stderr)
        return 2
    fixtures = sorted(p.stem for p in FIX.glob("*.lean") if (FIX / f"{p.stem}.expected.tsv").is_file() and p.stem != "Forged")
    examined = fixtures + ["Forged"]  # Forged is examined (its table says what `decide` must find) but never expected to pass the replay
    if not fixtures:
        print("no fixture has an expected table", file=sys.stderr)
        return 2
    problems: list[str] = []
    total_found = total_expected = 0
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp) / "JinshiFixtures"
        out.mkdir()
        lean_path = os.pathsep.join(p for p in [sh(["lake", "env", "printenv", "LEAN_PATH"]).stdout.strip(), tmp] if p)
        env = dict(os.environ, LEAN_PATH=lean_path)
        for name in fixtures + ["Forged"]:
            r = sh(["lake", "env", "lean", "-o", str(out / f"{name}.olean"), "-i", str(out / f"{name}.ilean"), str(FIX / f"{name}.lean")])
            if r.returncode:
                print(f"{name}.lean does not compile:\n" + r.stdout + r.stderr)
                return 2
        # the environment examinations, one process, every fixture a module
        args = [str(exe), "--seed", "Init"]
        for name in examined:
            args += ["--module", f"JinshiFixtures.{name}"]
        r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
        if r.returncode:
            print(r.stdout + r.stderr)
            return 2
        found = [json.loads(line) for line in r.stdout.splitlines() if line.strip()]
        found = [f for f in found if f["check"] != "summary"]
        for name in fixtures:
            found += [
                f for f in autoimplicit_findings(FIX / f"{name}.lean", f"JinshiFixtures.{name}", lake=True) if f["check"] != "reproduce"
            ]
        # judged per fixture: the findings on its module against its table
        for name in examined:
            text = (FIX / f"{name}.lean").read_text(encoding="utf-8")
            only = ONLY.search(text)
            only_checks = {c.strip() for c in only.group(1).split(",")} if only else None
            mine = [
                f
                for f in found
                if f["module"] == f"JinshiFixtures.{name}"
                and (only_checks is None or f["check"] in only_checks)
                and f["name"] not in ("", "[anonymous]")
            ]
            expected = read_expected(FIX / f"{name}.expected.tsv")
            total_found += len(mine)
            total_expected += len(expected)
            for check, sev, dname, word in expected:
                hits = [f for f in mine if f["check"] == check and f["name"] == dname]
                if not any(f["severity"] == sev and word in f["detail"] for f in hits):
                    problems.append(
                        f"{name}: MISSING  {check}/{sev} {dname} (detail containing {word!r}); got: {[(f['severity'], f['detail'][:80]) for f in hits]}"
                    )
            named = {d for _, _, d, _ in expected}
            for f in mine:
                if f["name"] not in named:
                    problems.append(f"{name}: UNEXPECTED {f['check']}/{f['severity']} {f['name']}: {f['detail'][:120]}")
                elif not any(f["check"] == c and f["severity"] == s and w in f["detail"] for c, s, d, w in expected if d == f["name"]):
                    problems.append(f"{name}: EXTRA    {f['check']}/{f['severity']} {f['name']}: {f['detail'][:120]}")
        # the replay: the forged module refused, every other accepted, by every kernel at hand
        os.environ["LEAN_PATH"] = lean_path
        for kernel, fn in (("replay", replay_finding), ("lean4lean", lean4lean_finding)):
            if kernel == "lean4lean" and not os.environ.get("JINSHI_LEAN4LEAN"):
                print("lean4lean: JINSHI_LEAN4LEAN is not set, its replay is not tested here")
                continue
            forged = fn("JinshiFixtures.Forged")
            if not any(f["severity"] == "fail" for f in forged):
                problems.append(f"Forged: MISSING  {kernel}/fail: the forged proof of False was NOT refused; got {forged}")
            honest = [f for name in fixtures for f in fn(f"JinshiFixtures.{name}")]
            if honest:
                problems.append(f"{kernel}: EXTRA on an honest fixture: {honest}")
            print(
                f"{kernel}: the forged module {'refused' if forged else 'ACCEPTED'}, {len(fixtures)} honest module(s) {'accepted' if not honest else 'REFUSED'}"
            )
    for p in problems:
        print(p)
    print(f"jinshi selftest: {len(fixtures)} fixtures, {total_found} findings, {total_expected} expected, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
