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
import time
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
        def mark(what: str) -> None:  # progress with the children's peak memory: a runner that dies says where
            import resource

            peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            peak_mb = peak // (1024 if sys.platform != "darwin" else 1024 * 1024)
            print(f"[selftest {time.time() - t0:5.0f} s, peak child {peak_mb} MB] {what}", flush=True)

        t0 = time.time()
        for name in fixtures + ["Forged"]:
            r = sh(["lake", "env", "lean", "-o", str(out / f"{name}.olean"), "-i", str(out / f"{name}.ilean"), str(FIX / f"{name}.lean")])
            if r.returncode:
                print(f"{name}.lean does not compile:\n" + r.stdout + r.stderr)
                return 2
            mark(f"compiled {name}")
        # the environment examinations, one process, every fixture a module
        args = [str(exe), "--seed", "Init"]
        for name in examined:
            args += ["--module", f"JinshiFixtures.{name}"]
        if os.environ.get("JINSHI_SELFTEST_PROBE", "1") != "0":  # on by default for this diagnostic commit
            # DIAGNOSTIC (temporary): one process per examination over every fixture, each under a 3 GB address-space cap, so the
            # examination that exhausts a runner's memory names itself; the combined run is then skipped.
            import resource

            def cap() -> None:
                resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))

            names = [ln.strip() for ln in sh([str(exe), "--list"]).stdout.splitlines() if ln.strip()]
            for check in names:
                before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
                t1 = time.time()
                r = subprocess.run(args + ["--check", check], cwd=ROOT, capture_output=True, text=True, env=env, preexec_fn=cap)
                after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
                n = sum(1 for ln in r.stdout.splitlines() if ln.strip())
                print(f"[probe] {check:12s} rc={r.returncode} {time.time() - t1:5.1f} s peak-so-far {after // 1024} MB (was {before // 1024}) {n} lines; {(r.stderr or '')[-200:].strip()!r}", flush=True)
            return 3
        mark("running every examination over every fixture in one process")
        r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
        mark(f"the executable returned {r.returncode}")
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
    # mutants (appended block): the fixture's mutant modules, generated into a directory of their own, judged by every kernel at hand
    # (leanchecker; lean4lean when JINSHI_LEAN4LEAN names it): no disagreement with Lean's in-process verdict, and at least one mutant
    # refused by every kernel and one accepted by every kernel
    from mutants import generate, judge  # noqa: E402

    # (the mutants' directory is NOT under the fixtures' LEAN_PATH entry: a module is named by the search-path entry it is found under)
    with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as mtmp:
        out = Path(tmp) / "JinshiFixtures"
        out.mkdir()
        r = sh(["lake", "env", "lean", "-o", str(out / "Mutants.olean"), "-i", str(out / "Mutants.ilean"), str(FIX / "Mutants.lean")])
        if r.returncode:
            problems.append("Mutants: the fixture does not compile for the kernels' run: " + (r.stdout + r.stderr)[-300:])
        else:
            lean_path = os.pathsep.join(p for p in [sh(["lake", "env", "printenv", "LEAN_PATH"]).stdout.strip(), tmp] if p)
            env = dict(os.environ, LEAN_PATH=lean_path)
            mdir = Path(mtmp) / "mutants"
            gen = generate(["JinshiFixtures.Mutants"], mdir, seed="Init", env=env)
            fs, verdicts = judge(mdir, jobs=4, env=env)
            for f in gen + fs:
                if f["severity"] == "fail":
                    problems.append(f"Mutants: KERNELS DISAGREE {f['name']}: {f['detail'][:300]}")
                elif f["severity"] == "warn":
                    problems.append(f"Mutants: WARN {f['name']}: {f['detail'][:300]}")
            accepted = sum(1 for v in verdicts if all(x == "accept" for x in v["verdicts"].values()))
            refused = sum(1 for v in verdicts if all(x == "reject" for x in v["verdicts"].values()))
            if not verdicts:
                problems.append("Mutants: MISSING  no mutant module was generated")
            if verdicts and not accepted:
                problems.append("Mutants: MISSING  no mutant accepted by every kernel")
            if verdicts and not refused:
                problems.append("Mutants: MISSING  no mutant refused by every kernel")
            kernels = ["lean", "leanchecker"] + (["lean4lean"] if os.environ.get("JINSHI_LEAN4LEAN") else [])
            print(
                f"mutants: {len(verdicts)} mutants, {accepted} accepted by every kernel, {refused} refused by every kernel, "
                f"{len(verdicts) - accepted - refused} disagreements or timeouts (kernels: {', '.join(kernels)})"
            )
    for p in problems:
        print(p)
    print(f"jinshi selftest: {len(fixtures)} fixtures, {total_found} findings, {total_expected} expected, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
