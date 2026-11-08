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
from run import autoimplicit_findings, candidates_in_scope, lean4lean_finding, near_miss, replay_finding  # noqa: E402


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
        mark("running every examination over every fixture in one process")
        r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
        mark(f"the executable returned {r.returncode}")
        if r.returncode:
            print(r.stdout + r.stderr)
            return 2
        found = [json.loads(line) for line in r.stdout.splitlines() if line.strip()]
        # arithUniverse is self-contained and synthetic (docs/jinshi.md): it reads no fixture module, but its findings are
        # still attributed to whatever module happens to be first on the command line (c.mods.headD, as `decide`'s summary
        # already does), so it is examined on its own below instead of against a fixture's expected table
        found = [f for f in found if f["check"] not in ("summary", "arithUniverse")]
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
        # arithUniverse: self-contained, no fixture of its own — the smallest smoke test is that the executable knows it
        # and that a standalone run over one trivial seed module returns its summary line with 0 "fail"s
        lst = subprocess.run([str(exe), "--list"], cwd=ROOT, capture_output=True, text=True)
        if "arithUniverse" not in lst.stdout.splitlines():
            problems.append("arithUniverse: MISSING from --list")
        else:
            au = subprocess.run(
                [str(exe), "--seed", "Init", "--module", f"JinshiFixtures.{fixtures[0]}", "--check", "arithUniverse"],
                cwd=ROOT,
                capture_output=True,
                text=True,
                env=env,
            )
            au_lines = [json.loads(l) for l in au.stdout.splitlines() if l.strip()]
            au_findings = [l for l in au_lines if l.get("check") == "arithUniverse"]
            au_summary = [f for f in au_findings if f.get("name") in ("", "[anonymous]") and "universe:" in f.get("detail", "")]
            au_fails = [f for f in au_findings if f.get("severity") == "fail"]
            if au.returncode or not au_summary:
                problems.append(
                    f"arithUniverse: MISSING standalone summary line; returncode {au.returncode}: {(au.stdout + au.stderr)[-300:]}"
                )
            elif au_fails:
                problems.append(
                    f"arithUniverse: {len(au_fails)} fail finding(s) on a standalone run: {[f['detail'][:160] for f in au_fails]}"
                )
            else:
                print(f"arithUniverse: {au_summary[0]['detail']}")
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
    # (leanchecker; lean4lean when JINSHI_LEAN4LEAN names it; nanoda when NANODA_BIN and JINSHI_LEAN4EXPORT name their binaries): no
    # disagreement with Lean's in-process verdict, and at least one mutant refused by every kernel and one accepted by every kernel.
    # Neither NANODA_BIN nor JINSHI_LEAN4EXPORT set: nanoda.py's nanoda_verdict is never called (mutants.py's judge() adds the
    # "nanoda" column only when NANODA_BIN is set), so everything below this comment behaves exactly as it did before nanoda existed.
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
            # a nanoda "skip" (a trusted-head mutant, nanoda.py's TRUSTED_HEADS) is not a verdict to agree or disagree with -- judge()
            # already drops it the same way before comparing kernels, so the two invariants below ("every kernel") are judged on
            # the same (non-skip) verdicts judge() itself compared, never penalising a mutant nanoda chose not to judge
            judged = [{k: x for k, x in v["verdicts"].items() if x != "skip"} for v in verdicts]
            accepted = sum(1 for j in judged if all(x == "accept" for x in j.values()))
            refused = sum(1 for j in judged if all(x == "reject" for x in j.values()))
            if not verdicts:
                problems.append("Mutants: MISSING  no mutant module was generated")
            if verdicts and not accepted:
                problems.append("Mutants: MISSING  no mutant accepted by every kernel")
            if verdicts and not refused:
                problems.append("Mutants: MISSING  no mutant refused by every kernel")
            kernels = ["lean", "leanchecker"] + (["lean4lean"] if os.environ.get("JINSHI_LEAN4LEAN") else [])
            if os.environ.get("NANODA_BIN"):
                kernels.append("nanoda")
                # NANODA_BIN is set: if no verdict even carries a "nanoda" key, judge() silently treated it as unset (a wiring bug
                # between this script's env and judge()'s kenv.get("NANODA_BIN") -- the whole point of exercising this path here)
                if verdicts and not any("nanoda" in v["verdicts"] for v in verdicts):
                    problems.append("Mutants: MISSING  NANODA_BIN is set but no mutant's verdicts carry a nanoda column")
                skipped = sum(1 for v in verdicts if v["verdicts"].get("nanoda") == "skip")
                print(f"mutants: nanoda judged {len(verdicts) - skipped} mutant(s), skipped {skipped} (trusted head)")
            print(
                f"mutants: {len(verdicts)} mutants, {accepted} accepted by every kernel, {refused} refused by every kernel, "
                f"{len(verdicts) - accepted - refused} disagreements or timeouts (kernels: {', '.join(kernels)})"
            )
    # autoimplicit near-miss (scripts/jinshi/run.py): pure Python, no Lean needed. The first version
    # of near_miss() picked an arbitrary tied candidate depending on a set's iteration order (caught
    # locally before this ever reached a fixture); each case below is a permanent regression test,
    # named for the exact thing it once got wrong or must keep getting right.
    nm_cases = [
        ("a typo of an in-scope binder is found and unique",
         "theorem bar (xs : List alpha) (n : Nat) (hyp : foo xs m = 0) : foo xs n = 0 := by sorry",
         1, "m", ("n", 1)),
        ("a typo of a variable-block name is found across the whole file, not just the declaration",
         "variable (generalResult : Nat)\n\ntheorem t2 : generalResul = generalResult := by sorry\n",
         3, "generalResul", ("generalResult", 1)),
        ("a tie between two equally-close candidates is ambiguous, not an arbitrary pick",
         "theorem bar (n : Nat) (h : Nat) (hyp : foo m = 0) : True := trivial",
         1, "m", None),
        ("a genuinely free, intentional type variable with nothing nearby is not flagged",
         "theorem baz (xs : List delta) : xs = xs := rfl",
         1, "delta", None),
        ("a long, clearly-different identifier does not match a short unrelated one",
         "theorem t (n : Nat) (xs : List Nat) : True := trivial",
         1, "completely_different_name", None),
    ]
    for label, text, line, ident, expected in nm_cases:
        cands = candidates_in_scope(text, line) - {ident}
        got = near_miss(ident, cands)
        if got != expected:
            problems.append(f"near_miss: FAIL [{label}]: near_miss({ident!r}, ...) = {got!r}, expected {expected!r}")
    for p in problems:
        print(p)
    print(f"jinshi selftest: {len(fixtures)} fixtures, {total_found} findings, {total_expected} expected, {len(problems)} problems")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
