"""axioms_check.py against a fake tengoku-axioms: clashing modules are split apart, not checked one run per module.

The fake reads its rules from the environment: FAKE_CLASH lists pairs that cannot be imported together
("A:B,C:D"), FAKE_BAD modules with a non-standard axiom, FAKE_ALONE modules that clash with the tree itself. It logs every run (one line per run) and the number of
runs alive at once, so the tests see how many runs were made and that no more than AXIOMS_JOBS overlapped.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]

FAKE = r'''
import fcntl, os, sys, time
mods = [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == "--module"]
log = os.environ["FAKE_LOG"]
def bump(d):
    with open(log + ".live", "a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX); f.seek(0); n = int(f.read() or 0) + d; f.seek(0); f.truncate(); f.write(str(n))
    if d > 0:
        with open(log + ".peak", "a+") as g:
            fcntl.flock(g, fcntl.LOCK_EX); g.seek(0); p = int(g.read() or 0)
            if n > p: g.seek(0); g.truncate(); g.write(str(n))
bump(1)
time.sleep(0.05)
with open(log, "a") as f: f.write(" ".join(mods) + "\n")
bump(-1)
pairs = [p.split(":") for p in os.environ.get("FAKE_CLASH", "").split(",") if p]
self_clash = set(os.environ.get("FAKE_ALONE", "").split(","))
for a, b in pairs:
    if a in mods and b in mods:
        print(f"uncaught exception: import failed, environment already contains '{a}.x' from {a}"); sys.exit(1)
for m in mods:
    if m in self_clash:
        print(f"uncaught exception: import failed, environment already contains '{m}.y' from Tengoku.Core"); sys.exit(1)
bad = [m for m in mods if m in os.environ.get("FAKE_BAD", "").split(",")]
for m in bad: print(f"error: {m}.thm depends on [sorryAx] (allowed: propext, Classical.choice, Quot.sound)")
print(f"axioms: {len(mods)} declarations checked, {len(bad)} with non-standard axioms")
sys.exit(1 if bad else 0)
'''


class AxiomsCheck(unittest.TestCase):
    def setUp(self) -> None:
        self.dir = tempfile.TemporaryDirectory()
        self.fake = Path(self.dir.name, "fake.py")
        self.fake.write_text(FAKE)
        self.log = Path(self.dir.name, "runs.log")

    def tearDown(self) -> None:
        self.dir.cleanup()

    def check(self, mods: list[str], jobs: int = 3, **rules: str) -> tuple[int, str, list[str]]:
        env = {**os.environ, "AXIOMS_TOOL": f"{sys.executable} {self.fake}", "AXIOMS_JOBS": str(jobs), "FAKE_LOG": str(self.log)}
        env.update({f"FAKE_{k.upper()}": v for k, v in rules.items()})
        p = subprocess.run([sys.executable, str(CI / "axioms_check.py"), *mods], capture_output=True, text=True, env=env)
        runs = self.log.read_text().splitlines() if self.log.exists() else []
        return p.returncode, p.stdout + p.stderr, runs

    def peak(self) -> int:
        return int(Path(str(self.log) + ".peak").read_text())

    def test_no_clash_is_one_run(self) -> None:
        rc, out, runs = self.check([f"M{i}" for i in range(40)])
        self.assertEqual((rc, len(runs)), (0, 1), out)
        self.assertIn("40 modules in 1 run(s)", out)

    def test_one_clash_splits_far_fewer_runs_than_modules(self) -> None:
        mods = [f"M{i}" for i in range(40)]
        rc, out, runs = self.check(mods, clash="M3:M30")
        self.assertEqual(rc, 0, out)
        checked = sorted({m for r in runs for m in r.split()})
        self.assertEqual(checked, sorted(mods))
        self.assertLessEqual(len(runs), 3, runs)   # all 40, then two halves that each import
        for r in runs[1:]:
            self.assertFalse({"M3", "M30"} <= set(r.split()), r)

    def test_several_clashes_all_resolved(self) -> None:
        mods = [f"M{i}" for i in range(40)]
        rc, out, runs = self.check(mods, clash="M0:M1,M10:M11,M20:M39,M5:M25")
        self.assertEqual(rc, 0, out)
        self.assertLess(len(runs), 20, runs)
        passed = [r for r in runs if not any(a in r.split() and b in r.split() for a, b in [("M0", "M1"), ("M10", "M11"), ("M20", "M39"), ("M5", "M25")])]
        self.assertEqual(sorted({m for r in passed for m in r.split()}), sorted(mods))

    def test_bad_axiom_fails_and_is_reported(self) -> None:
        rc, out, _ = self.check(["M0", "M1", "M2"], bad="M1")
        self.assertEqual(rc, 1)
        self.assertIn("error: M1.thm depends on [sorryAx]", out)

    def test_bad_axiom_inside_a_split_half_fails(self) -> None:
        rc, out, _ = self.check([f"M{i}" for i in range(8)], clash="M0:M7", bad="M6")
        self.assertEqual(rc, 1)
        self.assertIn("error: M6.thm depends on", out)

    def test_a_module_that_clashes_alone_fails(self) -> None:
        rc, out, _ = self.check(["M0", "M1", "M2", "M3"], alone="M2")
        self.assertEqual(rc, 1)
        self.assertIn("environment already contains 'M2.y'", out)

    def test_parallel_runs_stay_within_the_limit(self) -> None:
        mods = [f"M{i}" for i in range(32)]
        clash = ",".join(f"M{i}:M{i + 1}" for i in range(0, 32, 2))   # forces a split down to single modules
        rc, out, runs = self.check(mods, jobs=2, clash=clash)
        self.assertEqual(rc, 0, out)
        self.assertLessEqual(self.peak(), 2)

    def test_no_modules_is_a_usage_error(self) -> None:
        rc, _, runs = self.check([])
        self.assertEqual((rc, runs), (2, []))


if __name__ == "__main__":
    unittest.main()
