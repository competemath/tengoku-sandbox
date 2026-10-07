"""The `native` class: novel Lean modules under Tengoku/Native/ (scripts/ci/native_check.py; docs/native.md, docs/pr-classes.md section 8). Its own file, so that tests of other
gates added at the end of test_gates.py do not conflict with it."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
from test_gates import Repo  # noqa: E402

BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}
GOOD = "/-\nAuthors: CompeteMath\n-/\nimport Tengoku\n\nnamespace Native.Fx\n\n/-- One plus one. -/\ntheorem one_add_one : 1 + 1 = 2 := rfl\n\nend Native.Fx\n"
SECOND = GOOD.replace("one_add_one", "two_add_two").replace("1 + 1 = 2", "2 + 2 = 4")
TAG = "@isnad1 id=eq.0h2v.s4.05598c1b76c4 from=novel src=0 shape=900bc7c0 vocab=fc0e7020"
A, B = "Tengoku/Native/Fx/A.lean", "Tengoku/Native/Fx/B.lean"
ALL_LINES = "import Tengoku.Lib\n"


class Setup(unittest.TestCase):
    def repo(self, with_native=False):
        r = Repo()
        r.write("Tengoku/All.lean", ALL_LINES + ("import Tengoku.Native\n" if with_native else ""))
        if with_native:
            r.write(A, GOOD)
            r.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\n")
        r.commit("the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def first(self, r, text=GOOD, umbrella="import Tengoku.Native.Fx.A\n", all_=ALL_LINES + "import Tengoku.Native\n"):
        """the first native PR: a module, the umbrella and the import in All.lean"""
        r.write(A, text)
        r.write("Tengoku/Native.lean", umbrella)
        r.write("Tengoku/All.lean", all_)
        r.commit("native")

    def classify(self, r, env=BOT):
        return r.gate("classify.py", env=env)

    def check(self, r):
        return r.gate("native_check.py")


class Gate(Setup):
    def test_the_first_native_pr_is_class_native_and_passes(self):
        r = self.repo()
        self.first(r)
        rc, out = self.classify(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=native (3 files)", out)
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("native ok: 1 modules", out)

    def test_a_later_pr_adds_a_module_and_its_import_only(self):
        r = self.repo(with_native=True)
        r.write(B, SECOND)
        r.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.B\n")
        r.commit("a second module")
        self.assertIn("class=native", self.classify(r)[1])
        self.assertEqual(self.check(r)[0], 0)

    def test_editing_a_module_is_fine(self):
        r = self.repo(with_native=True)
        r.write(A, GOOD.replace("One plus one.", "One plus one, as a sum."))
        r.commit("edit")
        self.assertIn("class=native", self.classify(r)[1])
        self.assertEqual(self.check(r)[0], 0)

    def test_only_the_factory_account_may_send_one(self):
        r = self.repo()
        self.first(r)
        rc, out = self.classify(r, {"PR_ACTOR": "someone", "TENGOKU_BOT": "tengoku-bot"})
        self.assertNotEqual(rc, 0)
        self.assertIn("a native PR comes from the factory's account", out)

    def test_a_native_pr_that_touches_anything_else_is_not_one(self):
        r = self.repo()
        self.first(r)
        r.write("scripts/x.py", "print(2)\n")
        r.commit("and a script")
        self.assertNotIn("class=native", self.classify(r)[1])

    def test_the_check_itself_refuses_a_path_that_is_not_native(self):
        r = self.repo()
        self.first(r)
        r.write("scripts/x.py", "print(2)\n")
        r.write("Tengoku/Seed/Foo.lean", "x\n")
        r.commit("and others")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("not a Native path", out)

    def test_no_module_is_not_a_native_pr(self):
        r = self.repo(with_native=True)
        r.write("Tengoku/All.lean", ALL_LINES + "import Tengoku.Native\n-- x\n")
        r.commit("only All.lean")
        self.assertNotIn("class=native", self.classify(r)[1])

    def test_a_module_may_not_be_deleted_or_moved(self):
        r = self.repo(with_native=True)
        r.git("rm", "-q", A)
        r.write("Tengoku/Native.lean", "")
        r.commit("delete")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        r2 = self.repo(with_native=True)
        r2.git("mv", A, B)
        r2.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.B\n")
        r2.commit("move")
        self.assertNotEqual(self.check(r2)[0], 0)

    def test_the_credit_is_required(self):
        r = self.repo()
        self.first(r, GOOD.replace("Authors: CompeteMath", "Someone wrote this"))
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("no credit", out)

    def test_only_the_seed_and_native_modules_may_be_imported(self):
        for bad in ("import Mathlib", "import Tengoku.Pfr.PFR.Foo", "import Lean", "import Tengoku.Seed.Algebra.Group.Defs"):
            r = self.repo()
            self.first(r, GOOD.replace("import Tengoku\n", f"import Tengoku\n{bad}\n"))
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, bad)
            self.assertIn("Native builds on `Tengoku`", out)
        r = self.repo(with_native=True)
        r.write(B, SECOND.replace("import Tengoku\n", "import Tengoku\nimport Tengoku.Native.Fx.A\n"))
        r.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.B\n")
        r.commit("a native import")
        self.assertEqual(self.check(r)[0], 0)

    def test_what_trusts_the_compiler_or_runs_code_is_refused(self):
        for bad in (
            "theorem x : 1 + 1 = 2 := by native_decide",
            "#eval 1",
            'elab "foo" : command => pure ()',
            "initialize foo : IO.Ref Nat ← IO.mkRef 0",
        ):
            r = self.repo()
            self.first(r, GOOD.replace("end Native.Fx", f"{bad}\n\nend Native.Fx"))
            self.assertNotEqual(self.check(r)[0], 0, bad)

    def test_sorry_is_refused_but_the_word_in_a_comment_is_not(self):
        r = self.repo()
        self.first(r, GOOD.replace(":= rfl", ":= by sorry"))
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("`sorry`", out)
        r2 = self.repo()
        self.first(r2, GOOD.replace("One plus one.", "One plus one; no sorry here."))
        self.assertEqual(self.check(r2)[0], 0)

    def test_a_tag_is_refused_because_the_sweep_writes_them(self):
        r = self.repo()
        self.first(r, GOOD.replace("One plus one. -/", f"One plus one.\n{TAG}\n-/"))
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("isnad tag", out)

    def test_the_umbrella_imports_every_module_once_and_nothing_else(self):
        for umbrella in (
            "",
            "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.A\n",
            "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.Ghost\n",
            "import Tengoku.Native.Fx.A\ndef x := 1\n",
        ):
            r = self.repo()
            self.first(r, umbrella=umbrella)
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, umbrella)
            self.assertIn("Native.lean", out)

    def test_all_lean_gains_exactly_the_import_with_the_first_umbrella(self):
        for all_ in (ALL_LINES, ALL_LINES + "import Tengoku.Native\nimport Tengoku.Other\n", "import Tengoku.Native\n"):
            r = self.repo()
            self.first(r, all_=all_)
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, all_)
            self.assertIn("All.lean", out)

    def test_all_lean_is_left_alone_once_the_umbrella_is_in(self):
        r = self.repo(with_native=True)
        r.write(B, SECOND)
        r.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.B\n")
        r.write("Tengoku/All.lean", ALL_LINES + "import Tengoku.Native\n-- touched\n")
        r.commit("touch All.lean")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("untouched", out)

    def test_a_module_that_is_not_utf8_is_refused(self):
        r = self.repo()
        r.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\n")
        r.write("Tengoku/All.lean", ALL_LINES + "import Tengoku.Native\n")
        (r.dir / A).parent.mkdir(parents=True, exist_ok=True)
        (r.dir / A).write_bytes(GOOD.encode() + b"-- \xff\n")
        r.commit("bad bytes")
        self.assertIn("UTF-8", self.check(r)[1])

    def test_at_most_400_modules(self):
        r = self.repo()
        names = [f"Tengoku.Native.Many.M{i}" for i in range(401)]
        for i in range(401):
            r.write(f"Tengoku/Native/Many/M{i}.lean", GOOD)
        r.write("Tengoku/Native.lean", "".join(f"import {n}\n" for n in names))
        r.write("Tengoku/All.lean", ALL_LINES + "import Tengoku.Native\n")
        r.commit("401 modules")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("at most 400", out)

    def test_the_queue_builds_the_modules_and_all_of_native_when_one_is_edited(self):
        r = self.repo()
        self.first(r)
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.split() if ln.startswith("Tengoku.")], ["Tengoku.Native.Fx.A"])
        r2 = self.repo(with_native=True)
        r2.write(A, GOOD.replace("One plus one.", "Edited."))
        r2.write(B, SECOND)
        r2.write("Tengoku/Native.lean", "import Tengoku.Native.Fx.A\nimport Tengoku.Native.Fx.B\n")
        r2.commit("edit and add")
        rc, out = r2.gate("queue_targets.py")
        self.assertEqual(
            sorted(ln for ln in out.split() if ln.startswith("Tengoku.")), ["Tengoku.Native", "Tengoku.Native.Fx.A", "Tengoku.Native.Fx.B"]
        )

    def test_a_native_group_has_nothing_to_regenerate(self):
        r = self.repo()
        self.first(r)
        rc, out = r.gate("queue_targets.py", "main", "pr", "--regenerate")
        self.assertEqual(rc, 0, out)
        self.assertEqual([ln for ln in out.split() if ln.startswith("Tengoku.")], [])


if __name__ == "__main__":
    unittest.main()
