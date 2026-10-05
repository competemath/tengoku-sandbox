"""The gates, tested against synthetic repositories: every rule has a case that must fail and one that must pass."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
TREE = CI.parents[1]
GOOD = {
    "name": "Lib.good",
    "statement": "theorem Lib.good : 1 + 1 = 2",
    "proof": ":= rfl",
    "status": "staging",
    "library": "lib",
    "source_url": "https://github.com/leanprover-community/mathlib4/blob/x/y.lean#L1",
    "toolchain": "leanprover/lean4:v4.34.0-rc2",
}


class Repo:
    def __init__(self):
        self.dir = Path(tempfile.mkdtemp())
        shutil.copytree(TREE / "schemas", self.dir / "schemas")
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@t")
        self.git("config", "user.name", "t")
        self.write("data/staging/lib.jsonl", json.dumps(GOOD) + "\n")
        self.write(
            "data/trusted/lib.jsonl",
            json.dumps(
                {
                    **GOOD,
                    "name": "Lib.old",
                    "statement": "theorem Lib.old : 1 + 1 = 2",
                    "status": "trusted",
                    "promoted_at": "2026-01-01T00:00:00Z",
                }
            )
            + "\n",
        )
        self.write("Tengoku/Lib/Basic.lean", "/-\nAuthors: Someone\n-/\ntheorem Lib.old : 1 + 1 = 2 := rfl\n")
        self.write("Tengoku/Logic/Basic.lean", "/-\nAuthors: Mathlib\n-/\ntheorem seeded : True := trivial\n")
        self.write("scripts/x.py", "print(1)\n")
        self.write("README.md", "# t\n")
        self.commit("base")
        self.git("checkout", "-q", "-b", "pr")

    def git(self, *a):
        return subprocess.run(["git", *a], cwd=self.dir, capture_output=True, text=True, check=True).stdout

    def write(self, p, s):
        (self.dir / p).parent.mkdir(parents=True, exist_ok=True)
        (self.dir / p).write_text(s, encoding="utf-8")

    def append(self, p, s):
        with (self.dir / p).open("a", encoding="utf-8") as f:
            f.write(s)

    def commit(self, msg, signoff=True):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg + ("\n\nSigned-off-by: t <t@t>" if signoff else ""))

    def gate(self, script, *args, env=None):
        r = subprocess.run(
            [sys.executable, str(CI / script), *(args or ("main", "pr"))],
            cwd=self.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(self.dir), **(env or {})},
        )
        return r.returncode, (r.stdout + r.stderr)


class Gates(unittest.TestCase):
    def test_clean_append_passes_everything(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new", "statement": "theorem Lib.new : 1 + 1 = 2"}) + "\n")
        r.commit("add")
        for s in ["classify.py", "append_only.py", "credits.py", "validate_records.py", "lint_banked.py", "dco.py"]:
            rc, out = r.gate(s)
            self.assertEqual(rc, 0, f"{s}: {out}")
        self.assertIn("class=content", r.gate("classify.py")[1])

    def test_credit_docstring_in_statement_passes_and_is_protected(self):
        r = Repo()
        doc = "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n"
        rec = {**GOOD, "name": "Lib.credited", "statement": doc + "theorem Lib.credited : 1 + 1 = 2"}
        r.append("data/staging/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("add")
        for s in ["classify.py", "append_only.py", "credits.py", "validate_records.py", "lint_banked.py"]:
            rc, out = r.gate(s)
            self.assertEqual(rc, 0, f"{s}: {out}")
        r.git("checkout", "-q", "-b", "strip")
        r.write(
            "data/staging/lib.jsonl", json.dumps(GOOD) + "\n" + json.dumps({**rec, "statement": "theorem Lib.credited : 1 + 1 = 2"}) + "\n"
        )
        r.commit("drop the credit")
        rc, out = r.gate("credits.py", "pr", "strip")
        self.assertEqual(rc, 1)
        self.assertIn("Author:", out)

    def test_vacuous_theorem_needs_an_acknowledgement(self):
        r = Repo()
        rec = {
            **GOOD,
            "name": "Lib.vac",
            "statement": "theorem Lib.vac (n : Nat) (h : n < 0) : n = 1",
            "proof": ":= by omega",
            "source_path": "lib/A.lean",
            "context": "",
        }
        r.append("data/staging/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("add")
        report = r.dir / "report.txt"
        report.write_text(
            "tactics available: [omega]\nVACUOUS Lib.vac Tengoku.Lib._candidate_A omega\n  its assumptions can never all hold; `omega` derives a contradiction from:\n    h : n < 0\nchecked 1 theorems in 1 modules: 1 vacuous\n"
        )
        env = {"VACUITY_REPORT": str(report), "VACUITY_TARGETS": "0"}
        (r.dir / "body.txt").write_text("Adds a lemma.\n")
        rc, out = r.gate("vacuity.py", "main", "pr", str(r.dir / "body.txt"), env=env)
        self.assertEqual(rc, 1)
        self.assertIn("Lib.vac", out)
        self.assertIn("h : n < 0", out)
        self.assertIn("Vacuous-Ack: Lib.vac:", out)
        (r.dir / "body.txt").write_text(
            "Adds a lemma.\n\nVacuous-Ack: Lib.vac: the source states it this way; the theorem documents the impossible case.\n"
        )
        rc, out = r.gate("vacuity.py", "main", "pr", str(r.dir / "body.txt"), env=env)
        self.assertEqual(rc, 0, out)
        self.assertIn("acknowledged", out)
        # the checker reports the name with the namespaces the module opens around the record (the
        # sandbox's acked scenario failed here: FirstOrder.Language.Formula.Selftest.vac2); the name as the
        # record writes it acknowledges it, a different name does not
        report.write_text(
            "tactics available: [omega]\nVACUOUS Ctx.Deep.Lib.vac Tengoku.Lib._candidate_A omega\n  its assumptions can never all hold; `omega` derives a contradiction from:\n    h : n < 0\nchecked 1 theorems in 1 modules: 1 vacuous\n"
        )
        rc, out = r.gate("vacuity.py", "main", "pr", str(r.dir / "body.txt"), env=env)
        self.assertEqual(rc, 0, out)
        self.assertIn("Ctx.Deep.Lib.vac is vacuous and acknowledged", out)
        (r.dir / "body.txt").write_text("Vacuous-Ack: vac: not the record's name, only its last component.\n")
        rc, out = r.gate("vacuity.py", "main", "pr", str(r.dir / "body.txt"), env=env)
        self.assertEqual(rc, 1)
        self.assertIn("Vacuous-Ack: Ctx.Deep.Lib.vac:", out)
        report.write_text("checked 1 theorems in 1 modules: 0 vacuous\n")
        rc, out = r.gate("vacuity.py", "main", "pr", str(r.dir / "body.txt"), env=env)
        self.assertEqual(rc, 0, out)

    def test_multi_purpose_fails_classify(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new", "statement": "theorem Lib.new : 1 + 1 = 2"}) + "\n")
        r.write("scripts/x.py", "print(2)\n")
        r.commit("two things")
        rc, out = r.gate("classify.py")
        self.assertEqual(rc, 1)
        self.assertIn("multi-purpose", out)

    def test_docs_may_ride_along(self):
        r = Repo()
        r.write("scripts/x.py", "print(2)\n")
        r.write("README.md", "# t2\n")
        r.commit("tooling+docs")
        rc, out = r.gate("classify.py")
        self.assertEqual(rc, 0)
        self.assertIn("class=tooling", out)

    def test_a_file_that_is_not_utf8_does_not_end_a_gate_in_a_traceback(self):
        """git's output for such a file used to fail to decode (credits.py, on the fuzzer's own corpus)."""
        r = Repo()
        (r.dir / "README.md").write_bytes(b"# t\n\xff\xfe\n")
        r.commit("a document with bytes that are not UTF-8")
        for gate in ("credits.py", "classify.py"):
            with self.subTest(gate=gate):
                rc, out = r.gate(gate)
                self.assertNotIn("Traceback", out)

    def test_derived_edit_fails_classify(self):
        r = Repo()
        r.write("Tengoku/Lib/Basic.lean", "theorem Lib.old : 1 + 1 = 2 := by rfl\n")
        r.commit("hand edit")
        rc, out = r.gate("classify.py")
        self.assertEqual(rc, 1)
        self.assertIn("derived", out)

    def test_seeded_module_is_tooling_not_derived(self):
        r = Repo()
        r.write("Tengoku/Logic/Basic.lean", "/-\nAuthors: Mathlib\n-/\ntheorem seeded : True := trivial\ntheorem more : True := trivial\n")
        r.commit("seed")
        rc, out = r.gate("classify.py")
        self.assertEqual(rc, 0)
        self.assertIn("class=tooling", out)

    def test_deletion_in_staging_fails_append_only(self):
        r = Repo()
        r.write("data/staging/lib.jsonl", "")
        r.commit("wipe")
        rc, out = r.gate("append_only.py")
        self.assertEqual(rc, 1)
        self.assertIn("append-only", out)

    def test_edit_in_place_fails_append_only(self):
        r = Repo()
        r.write("data/staging/lib.jsonl", json.dumps({**GOOD, "proof": ":= by decide"}) + "\n")
        r.commit("edit")
        rc, out = r.gate("append_only.py")
        self.assertEqual(rc, 1)
        self.assertIn("line 1", out)

    def test_tombstone_is_an_append(self):
        r = Repo()
        r.append(
            "data/trusted/lib.jsonl",
            json.dumps({"tombstone": "Lib.old", "category": "incorrect", "reason": "wrong", "by": "t", "at": "2026-09-15"}) + "\n",
        )
        r.commit("retract")
        self.assertEqual(r.gate("append_only.py")[0], 0)
        self.assertEqual(r.gate("validate_records.py")[0], 0)
        self.assertIn("class=tombstone", r.gate("classify.py")[1])

    def test_removed_author_line_fails_credits(self):
        r = Repo()
        r.write("Tengoku/Logic/Basic.lean", "/-\n-/\ntheorem seeded : True := trivial\n")
        r.commit("strip credit")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 1)
        self.assertIn("Authors", out)

    def test_records_schema(self):
        r = Repo()
        bad = [
            json.dumps({**GOOD, "name": "Lib.a", "statement": "theorem Lib.a : 1 + 1 = 2", "status": "trusted"}),
            json.dumps({**GOOD, "name": "Lib.b", "statement": "theorem Lib.b : 1 + 1 = 2", "source_url": "https://evil.example/x"}),
            json.dumps({**GOOD, "name": "Lib.old", "statement": "theorem Lib.old : 1 + 1 = 2"}),
            "{not json",
            json.dumps({**GOOD, "name": "Lib.c", "statement": "theorem Lib.c : 1 + 1 = 2", "library": "other"}),
        ]
        r.append("data/staging/lib.jsonl", "\n".join(bad) + "\n")
        r.commit("bad records")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 1)
        for needle in ["status 'trusted'", "allowlist", "already trusted", "not JSON", "library 'other'"]:
            self.assertIn(needle, out)

    def test_content_lint(self):
        r = Repo()
        for i, (body, why) in enumerate(
            [
                ("#eval IO.println 1", "#eval"),
                ("initialize foo : IO Unit := pure ()", "initialize"),
                ('@[simp] macro "x" : term => `(1)', "macro"),
                ("theorem t : True := by native_decide", "native_decide"),
                ("set_option pp.proofs true in\ntheorem t : True := trivial", "pp.proofs"),
            ]
        ):
            r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": f"Lib.bad{i}", "context": body}) + "\n")
        r.append(
            "data/staging/lib.jsonl",
            json.dumps(
                {
                    **GOOD,
                    "name": "Lib.fine",
                    "context": "initialize_simps_projections Foo (toFun → apply)\nset_option maxHeartbeats 400000 in",
                    "proof": ":= by\n  aesop (add unsafe ModEq.mul)",
                }
            )
            + "\n",
        )
        r.commit("lint cases")
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 1)
        for needle in ["#eval", "initialize", "macro", "native_decide", "pp.proofs"]:
            self.assertIn(needle, out)
        self.assertNotIn("Lib.fine", out)

    def test_unsigned_commit_fails_dco(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new", "statement": "theorem Lib.new : 1 + 1 = 2"}) + "\n")
        r.commit("unsigned", signoff=False)
        rc, out = r.gate("dco.py")
        self.assertEqual(rc, 1)
        self.assertIn("Signed-off-by", out)

    def test_sorry_scan_is_advisory(self):
        r = Repo()
        r.append(
            "data/staging/lib.jsonl",
            json.dumps({**GOOD, "name": "Lib.s", "statement": "theorem Lib.s : 1 + 1 = 2", "proof": ":= by sorry"}) + "\n",
        )
        r.commit("sorry")
        rc, out = r.gate("sorry_scan.py")
        self.assertEqual(rc, 0)
        self.assertIn("Lib.s", out)

    def test_queue_comment_explains_the_first_error(self):
        r = Repo()
        r.write("Tengoku/Lib/_candidate_lib.lean", "theorem Lib.bad : 1 = 2 := by\n  rfl\n")
        r.commit("c")
        r.write(
            "build.log",
            "✖ [1/1] Building Tengoku.Lib._candidate_lib\nTengoku/Lib/_candidate_lib.lean:2:2: error: The rfl tactic failed. unsolved goals\n⊢ 1 = 2\n",
        )
        rc, out = r.gate("queue_comment.py", "build.log", "https://example/run/1")
        self.assertEqual(rc, 0)
        self.assertIn("_candidate_lib.lean:2:2", out)
        self.assertIn("Lib.bad", out)
        self.assertIn("unsolved goals", out.lower())
        self.assertIn("What to do", out)


class ScopeFix(unittest.TestCase):
    """A scope-fix PR: existing modules of an intake library, a registration made local, nothing else (scope_fix_check.py judges every line)."""

    BASIC = "import Tengoku\n\nnamespace Fx\n\ninstance : Coe (ℕ × ℕ) (ℤ × ℤ) := ⟨fun p => p⟩\n\n@[simp] theorem s : 1 + 1 = 2 := rfl\n\ntheorem good : 1 + 1 = 2 := rfl\n\nend Fx\n"
    USE = "import Tengoku\nimport Tengoku.FxLib.Fx.Basic\n\ntheorem use : 1 + 1 = 2 := by simp\n"
    BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}

    def repo(self):
        r = Repo()
        r.write("Tengoku/FxLib/Fx/Basic.lean", self.BASIC)
        r.write("Tengoku/FxLib/Fx/Use.lean", self.USE)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\nimport Tengoku.FxLib.Fx.Use\n")
        r.write("data/intake/fx-lib/manifest.jsonl", json.dumps({"name": "Fx.good", "library": "fx-lib"}) + "\n")
        r.commit("an intake library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def edit(self, r, basic=None, use=None, extra=()):
        if basic is not None:
            r.write("Tengoku/FxLib/Fx/Basic.lean", basic)
        if use is not None:
            r.write("Tengoku/FxLib/Fx/Use.lean", use)
        for path, text in extra:
            r.write(path, text)
        r.commit("scope fix")

    def judge(self, r):
        rc, out = r.gate("classify.py", env=self.BOT)
        if rc != 0:
            return rc, out
        self.assertIn("class=scope-fix", out)
        return r.gate("scope_fix_check.py")

    def test_the_exact_transformation_passes(self):
        r = self.repo()
        basic = (
            self.BASIC.replace("instance :", "local instance :").replace("@[simp]", "@[local simp]")
            + "-- Tengoku: 2 registration(s) of this module made local so they do not change other libraries (generated)\n"
        )
        use = self.USE.replace(
            "\ntheorem use", "\nattribute [local instance] Fx.instCoeProdNatInt\nattribute [local simp] Fx.s\n\ntheorem use"
        )
        self.edit(r, basic, use)
        rc, out = self.judge(r)
        self.assertEqual(rc, 0, out)
        self.assertIn("scope-fix ok: 2 modules", out)

    def test_only_the_factory_may_send_one(self):
        r = self.repo()
        self.edit(r, self.BASIC.replace("instance :", "local instance :"))
        rc, out = r.gate("classify.py", env={"PR_ACTOR": "someone", "TENGOKU_BOT": "tengoku-bot"})
        self.assertNotEqual(rc, 0)
        self.assertIn("factory's account", out)

    def test_a_changed_statement_or_a_new_declaration_is_refused(self):
        for basic in (
            self.BASIC.replace("1 + 1 = 2 := rfl\n\nend", "2 + 2 = 4 := rfl\n\nend"),
            self.BASIC.replace("end Fx", "theorem extra : True := trivial\n\nend Fx"),
            self.BASIC.replace("theorem good", "local theorem good"),
            self.BASIC.replace("instance :", "local instance :").replace("\n\nend Fx", "\nend Fx"),
        ):
            r = self.repo()
            self.edit(r, basic)
            rc, out = self.judge(r)
            self.assertNotEqual(rc, 0, basic)

    def test_a_local_in_a_comment_or_a_string_is_refused(self):
        r = self.repo()
        self.edit(
            r,
            self.BASIC.replace("namespace Fx", "-- an instance of the thing\nnamespace Fx").replace(
                "-- an instance", "-- an local instance"
            ),
        )
        self.assertNotEqual(self.judge(r)[0], 0)

    def test_an_added_attribute_must_repeat_a_registration_of_the_library(self):
        r = self.repo()
        self.edit(
            r, None, self.USE.replace("\ntheorem use", "\nattribute [local instance] Matrix.linftyOpNormedAddCommGroup\n\ntheorem use")
        )
        rc, out = self.judge(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("is not an instance this library registers", out)

    def test_other_files_and_other_libraries_are_not_a_scope_fix(self):
        r = self.repo()
        self.edit(r, self.BASIC.replace("instance :", "local instance :"), extra=[("Tengoku/All.lean", "import Tengoku.FxLib\n")])
        rc, out = r.gate("classify.py", env=self.BOT)
        self.assertNotIn("class=scope-fix", out)
        r2 = self.repo()
        self.edit(r2, None, None, extra=[("Tengoku/Lib/Basic.lean", "/-\nAuthors: Someone\n-/\nlocal instance : Foo := x\n")])
        self.assertNotIn("class=scope-fix", r2.gate("classify.py", env=self.BOT)[1])

    def test_the_queue_builds_the_library_of_a_scope_fix_again(self):
        r = ScopeFix().repo()
        r.write("schemas/sources.json", json.dumps({"corpora": {}}))
        r.commit("schemas")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        ScopeFix().edit(r, ScopeFix.BASIC.replace("instance :", "local instance :"))
        rc, out = r.gate("queue_targets.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("Tengoku.FxLib", out.split())


class ScopeFixUnits(unittest.TestCase):
    """The pure parts of scope_fix_check.py, in process."""

    def setUp(self):
        sys.path.insert(0, str(CI))
        import scope_fix_check

        self.sf = scope_fix_check

    def test_the_mask_blanks_comments_and_strings_and_keeps_the_columns(self):
        text = 'a -- instance\n/- x /- nested instance -/ y -/ b "s \\" instance" c /- never closed instance'
        masked = self.sf.mask(text)
        self.assertEqual(len(masked), len(text))
        self.assertEqual(masked.count("\n"), text.count("\n"))
        self.assertNotIn("instance", masked)
        self.assertEqual(masked[:2], "a ")
        self.assertIn(" b ", masked)
        self.assertIn(" c ", masked)

    def test_local_insertion(self):
        ok = self.sf.local_insertion
        self.assertTrue(ok("instance : Foo", "local instance : Foo"))
        self.assertTrue(ok("@[simp, x] theorem t", "@[local simp, x] theorem t"))
        self.assertTrue(ok("attribute [instance] A", "attribute [local instance] A"))
        self.assertFalse(ok("theorem t", "local theorem t"))  # not before instance/simp
        self.assertFalse(ok("simp_all", "local simp_all"))  # a different word
        self.assertFalse(ok("-- instance", "-- local instance"))  # inside a comment
        self.assertFalse(ok("instance", "instance"))  # nothing inserted
        self.assertFalse(ok("instance : A", "local instance : B"))  # something else changed too

    def test_only_global_registrations_count(self):
        text = self.sf.mask(
            "attribute [local instance] A.a\nattribute [-simp] B.b\nattribute [scoped instance] C.c\n"
            "attribute [local simp, instance 100] D.d\nattribute [simp] E.e\nlocal instance f : X := x\n"
            "@[local simp] theorem g : a = b := rfl\n@[simp, to_additive] theorem h : a = b := rfl\ninstance i : Y := y\n"
        )
        got = self.sf.registrations(text)
        self.assertEqual(got["instance"], {"d", "i"})  # `local instance f` and `attribute [local instance] a` are not registrations
        self.assertEqual(got["simp"], {"e", "h"})  # `-simp`, `local simp` (even beside a global instance) are not

    def test_what_a_library_registers_by_kind(self):
        text = self.sf.mask(
            "namespace A\ninstance (priority := low) foo : X := x\n@[simp] theorem s1 : a = b := rfl\n"
            "attribute [instance, simp] B.c\n  D.e\nattribute [reducible] F.g\n-- instance ignored : Y\nend A\n"
        )
        got = self.sf.registrations(text)
        self.assertEqual(got["instance"], {"foo", "c", "e"})
        self.assertEqual(got["simp"], {"s1", "c", "e"})

    def test_added_lines(self):
        known = {"instance": {"foo"}, "simp": {"s1"}}
        f = self.sf.added_line_errors
        self.assertEqual(f("p", 1, "", known), [])
        self.assertEqual(
            f("p", 1, "-- Tengoku: 2 registration(s) of this module made local so they do not change other libraries (generated)", known),
            [],
        )
        self.assertEqual(f("p", 1, "attribute [local instance] X.foo X.instBar", known), [])
        self.assertEqual(f("p", 1, "attribute [local instance 100] X.foo", known), [])
        self.assertEqual(f("p", 1, "attribute [local simp] X.s1", known), [])
        self.assertTrue(f("p", 1, "attribute [local simp] X.foo", known))  # an instance's name is not a simp lemma
        self.assertTrue(f("p", 1, "attribute [local instance] X.s1", known))  # and the other way round
        self.assertTrue(f("p", 1, "attribute [local instance] X.instBar Matrix.other", known))
        self.assertTrue(f("p", 1, "axiom bad : False", known))

    def test_a_removed_or_resized_edit_is_refused(self):
        known = {"instance": set(), "simp": set()}
        self.assertTrue(self.sf.check_file("p", "a\nb\nc", "a\nc", known))  # a line removed
        self.assertTrue(self.sf.check_file("p", "a\nb", "a\nb\nc", known))  # an unexpected line added
        self.assertEqual(self.sf.check_file("p", "a\ninstance : X\nb", "a\nlocal instance : X\nb", known), [])

    def test_file_errors_in_process(self):
        from unittest import mock

        sf = self.sf
        blobs = {("b", "Tengoku/FxLib/Fx/A.lean"): b"instance : X := x\n", ("h", "Tengoku/FxLib/Fx/A.lean"): b"local instance : X := x\n"}
        sf.base, sf.head = "b", "h"
        with mock.patch.object(sf, "blob", lambda rev, p: blobs.get((rev, p))), mock.patch.object(sf, "run", lambda *a, **k: ""):
            cache: dict = {}
            self.assertEqual(sf.file_errors("M", "Tengoku/FxLib/Fx/A.lean", {"FxLib"}, cache), [])
            self.assertIn("FxLib", cache)  # scanned once
            self.assertTrue(sf.file_errors("A", "Tengoku/FxLib/Fx/A.lean", {"FxLib"}, cache))  # added, not modified
            self.assertTrue(sf.file_errors("M", "Tengoku/Other/Fx/A.lean", {"FxLib"}, cache))  # a library that is not an intake bundle
            self.assertTrue(sf.file_errors("M", "README.md", {"FxLib"}, cache))
            self.assertIn("not readable", sf.file_errors("M", "Tengoku/FxLib/Fx/Gone.lean", {"FxLib"}, cache)[0])
            blobs[("h", "Tengoku/FxLib/Fx/B.lean")] = b"\xff\xfe"
            blobs[("b", "Tengoku/FxLib/Fx/B.lean")] = b"x\n"
            self.assertIn("not valid UTF-8", sf.file_errors("M", "Tengoku/FxLib/Fx/B.lean", {"FxLib"}, cache)[0])

    def test_main_in_process(self):
        import io
        from contextlib import redirect_stdout
        from unittest import mock

        sf = self.sf
        ok = [("M", "Tengoku/FxLib/Fx/A.lean"), ("M", "Tengoku/FxLib/Fx/B.lean")]
        with (
            mock.patch.object(sf, "changed_files", lambda b, h: ok),
            mock.patch.object(sf, "intake_namespaces", lambda: {"FxLib"}),
            mock.patch.object(sf, "file_errors", lambda *a: []),
            redirect_stdout(io.StringIO()) as out,
        ):
            sf.main(["x", "b", "h"])
        self.assertIn("scope-fix ok: 2 modules of 1 libraries", out.getvalue())
        with mock.patch.object(sf, "changed_files", lambda b, h: []), mock.patch.object(sf, "intake_namespaces", lambda: set()):
            with self.assertRaises(SystemExit):
                sf.main(["x", "b", "h"])
        many = [("M", f"Tengoku/FxLib/Fx/M{i}.lean") for i in range(12)]
        with (
            mock.patch.object(sf, "changed_files", lambda b, h: many),
            mock.patch.object(sf, "intake_namespaces", lambda: {"FxLib"}),
            mock.patch.object(sf, "file_errors", lambda *a: ["e"]),
        ):
            with self.assertRaises(SystemExit):
                sf.main(["x", "b", "h"])

    def test_intake_namespaces_in_process(self):
        from unittest import mock

        sf = self.sf
        listing = "data/intake/fx-lib/manifest.jsonl\ndata/intake/fx-lib/report.json\ndata/intake/other/manifest.jsonl"
        with mock.patch.object(sf, "run", lambda *a, **k: listing):
            self.assertEqual(sf.intake_namespaces(), {"FxLib", "Other"})


if __name__ == "__main__":
    unittest.main()


class NestedAndPromotion(unittest.TestCase):
    def test_per_pr_staging_file_is_content(self):
        r = Repo()
        r.write(
            "data/staging/lib/pr-42.jsonl", json.dumps({**GOOD, "name": "Lib.pr42", "statement": "theorem Lib.pr42 : 1 + 1 = 2"}) + "\n"
        )
        r.commit("nested")
        self.assertIn("class=content", r.gate("classify.py")[1])
        for s in ["append_only.py", "validate_records.py", "lint_banked.py"]:
            rc, out = r.gate(s)
            self.assertEqual(rc, 0, f"{s}: {out}")

    def test_promotion_is_only_for_the_bot(self):
        r = Repo()
        r.write("data/staging/lib.jsonl", "")
        r.append("data/trusted/lib.jsonl", json.dumps({**GOOD, "status": "trusted", "promoted_at": "2026-09-15T00:00:00Z"}) + "\n")
        r.write("Tengoku/Lib/Basic.lean", "theorem Lib.old : 1 + 1 = 2 := rfl\ntheorem Lib.good : 1 + 1 = 2 := rfl\n")
        r.commit("promote")
        rc, out = r.gate("classify.py")
        self.assertEqual(rc, 1)
        self.assertIn("derived", out)
        os.environ["PR_ACTOR"] = "tengoku-bot"
        try:
            rc, out = r.gate("classify.py")
            self.assertEqual(rc, 0)
            self.assertIn("class=promotion", out)
            self.assertEqual(r.gate("append_only.py", "main", "pr", "--promotion")[0], 0)
        finally:
            del os.environ["PR_ACTOR"]
        os.environ["TENGOKU_ACTOR_CHECKED"] = "1"  # merge group: no actor, already checked on the PR
        try:
            rc, out = r.gate("classify.py")
            self.assertEqual(rc, 0)
            self.assertIn("class=promotion", out)
        finally:
            del os.environ["TENGOKU_ACTOR_CHECKED"]


class CreditsScope(unittest.TestCase):
    def test_tooling_may_mention_provenance_keys(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("scripts/fixture.sh", 'GOOD=\'{"source_url": "https://example/a"}\'\n')
        r.commit("fixture")
        r.git("branch", "-f", "pr", "main")
        r.git("checkout", "-q", "pr")
        r.write("scripts/fixture.sh", 'GOOD=\'{"source_url": "https://example/b", "context": ""}\'\n')
        r.commit("edit fixture")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 0, out)

    def test_data_provenance_stays(self):
        r = Repo()
        r.write(
            "data/trusted/lib.jsonl",
            json.dumps({k: v for k, v in GOOD.items() if k != "source_url"} | {"name": "Lib.old", "status": "trusted"}) + "\n",
        )
        r.commit("strip")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 1)
        self.assertIn("data/trusted/lib.jsonl:1", out)


class QueueComment(unittest.TestCase):
    def test_only_the_removed_pr_is_told_and_the_wording_follows_the_rearm_setup(self):
        r = Repo()
        base = r.git("rev-parse", "HEAD").strip()
        r.git("commit", "-q", "--allow-empty", "-m", "ahead in the group (#2)")
        r.git("commit", "-q", "--allow-empty", "-m", "the removed one (#10)")
        (r.dir / "build.log").write_text("error: Tengoku/Lib/_candidate_Basic.lean:4:2: unsolved goals\n")
        for rearm, wording in (("1", "AUTO re-queue"), ("", "MANUAL re-queue")):
            env = {**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "TENGOKU_COMMENT_DRY": "1", "TENGOKU_REARM": rearm}
            env["GITHUB_REF"] = f"refs/heads/gh-readonly-queue/main/pr-10-{base}"
            out = subprocess.run(
                [sys.executable, str(CI / "queue_comment.py"), "build.log", "https://example/run", base],
                cwd=r.dir,
                capture_output=True,
                text=True,
                env=env,
            ).stdout
            self.assertIn("would comment on: #10\n", out)
            self.assertIn(wording, out)

    def test_names_file_line_record_and_every_pr_in_the_group(self):
        r = Repo()
        r.write("Tengoku/Lib/_candidate_Basic.lean", "theorem Lib.old : 1 + 1 = 2 := rfl\n\ntheorem Lib.bad : 1 + 1 = 3 := by\n  decide\n")
        base = r.git("rev-parse", "HEAD").strip()
        r.git("commit", "-q", "--allow-empty", "-m", "selftest: clean (expect pass) (#2)")
        r.git("commit", "-q", "--allow-empty", "-m", "selftest: broken (expect pass) (#10)")
        (r.dir / "build.log").write_text(
            "error: Tengoku/Lib/_candidate_Basic.lean:4:2: unsolved goals\n  ⊢ 1 + 1 = 3\nerror: something else\n"
        )
        out = subprocess.run(
            [sys.executable, str(CI / "queue_comment.py"), "build.log", "https://example/run", base],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "TENGOKU_COMMENT_DRY": "1", "GITHUB_REF": ""},
        ).stdout
        self.assertIn("would comment on: #2, #10", out)
        self.assertIn("`Tengoku/Lib/_candidate_Basic.lean:4:2`", out)
        self.assertIn("Record: `Lib.bad`", out)
        self.assertIn("unsolved goals\n  ⊢ 1 + 1 = 3\n```", out)
        self.assertNotIn("something else", out)
        self.assertIn("every goal is closed", out)


class PromotionRules(unittest.TestCase):
    def promote(self, r, **changes):
        recs = [json.loads(line) for line in (r.dir / "data/staging/lib.jsonl").read_text().splitlines() if line.strip()]
        r.write("data/staging/lib.jsonl", "")
        for rec in recs:
            r.append(
                "data/trusted/lib.jsonl", json.dumps({**rec, **changes, "status": "trusted", "promoted_at": "2026-09-15T00:00:00Z"}) + "\n"
            )
        r.write(
            "Tengoku/Lib/Basic.lean",
            "import Tengoku\n/-\nAuthors: Someone\n-/\ntheorem Lib.old : 1 + 1 = 2 := rfl\ntheorem Lib.good : 1 + 1 = 2 := rfl\n",
        )
        r.commit("promote")

    def test_moved_record_keeps_its_credit(self):
        r = Repo()
        self.promote(r)
        rc, out = r.gate("credits.py", "main", "pr", "--promotion")
        self.assertEqual(rc, 0, out)
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 0, out)  # the generator's import line is not content

    def test_moved_record_with_changed_provenance_fails(self):
        r = Repo()
        self.promote(r, source_url="https://github.com/leanprover-community/mathlib4/blob/x/Other.lean")
        rc, out = r.gate("credits.py", "main", "pr", "--promotion")
        self.assertEqual(rc, 1)
        self.assertIn("without an identical trusted record", out)

    def test_without_the_flag_a_removed_staging_record_still_fails(self):
        r = Repo()
        self.promote(r)
        self.assertEqual(r.gate("credits.py")[0], 1)

    def test_import_inside_a_record_is_still_forbidden(self):
        r = Repo()
        r.append(
            "data/staging/lib.jsonl",
            json.dumps({**GOOD, "name": "Lib.imp", "statement": "theorem Lib.imp : 1 + 1 = 2", "context": "import Std"}) + "\n",
        )
        r.commit("imp")
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 1)
        self.assertIn("import", out)


class DerivedModuleMapping(unittest.TestCase):
    def test_derived_module_maps_to_its_library(self):
        sys.path.insert(0, str(CI))
        from _git import library_of_module  # noqa: E402

        libs = ["equational-theories", "prime-number-theorem-and"]
        self.assertEqual(library_of_module("Tengoku/EquationalTheories/Completeness.lean", libs), "equational-theories")
        self.assertEqual(library_of_module("Tengoku/EquationalTheories.lean", libs), "equational-theories")
        self.assertEqual(library_of_module("Tengoku/PrimeNumberTheoremAnd/Deps/Basic.lean", libs), "prime-number-theorem-and")
        self.assertIsNone(library_of_module("Tengoku/Logic/Basic.lean", libs))
        self.assertIsNone(library_of_module("data/stats.json", libs))


class QueueCommentRegen(unittest.TestCase):
    def test_regeneration_failure_names_the_files(self):
        r = Repo()
        base = r.git("rev-parse", "HEAD").strip()
        r.git("commit", "-q", "--allow-empty", "-m", "selftest: derived-edit (expect fail) (#12)")
        (r.dir / "build.log").write_text(
            " Tengoku/EquationalTheories/Asterix.lean | 1 -\n 1 file changed, 1 deletion(-)\nerror: regenerated derived files differ from the PR (hand-edited generated file?)\n"
        )
        out = subprocess.run(
            [sys.executable, str(CI / "queue_comment.py"), "build.log", "https://example/run", base],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "TENGOKU_COMMENT_DRY": "1"},
        ).stdout
        self.assertIn("would comment on: #12", out)
        self.assertIn("failed at the regeneration check", out)
        self.assertIn("- `Tengoku/EquationalTheories/Asterix.lean`", out)
        self.assertIn("Do not edit Tengoku/<Library>/** by hand", out)


class LintScope(unittest.TestCase):
    def test_root_tool_program_may_be_unsafe(self):
        r = Repo()
        r.write("TengokuAxioms.lean", "unsafe def main : IO Unit := pure ()\n")
        r.commit("tool")
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 0, out)

    def test_module_may_not_be_unsafe(self):
        r = Repo()
        r.write("Tengoku/Lib/Bad.lean", "unsafe def x : Nat := 1\n")
        r.commit("bad")
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 1)
        self.assertIn("unsafe", out)


class RecordNames(unittest.TestCase):
    def test_name_with_space_or_comma_fails(self):
        for bad in ["Selftest.has space", "Selftest.a,b"]:
            r = Repo()
            r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": bad, "statement": f"theorem {bad} : 1 + 1 = 2"}) + "\n")
            r.commit("bad name")
            rc, out = r.gate("validate_records.py")
            self.assertEqual(rc, 1, bad)
            self.assertIn("not a Lean identifier", out)

    def test_statement_must_declare_the_name(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.other", "statement": "theorem Lib.good : 1 + 1 = 2"}) + "\n")
        r.commit("mismatch")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 1)
        self.assertIn("does not declare", out)


class GateSummary(unittest.TestCase):
    def render(self, jobs_):
        return subprocess.run(
            [sys.executable, str(CI / "gate_summary.py"), "--render-test"],
            input=json.dumps(jobs_),
            capture_output=True,
            text=True,
            env={
                **os.environ,
                "GITHUB_REPOSITORY": "o/r",
                "GITHUB_RUN_ID": "1",
                "PR_NUMBER": "7",
                "HEAD_SHA": "abcdef012345",
                "PR_CLASS": "content",
            },
        ).stdout

    def test_failed_job_gets_step_advice_and_report_link(self):
        out = self.render(
            [
                {"name": "classify", "conclusion": "success", "databaseId": 1, "steps": []},
                {
                    "name": "data-rules",
                    "conclusion": "failure",
                    "databaseId": 2,
                    "steps": [{"name": "append-only", "conclusion": "failure"}],
                },
                {
                    "name": "dco",
                    "conclusion": "failure",
                    "databaseId": 3,
                    "steps": [{"name": "Run python3 scripts/ci/dco.py", "conclusion": "failure"}],
                },
            ]
        )
        self.assertIn("2 checks failed for a `content` PR at `abcdef01`", out)
        self.assertIn("**data-rules** → step *append-only*", out)
        self.assertIn("re-open the file and append", out)
        self.assertIn("Report a gate bug", out)
        self.assertIn("issues/new?labels=gate-bug", out)
        self.assertIn("git commit -s --amend", out)
        self.assertNotIn("Report a gate bug](", out.split("**dco**")[1])  # a low-fragility check gets no report link

    def test_all_passed(self):
        out = self.render(
            [
                {"name": "classify", "conclusion": "success", "databaseId": 1, "steps": []},
                {"name": "pr-gate", "conclusion": "failure", "databaseId": 9, "steps": []},
            ]
        )
        self.assertIn("all checks passed", out)
        self.assertIn("Resolve conversation", out)

    def test_both_verdicts_say_how_to_clear_review_conversations(self):
        passed = self.render(
            [{"name": "dco", "conclusion": "success", "databaseId": 3, "steps": [{"name": "dco", "conclusion": "success"}]}]
        )
        failed = self.render(
            [{"name": "dco", "conclusion": "failure", "databaseId": 3, "steps": [{"name": "dco", "conclusion": "failure"}]}]
        )
        self.assertIn("all checks passed", passed)
        self.assertIn("check failed", failed)
        for out in (passed, failed):  # the whole guidance, in each verdict
            self.assertIn("every review conversation must be resolved", out)
            self.assertIn("(CodeRabbit)", out)
            self.assertIn("fix what applies or reply saying why not", out)
            self.assertIn("**Resolve conversation**", out)
            self.assertIn("As the PR's author you can resolve them yourself", out)


class DeregisteredSource(unittest.TestCase):
    """A source taken off the allowlist takes its tentative/staging data with it; nothing else may be deleted."""

    GONE = {
        **GOOD,
        "name": "Gone.thm",
        "library": "gone",
        "status": "tentative",
        "source_url": "https://github.com/example/gone/blob/x/G.lean#L1",
    }

    def repo_with(self, path, records):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write(path, "".join(json.dumps(x) + "\n" for x in records))
        r.commit("add " + path)
        r.git("checkout", "-q", "-B", "pr")
        return r

    def test_deleting_a_deregistered_sources_tentative_file_passes(self):
        r = self.repo_with("data/tentative/gone.jsonl", [self.GONE, {**self.GONE, "name": "Gone.two"}])
        r.git("rm", "-q", "data/tentative/gone.jsonl")
        r.commit("drop gone")
        rc, out = r.gate("append_only.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("deleted with its source", out)

    def test_deleting_a_registered_sources_file_fails(self):
        r = Repo()
        r.git("rm", "-q", "data/staging/lib.jsonl")
        r.commit("drop lib")
        rc, out = r.gate("append_only.py")
        self.assertEqual(rc, 1)
        self.assertIn("append-only", out)

    def test_a_file_mixing_sources_cannot_be_deleted(self):
        r = self.repo_with("data/tentative/mixed.jsonl", [self.GONE, {**GOOD, "name": "Lib.kept", "status": "tentative"}])
        r.git("rm", "-q", "data/tentative/mixed.jsonl")
        r.commit("drop mixed")
        self.assertEqual(r.gate("append_only.py")[0], 1)

    def test_trusted_records_of_a_deregistered_source_retract_by_tombstone_only(self):
        r = self.repo_with("data/trusted/gone.jsonl", [{**self.GONE, "status": "trusted", "promoted_at": "2026-01-01T00:00:00Z"}])
        r.git("rm", "-q", "data/trusted/gone.jsonl")
        r.commit("drop trusted gone")
        self.assertEqual(r.gate("append_only.py")[0], 1)

    def test_a_deregistered_sources_file_is_still_append_only_while_it_exists(self):
        r = self.repo_with("data/tentative/gone.jsonl", [self.GONE, {**self.GONE, "name": "Gone.two"}])
        r.write("data/tentative/gone.jsonl", json.dumps(self.GONE) + "\n")
        r.commit("shrink gone")
        self.assertEqual(r.gate("append_only.py")[0], 1)

    def test_deleting_a_deregistered_sources_file_is_a_content_pr(self):
        r = self.repo_with("data/tentative/gone.jsonl", [self.GONE])
        r.git("rm", "-q", "data/tentative/gone.jsonl")
        r.commit("drop gone")
        self.assertIn("class=content", r.gate("classify.py")[1])

    def test_credits_let_a_deregistered_sources_file_go(self):
        r = self.repo_with("data/tentative/gone.jsonl", [self.GONE])
        r.git("rm", "-q", "data/tentative/gone.jsonl")
        r.commit("drop gone")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 0, out)

    def test_credits_still_guard_a_registered_sources_file(self):
        r = Repo()
        r.git("rm", "-q", "data/staging/lib.jsonl")
        r.commit("drop lib")
        rc, out = r.gate("credits.py")
        self.assertEqual(rc, 1)
        self.assertIn("provenance", out)


class Export:
    """A tiny lean4export file, written line by line in the exporter's order."""

    def __init__(self) -> None:
        meta = {
            "exporter": {"name": "lean4export", "version": "3.1.0"},
            "format": {"version": "3.1.0"},
            "lean": {"githash": "x", "version": "4.34.0-rc2"},
        }
        self.lines = [json.dumps({"meta": meta})]
        self.names = {"": 0}
        self.terms = 0

    def n(self, s: str) -> int:
        if s not in self.names:
            pre, _, last = s.rpartition(".")
            p = self.n(pre) if pre else 0
            self.names[s] = len(self.names)
            self.lines.append(json.dumps({"in": self.names[s], "str": {"pre": p, "str": last}}))
        return self.names[s]

    def e(self, kind: str, v) -> int:
        self.lines.append(json.dumps({"ie": self.terms, kind: v}))
        self.terms += 1
        return self.terms - 1

    def const(self, s: str) -> int:
        return self.e("const", {"name": self.n(s), "us": []})

    def app(self, f: int, a: int) -> int:
        return self.e("app", {"fn": f, "arg": a})

    def axiom(self, s: str) -> None:
        ty = self.e("sort", 0)
        self.lines.append(json.dumps({"axiom": {"name": self.n(s), "levelParams": [], "type": ty, "isUnsafe": False}}))

    def decl(self, s: str, ty: int, val: int, kind: str = "thm") -> None:
        self.lines.append(json.dumps({kind: {"name": self.n(s), "levelParams": [], "type": ty, "value": val, "all": [self.n(s)]}}))

    def inductive(self, s: str, ctor: str, ty: int, cty: int) -> None:
        types = [
            {"name": self.n(s), "levelParams": [], "type": ty, "numParams": 0, "numIndices": 0, "all": [self.n(s)], "ctors": [self.n(ctor)]}
        ]
        ctors = [{"name": self.n(ctor), "levelParams": [], "type": cty, "induct": self.n(s), "cidx": 0, "numParams": 0, "numFields": 0}]
        self.lines.append(json.dumps({"inductive": {"types": types, "ctors": ctors, "recs": []}}))


class AxiomScan(unittest.TestCase):
    """scripts/ci/axiom_scan.py: every constant's axioms, from the export alone."""

    def scan(self, x: Export, records: list[str] | None = None, tombstones: list[str] = (), index: list[str] = ()):
        """records: the trusted file of a compiled library (Tengoku/Lib.lean exists); index: a library without modules."""
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "tree.ndjson").write_text("\n".join(x.lines) + "\n")
            args = [sys.executable, str(CI / "axiom_scan.py"), "tree.ndjson", "--permitted", "permitted.json"]
            if records is not None:
                (Path(d) / "data/trusted").mkdir(parents=True)
                (Path(d) / "Tengoku").mkdir()
                (Path(d) / "Tengoku/Lib.lean").write_text("")
                lines = [json.dumps({"name": r}) for r in records] + [json.dumps({"tombstone": r}) for r in tombstones]
                (Path(d) / "data/trusted/lib.jsonl").write_text("\n".join(lines) + "\n")
                (Path(d) / "data/trusted/mathlib-index.jsonl").write_text("".join(json.dumps({"name": r}) + "\n" for r in index))
                args += ["--records", "data/trusted"]
            r = subprocess.run(args, cwd=d, capture_output=True, text=True)
            permitted = json.loads((Path(d) / "permitted.json").read_text()) if (Path(d) / "permitted.json").exists() else None
        return r.returncode, r.stdout + r.stderr, permitted

    def standard(self) -> Export:
        x = Export()
        for a in ("propext", "Classical.choice", "Quot.sound"):
            x.axiom(a)
        return x

    def test_standard_axioms_pass_and_are_permitted(self):
        x = self.standard()
        p = x.const("propext")
        x.decl("A", p, x.app(p, p))
        x.decl("NS.B", p, x.const("A"))  # a record named B, declared inside a namespace
        code, out, permitted = self.scan(x, ["A", "B", "Gone"], tombstones=["Gone"])
        self.assertEqual(code, 0, out)
        self.assertEqual(permitted, ["propext", "Classical.choice", "Quot.sound"])
        self.assertIn("2 trusted records, 2 in the export, 2 of them rest only on the standard axioms", out)

    def test_sorry_anywhere_fails_even_through_other_constants(self):
        x = self.standard()
        x.axiom("sorryAx")
        s = x.const("sorryAx")
        x.decl("f", s, s, kind="def")
        x.decl("B", x.const("f"), x.const("f"))
        code, out, _ = self.scan(x)
        self.assertEqual(code, 1, out)
        self.assertIn("2 constants rest on sorryAx", out)
        self.assertIn("B", out)

    def test_native_axioms_fail_a_record_but_are_only_reported_elsewhere(self):
        x = self.standard()
        x.axiom("Lean.ofReduceBool")
        r = x.const("Lean.ofReduceBool")
        x.decl("Core.fast", r, r)
        x.decl("Rec", r, x.const("Core.fast"))
        code, out, permitted = self.scan(x, [])
        self.assertEqual(code, 0, out)  # no record rests on it
        self.assertIn("Lean.ofReduceBool: 2 constants rest on it", out)
        self.assertIn("Lean.ofReduceBool", permitted)
        code, out, _ = self.scan(x, ["Rec"])
        self.assertEqual(code, 1, out)
        self.assertIn("Rec rests on ['Lean.ofReduceBool']", out)

    def test_an_axiom_outside_the_prelude_fails(self):
        x = self.standard()
        x.axiom("Evil.ax")
        code, out, _ = self.scan(x)
        self.assertEqual(code, 1, out)
        self.assertIn("declares the axiom Evil.ax", out)

    def test_an_inductive_mentioning_itself_passes_its_axioms_on(self):
        # The exporter writes `const T` (inside T's own constructor type) before T's line, and every later
        # term that mentions T reuses that same term: its axioms must be T's, not nothing.
        x = self.standard()
        x.axiom("Lean.trustCompiler")
        g = x.const("Lean.trustCompiler")
        x.decl("g", g, g, kind="def")
        t = x.const("T")
        x.inductive("T", "T.mk", x.e("sort", 0), x.app(t, x.const("g")))
        x.decl("UsesT", x.app(t, t), t)
        code, out, _ = self.scan(x, ["UsesT"])
        self.assertEqual(code, 1, out)
        self.assertIn("UsesT rests on ['Lean.trustCompiler']", out)

    def test_a_constant_never_declared_or_a_missing_record_fails(self):
        x = self.standard()
        x.decl("A", x.const("Nowhere"), x.const("propext"))
        code, out, _ = self.scan(x)
        self.assertEqual(code, 1, out)
        self.assertIn("mentioned and never declared: ['Nowhere']", out)
        x = self.standard()
        x.decl("A", x.const("propext"), x.const("propext"))
        code, out, _ = self.scan(x, ["A", "NotCompiled"], index=["A", "Archive.thing"])
        self.assertEqual(code, 1, out)
        self.assertIn("1 trusted records of compiled libraries are not in the export: ['NotCompiled']", out)
        code, out, _ = self.scan(x, ["A"], index=["Archive.thing", "Other.thing"])
        self.assertEqual(code, 0, out)  # a library without modules: counted, not failed
        self.assertIn("from libraries the tree does not compile: mathlib-index 2", out)
        code, out, _ = self.scan(x, ["A", "Both"], index=["Both"])  # listed by a compiled library too: it must be there
        self.assertEqual(code, 1, out)
        self.assertIn("are not in the export: ['Both']", out)

    def test_terms_out_of_order_stop_the_scan(self):
        x = self.standard()
        x.lines.append(json.dumps({"ie": 99, "sort": 0}))
        code, out, _ = self.scan(x)
        self.assertNotEqual(code, 0)
        self.assertIn("out of order", out)


class OneDiffPerRun(unittest.TestCase):
    """_git.file_diff splits one whole-range diff by file; each section must be exactly what the old
    one-call-per-file diff printed, for every kind of change and awkward path."""

    def test_sections_equal_per_file_diffs(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("docs/a b.md", "one\ntwo\n")
        r.write("Tengoku/«1102.4662»/X.lean", "theorem x : True := trivial\n")
        r.write('docs/quote"d.md', "q\n")
        r.write("docs/old.md", "old\n")
        r.write("docs/moved.md", "moved\ncontent\nhere\n")
        r.write("scripts/tool.sh", "echo 1\n")
        (r.dir / "docs/blob.bin").write_bytes(bytes(range(256)))
        r.commit("base files")
        r.git("checkout", "-q", "-B", "pr")
        r.write("docs/a b.md", "one\n2\nthree\n")
        r.write("Tengoku/«1102.4662»/X.lean", "/-\nChanged for Tengoku.\n-/\ntheorem x : True := trivial\n")
        r.write('docs/quote"d.md', "q2\n")
        r.git("rm", "-q", "docs/old.md")
        r.git("mv", "docs/moved.md", "docs/renamed.md")
        (r.dir / "scripts/tool.sh").chmod(0o755)
        (r.dir / "docs/blob.bin").write_bytes(bytes(reversed(range(256))))
        r.write("docs/new.md", "new\n")
        r.commit("change everything")
        code = (
            "import sys, _git\n"
            "paths = [p for _, p in _git.changed_files('main', 'pr')]\n"
            "bad = [p for p in paths if _git.file_diff('main', 'pr', p) != _git.run('diff', '-U0', 'main...pr', '--', p)]\n"
            "print(len(paths), 'paths;', 'mismatch:', bad)\n"
            "sys.exit(1 if bad or len(paths) < 9 else 0)\n"
        )
        p = subprocess.run(
            [sys.executable, "-c", code],
            cwd=CI,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "PYTHONPATH": str(CI)},
        )
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)


class Intake(unittest.TestCase):
    """An intake PR: one library's verified Lean modules (a factory bundle), judged by shape, manifest, lint and provenance."""

    MOD = "import Tengoku\n\nnamespace Fx\n\ntheorem good : 1 + 1 = 2 := rfl\n\nend Fx\n"

    def repo(self):
        r = Repo()
        r.write("lean-toolchain", "leanprover/lean4:v4.34.0-rc2\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\n")
        r.commit("toolchain and All")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def bundle(self, r, mod=None, **over):
        manifest = {
            "name": "Fx.good",
            "statement": "theorem good : 1 + 1 = 2",
            "module": "Tengoku.FxLib.Fx.Basic",
            "source_path": "Fx/Basic.lean",
            "library": "fx-lib",
            "toolchain": "leanprover/lean4:v4.34.0-rc2",
            "via": "equal",
            **over,
        }
        r.write("Tengoku/FxLib/Fx/Basic.lean", mod if mod is not None else self.MOD)
        r.write("Tengoku/FxLib.lean", "import Tengoku.FxLib.Fx.Basic\n")
        r.write("data/intake/fx-lib/manifest.jsonl", json.dumps(manifest) + "\n")
        r.write("data/intake/fx-lib/report.json", "{}\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("intake fx-lib")

    BOT = {"PR_ACTOR": "tengoku-bot", "TENGOKU_BOT": "tengoku-bot"}

    def test_a_bundle_from_the_factory_is_class_intake_and_passes(self):
        r = self.repo()
        self.bundle(r)
        rc, out = r.gate("classify.py", env=self.BOT)
        self.assertEqual(rc, 0, out)
        self.assertIn("class=intake", out)
        rc, out = r.gate("intake_check.py")
        self.assertEqual(rc, 0, out)
        self.assertIn("intake ok: fx-lib: 1 modules, 1 theorems", out)

    def test_only_the_factory_account_may_send_one(self):
        r = self.repo()
        self.bundle(r)
        rc, out = r.gate("classify.py", env={"PR_ACTOR": "someone", "TENGOKU_BOT": "tengoku-bot"})
        self.assertNotEqual(rc, 0)
        self.assertIn("factory's account", out)

    def test_an_intake_pr_is_nothing_but_the_bundle(self):
        r = self.repo()
        self.bundle(r)
        r.write("scripts/x.py", "print(2)\n")
        r.commit("and a script")
        rc, out = r.gate("classify.py", env=self.BOT)
        self.assertNotEqual(rc, 0)
        self.assertIn("nothing else", out)

    def test_code_that_runs_while_compiling_fails_the_lint(self):
        r = self.repo()
        self.bundle(r, mod=self.MOD + '\n#eval IO.println "x"\n')
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("no # commands", out)

    def test_an_import_outside_the_tree_fails(self):
        r = self.repo()
        self.bundle(r, mod="import Mathlib.Data.Nat.Basic\n" + self.MOD)
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("not the tree", out)

    def test_notation_needs_the_proposed_lint(self):
        r = self.repo()
        self.bundle(r, mod=self.MOD + '\nnotation "ℓ" => 1\n')
        self.assertNotEqual(r.gate("intake_check.py")[0], 0)
        rc, out = r.gate("intake_check.py", "main", "pr", "--lint", "proposed")
        self.assertEqual(rc, 0, out)

    def test_the_manifest_must_name_a_module_of_the_pr_and_the_trees_toolchain(self):
        r = self.repo()
        self.bundle(r, module="Tengoku.FxLib.Other")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("not a file of this PR", out)
        r2 = self.repo()
        self.bundle(r2, toolchain="leanprover/lean4:v4.29.1")
        self.assertIn("toolchain", r2.gate("intake_check.py")[1])

    def test_all_lean_may_gain_one_line_only(self):
        r = self.repo()
        self.bundle(r)
        r.write("Tengoku/All.lean", "import Tengoku.FxLib\n")  # drops Lib's line
        r.commit("tamper")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("All.lean", out)

    def test_existing_files_are_never_rewritten(self):
        r = self.repo()
        self.bundle(r)
        r.write("Tengoku/Lib/Basic.lean", "theorem Lib.old : 1 + 1 = 2 := by decide\n")
        r.commit("rewrite an old module")
        rc, out = r.gate("classify.py", env=self.BOT)
        self.assertNotEqual(rc, 0)  # a record library's module is not part of this bundle: multi-purpose

    def test_a_library_already_in_the_tree_is_not_intaken_again(self):
        r = self.repo()  # base has Tengoku/Lib/: every new file under it is status A, a duplicate import line is still one added line
        r.write("Tengoku/Lib/Extra.lean", self.MOD)
        manifest = {
            "name": "Fx.good",
            "statement": "theorem good : 1 + 1 = 2",
            "module": "Tengoku.Lib.Extra",
            "library": "lib",
            "toolchain": "leanprover/lean4:v4.34.0-rc2",
        }
        r.write("data/intake/lib/manifest.jsonl", json.dumps(manifest) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.Lib\n")
        r.commit("add to an existing library")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("already in the tree", out)

    def test_the_archive_member_is_the_blobs_own_bytes(self):
        r = self.repo()
        self.bundle(r)
        (r.dir / "Tengoku/FxLib/Fx/Basic.lean").write_bytes(self.MOD.replace("\n", "\r\n").encode())  # CRLF survives
        r.commit("crlf")
        tar = Path(tempfile.mkdtemp()) / "bundle.tar"
        rc, out = r.gate("intake_check.py", "main", "pr", "--tar", str(tar))
        self.assertEqual(rc, 0, out)
        with tarfile.open(tar) as t:
            self.assertEqual(t.extractfile("Tengoku/FxLib/Fx/Basic.lean").read(), self.MOD.replace("\n", "\r\n").encode())

    def test_a_module_that_is_not_utf8_fails_cleanly(self):
        r = self.repo()
        self.bundle(r)
        (r.dir / "Tengoku/FxLib/Fx/Basic.lean").write_bytes(b"theorem x : True := trivial -- \xff\n")
        r.commit("not utf-8")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("not valid UTF-8", out)

    def test_the_queues_content_lint_follows_the_intake_lint_policy(self):
        r = self.repo()
        self.bundle(r, mod=self.MOD + '\nnotation "ℓ" => 1\n')
        rc, out = r.gate("lint_banked.py")
        self.assertNotEqual(rc, 0)  # strict: a notation command is not allowed anywhere
        self.assertIn("notation", out)
        rc, out = r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": "proposed"})
        self.assertEqual(rc, 0, out)
        # a sibling whose name merely starts like the bundle's root file is not the bundle's
        r.write("Tengoku/FxLib.leanExtra.lean", 'notation "ℓ" => 1\n')
        r.commit("a sibling of the root file")
        rc, out = r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": "proposed"})
        self.assertNotEqual(rc, 0)
        self.assertIn("Tengoku/FxLib.leanExtra.lean", out)
        r.git("reset", "-q", "--hard", "HEAD~1")
        # and only inside the bundle's own modules: a notation in any other module of the tree is still refused
        r.write("Tengoku/Lib/Basic.lean", 'theorem Lib.old : 1 + 1 = 2 := rfl\nnotation "ℓ" => 1\n')
        r.commit("a notation in an older library")
        rc, out = r.gate("lint_banked.py", env={"TENGOKU_INTAKE_LINT": "proposed"})
        self.assertNotEqual(rc, 0)
        self.assertIn("Tengoku/Lib/Basic.lean", out)

    def test_the_reducibility_attributes_are_inert(self):
        r = self.repo()
        self.bundle(r, mod=self.MOD + "\n@[implicit_reducible] def Fx.one : Nat := 1\n")
        rc, out = r.gate("intake_check.py")
        self.assertEqual(rc, 0, out)

    def test_a_manifest_that_is_not_made_of_objects_fails_with_a_message(self):
        r = self.repo()
        self.bundle(r)
        good = json.loads((r.dir / "data/intake/fx-lib/manifest.jsonl").read_text())
        rows = [[1, 2], {**good, "module": 5}, {**good, "name": ["x"]}, "text"]
        (r.dir / "data/intake/fx-lib/manifest.jsonl").write_text("".join(json.dumps(x) + "\n" for x in rows))
        r.commit("odd manifest")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertNotIn("Traceback", out)
        self.assertIn("not a JSON object", out)

    def test_a_tree_command_written_indented_is_still_refused(self):
        r = self.repo()
        self.bundle(r, mod=self.MOD + "\n  theorem_wanted foo : True\n")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("theorem_wanted", out)

    def test_an_import_line_may_carry_a_comment(self):
        r = self.repo()
        self.bundle(r, mod="import Tengoku -- the tree\n" + self.MOD.replace("import Tengoku\n", "", 1))
        rc, out = r.gate("intake_check.py")
        self.assertEqual(rc, 0, out)

    def with_record(self, name):
        """A repository whose base (main) already holds a trusted record of that name, then the bundle's branch."""
        r = self.repo()
        r.write(
            "data/trusted/lib2.jsonl",
            json.dumps({"name": name, "statement": f"theorem {name} : True", "status": "trusted", "library": "lib2"}) + "\n",
        )
        r.commit("a record of the tree")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        return r

    def test_a_bare_name_equal_to_a_records_proves_nothing_but_a_qualified_one_does(self):
        r = self.with_record("good")  # the tree's `good` is a record written inside some namespace
        self.bundle(r, name="good")
        rc, out = r.gate("intake_check.py")
        self.assertEqual(rc, 0, out)
        r2 = self.with_record("Fx.good")
        self.bundle(r2, name="Fx.good")
        rc, out = r2.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("already a trusted record", out)

    def test_staging_records_of_another_library_do_not_block_a_bundle_but_a_merged_bundles_theorem_does(self):
        r = self.repo()
        r.write(
            "data/staging/lib2/20260101T000000Z-000.jsonl",
            json.dumps({"name": "Fx.good", "statement": "theorem Fx.good : True", "status": "staging", "library": "lib2"}) + "\n",
        )
        r.commit("a staged record of another library")
        r.git("checkout", "-q", "main")
        r.git("merge", "-q", "--ff-only", "pr")
        r.git("checkout", "-q", "pr")
        self.bundle(r, name="Fx.good")
        rc, out = r.gate("intake_check.py")
        self.assertEqual(rc, 0, out)
        r2 = self.repo()
        r2.write("data/intake/lib2/manifest.jsonl", json.dumps({"name": "Fx.good", "library": "lib2"}) + "\n")
        r2.commit("a merged bundle")
        r2.git("checkout", "-q", "main")
        r2.git("merge", "-q", "--ff-only", "pr")
        r2.git("checkout", "-q", "pr")
        self.bundle(r2, name="Fx.good")
        rc, out = r2.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("already a trusted record or a bundle theorem", out)

    def test_the_queues_content_lint_reads_an_added_module_without_its_comments(self):
        r = self.repo()
        prose = "/-- Axioms: `#print axioms` confirms it; no `native_decide`, no `#eval`, no `initialize`. -/\n"
        self.bundle(
            r,
            mod=self.MOD.replace("theorem good", prose + "theorem good")
            + "-- run_cmd in a line comment\n/- a block: IO.Process.spawn -/\n",
        )
        rc, out = r.gate("lint_banked.py")
        self.assertEqual(rc, 0, out)
        r2 = self.repo()
        self.bundle(r2, mod=self.MOD + "\n#print axioms Fx.good\n")
        rc, out = r2.gate("lint_banked.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("#print axioms", out)
        r4 = self.repo()  # a line `import X -/` that closes a block comment must not be dropped before the comment is read
        self.bundle(r4, mod=self.MOD + "\n/- a comment\nimport Foo -/\n#eval 1\n")
        rc, out = r4.gate("lint_banked.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("#eval", out)
        r3 = self.repo()
        self.bundle(r3, mod=self.MOD + '\nopen Lean in\nrun_cmd logInfo "x"\n')
        rc, out = r3.gate("lint_banked.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("run_cmd", out)

    def test_an_empty_manifest_is_refused(self):
        r = self.repo()
        self.bundle(r)
        (r.dir / "data/intake/fx-lib/manifest.jsonl").write_text("")
        r.commit("a bundle that claims no theorem")
        rc, out = r.gate("intake_check.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("manifest has no theorem", out)

    def test_the_rebuilt_archive_is_the_factorys_archive(self):
        r = self.repo()
        self.bundle(r)
        tar = Path(tempfile.mkdtemp()) / "bundle.tar"
        rc, out = r.gate("intake_check.py", "main", "pr", "--tar", str(tar))
        self.assertEqual(rc, 0, out)
        # what the factory does (scripts/bump/bundle_tar.py in competemath/emissary-archangel): the bundle directory as one canonical archive
        sys.path.insert(0, str(CI))
        import bundle_tar

        d = Path(tempfile.mkdtemp())
        for rel in ("Tengoku/FxLib/Fx/Basic.lean", "Tengoku/FxLib.lean"):
            (d / rel).parent.mkdir(parents=True, exist_ok=True)
            (d / rel).write_text((r.dir / rel).read_text())
        (d / "manifest.jsonl").write_text((r.dir / "data/intake/fx-lib/manifest.jsonl").read_text())
        (d / "report.json").write_text((r.dir / "data/intake/fx-lib/report.json").read_text())
        out2 = Path(tempfile.mkdtemp()) / "factory.tar"
        bundle_tar.write_tar(bundle_tar.read_dir(str(d)), str(out2))
        self.assertEqual(tar.read_bytes(), out2.read_bytes())

    def test_the_archive_is_only_written_inside_the_working_or_a_temporary_directory(self):
        sys.path.insert(0, str(CI))
        import bundle_tar

        tmp = Path(tempfile.mkdtemp())
        self.assertTrue(bundle_tar.write_tar({"a.txt": b"x"}, str(tmp / "ok.tar")))
        for bad in (str(tmp / ".." / ".." / ".." / ".." / "etc" / "x.tar"), "/etc/x.tar", str(Path.home() / "x.tar")):
            with self.assertRaises(ValueError):
                bundle_tar.write_tar({"a.txt": b"x"}, bad)
        link = tmp / "link"
        link.symlink_to("/etc")
        with self.assertRaises(ValueError):  # a symlink out of the temporary directory
            bundle_tar.write_tar({"a.txt": b"x"}, str(link / "x.tar"))

    def test_the_archive_is_the_same_bytes_on_every_machine(self):
        sys.path.insert(0, str(CI))
        import bundle_tar

        out = Path(tempfile.mkdtemp()) / "g.tar"
        # the same vector, the same digest, in competemath/emissary-archangel's tests: the two copies of the function must not drift
        self.assertEqual(
            bundle_tar.write_tar({"a.txt": b"hello\n", "dir/b.lean": b"theorem x : True := trivial\n"}, str(out)),
            "69860ced3534fa1c7d35bcaf779a68ea88028baf4f447748b381fab33d64e100",  # pragma: allowlist secret (a digest, not a secret)
        )


class RecordNameTypes(unittest.TestCase):
    """A tombstone, a tombstone_note or a credit_correction names a record: a list or a number there is an error with a message, never a traceback
    (found by the records fuzz target: `{"tombstone_note": [...]}` raised TypeError: unhashable type)."""

    def test_a_name_that_is_not_a_string_fails_with_a_message(self):
        extra = {
            "category": "duplicate",
            "reason": "r",
            "at": "2026-01-01",
            "note": "n",
            "see": ["Lib.old"],
            "by": "b",
            "credit": "Authors: x",
            "evidence": "https://example.org",
        }
        for key in ("tombstone", "tombstone_note", "credit_correction"):
            for value in (["Lib.old"], 5, {"a": 1}):
                r = Repo()
                r.append("data/trusted/lib.jsonl", json.dumps({key: value, **extra}) + "\n")
                r.commit("a record name that is not a string")
                rc, out = r.gate("validate_records.py")
                self.assertNotEqual(rc, 0, (key, value, out))
                self.assertNotIn("Traceback", out, (key, value))
                self.assertIn("is the name of a record", out, (key, value))


class QueuePlacement(unittest.TestCase):
    """queue_targets.py fails a group whose records land in no module the queue compiles."""

    def setUp(self):
        sys.path.insert(0, str(CI))

    def test_unplaced(self):
        from _git import unplaced

        mod = "namespace EquationalTheories\ntheorem Selftest.queueAxioms : (3 : Nat) + 4 = 7 := rfl\nend EquationalTheories\n"
        self.assertEqual(unplaced({"Selftest.queueAxioms"}, [mod]), [])  # inside a library namespace
        self.assertEqual(
            unplaced({"Selftest.queueAxiomsX", "queueAxioms.Selftest"}, [mod]), ["Selftest.queueAxiomsX", "queueAxioms.Selftest"]
        )
        self.assertEqual(unplaced({"Selftest.queueAxioms"}, []), ["Selftest.queueAxioms"])
        other = "namespace Other\n@[simp] private theorem foo : True := trivial\nend Other\n"
        self.assertEqual(unplaced({"Lib.foo"}, [other]), ["Lib.foo"])  # declares Other.foo, not Lib.foo
        self.assertEqual(unplaced({"Other.foo"}, [other]), [])
        self.assertEqual(unplaced({"x"}, ["namespace A\ntheorem _root_.x : True := trivial\nend A\n"]), [])
        self.assertEqual(unplaced({"A.s"}, ["namespace A\nsection B\ntheorem s : True := trivial\nend B\nend A\n"]), [])
        mutual = (
            "namespace A\nmutual\ntheorem m1 : True := trivial\ntheorem m2 : True := trivial\nend\ntheorem after : True := trivial\nend A\n"
        )
        self.assertEqual(unplaced({"A.m1", "A.m2", "A.after"}, [mutual]), [])  # `end` of mutual keeps namespace A open
        ncs = "namespace A\nnoncomputable section\ntheorem n : True := trivial\nend\ntheorem after2 : True := trivial\nend A\n"
        self.assertEqual(unplaced({"A.n", "A.after2"}, [ncs]), [])

    def test_a_garbled_record_is_left_out_like_the_generator_does(self):
        from _git import garbled

        self.assertTrue(garbled({"statement": "theorem t : 1 \ufffd 2"}))
        self.assertTrue(garbled({"statement": "theorem t : True", "context": "a \ufffd b"}))
        self.assertFalse(garbled({"statement": "theorem t : 1 ≤ 2", "proof": ":= by decide"}))

    def test_an_annotation_cannot_start_another_workflow_command(self):
        from _git import annotation

        self.assertEqual(annotation("a\n::add-mask::x\r%"), "a%0A::add-mask::x%0D%25")
        self.assertNotIn("\n", annotation("Lib.x\n::stop-commands::t"))

    def test_the_log_form_of_a_failure_cannot_start_a_workflow_command(self):
        from _git import plain

        out = plain("in no module: Lib.x\n::add-mask::secret\r\n  ::stop-commands::t")
        self.assertNotIn("\n::", out)
        self.assertNotRegex(out, r"(?m)^\s*::")
        self.assertIn("in no module: Lib.x\n", out)  # still readable, line breaks kept

    def test_comments_and_strings_hide_nothing_and_declare_nothing(self):
        from _git import unplaced

        text = (
            "-- theorem missing : True := trivial\n/- theorem hidden /- nested -/ : True -/\n/-- about `shown` -/\n"
            'def s : String := "theorem instring : True /- not a comment"\n'
            "theorem after : True := trivial\n"
            "def c : Char := '\"'\ntheorem afterChar : True := trivial\n"
        )
        self.assertEqual(
            unplaced({"missing", "hidden", "shown", "instring", "after", "afterChar"}, [text]), ["hidden", "instring", "missing", "shown"]
        )

    def test_lexer(self):
        from lean_lex import code_only

        self.assertEqual(code_only("a -- x\nb"), "a \nb")
        self.assertEqual(code_only("a /- x /- y -/ z -/ b"), "a  b")
        self.assertEqual(code_only('s!"x -- y" z'), 's!"' + " " * len("x -- y") + '" z')
        self.assertEqual(code_only("f x' y'' '\\n' q"), "f x' y'' ' ' q")  # primes are identifiers; '\n' is a char
        self.assertEqual(code_only('r#"a " -- b"# c'), 'r#"' + " " * len('a " -- b') + '"# c')
        self.assertEqual(code_only('s!"a {x + 1} b"'), 's!"  {x + 1}  "')  # holes are code, literal text is blank
        self.assertEqual(code_only("theorem «a -- b /- c» : True"), "theorem «a -- b /- c» : True")  # escaped names are names
        self.assertEqual(code_only('s!"{«}»} x"'), 's!"{«}»}  "')  # a brace inside an escaped name does not close the hole
        self.assertEqual(code_only('def «x"y» := 1 -- z'), 'def «x"y» := 1 ')
        for src in ("a -- x\nb", "x /- y\nz -/ w", 's!"p\nq" r', "c '\\n' d", 'r#"u\nv"# t'):
            self.assertEqual(code_only(src).count("\n"), src.count("\n"), src)  # line breaks survive: line checks stay aligned


class Sbom(unittest.TestCase):
    """scripts/sbom.py lists the toolchain, the seed and the libraries whose records the tree holds, from the commit."""

    def test_bill(self):
        with tempfile.TemporaryDirectory() as d:
            run = lambda *a: subprocess.run(["git", *a], cwd=d, check=True, capture_output=True, text=True).stdout  # noqa: E731
            run("init", "-q", "-b", "main")
            run("config", "user.email", "t@t")
            run("config", "user.name", "t")
            root = Path(d)
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
            (root / "SEED.md").write_text(
                "| package | origin | rev | mapped to |\n|---|---|---|---|\n| mathlib | https://github.com/leanprover-community/mathlib4.git | "
                + "a" * 40
                + " | `Tengoku` |\n| Cli | https://github.com/leanprover/lean4-cli | "
                + "b" * 40
                + " | `Tengoku.Meta.Cli` |\n"
            )
            (root / "LICENSE-THIRD-PARTY.md").write_text(
                "| Package | Upstream | Licence | Folded into |\n|---|---|---|---|\n"
                "| Mathlib | [x](https://github.com/leanprover-community/mathlib4) | Apache-2.0 | `Tengoku/` |\n"
                "| lean4-cli | [x](https://github.com/leanprover/lean4-cli) | MIT | `Tengoku/Meta/Cli/` |\n"
            )
            (root / "schemas").mkdir()
            (root / "schemas/sources.json").write_text(
                json.dumps(
                    {
                        "licences": {
                            "https://github.com/teorth/equational_theories": "Apache-2.0",
                            "https://competemath.com/": "Apache-2.0",
                        },
                        "corpora": {"equational-theories": {"repo": "https://github.com/teorth/equational_theories", "commit": "c" * 40}},
                    }
                )
            )
            (root / "data/trusted").mkdir(parents=True)
            (root / "data/trusted/equational-theories.jsonl").write_text(
                '{"name": "A"}\n{"name": "B", "note": "tombstone"}\n{"tombstone": "A"}\n'
            )
            (root / "data/trusted/competemath.jsonl").write_text(
                '{"name": "P", "source_url": "https://competemath.com/practice/problems/1"}\n'
            )
            (root / "data/trusted/mathlib-algebra.jsonl").write_text('{"name": "M"}\n')
            run("add", "-A")
            run("commit", "-qm", "tree")
            out = subprocess.run(
                [sys.executable, str(TREE / "scripts/sbom.py"), "--commit", "HEAD", "--version", "v0.0.1"],
                cwd=d,
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            bom = json.loads(out)
            self.assertEqual(
                (bom["bomFormat"], bom["specVersion"], bom["metadata"]["component"]["version"]), ("CycloneDX", "1.5", "v0.0.1")
            )
            by = {c["name"]: c for c in bom["components"]}
            self.assertEqual(set(by), {"lean4", "mathlib", "Cli", "equational-theories", "competemath"})  # mathlib-* is seed metadata
            self.assertEqual(by["Cli"]["licenses"][0]["license"]["id"], "MIT")
            self.assertEqual(by["mathlib"]["purl"], "pkg:github/leanprover-community/mathlib4@" + "a" * 40)
            self.assertEqual(by["equational-theories"]["version"], "c" * 40)
            records = {p["name"]: p["value"] for p in by["equational-theories"]["properties"]}
            self.assertEqual(
                records["tengoku:trusted-records"], "1"
            )  # a tombstone is not a record, and the record it retracts is not counted
            self.assertEqual(by["competemath"]["licenses"][0]["license"]["id"], "Apache-2.0")


class AllowList(unittest.TestCase):
    """A compiled record passes only if everything in it is known to be inert (scripts/ci/allowlist.py)."""

    CASES = {
        "card notation": ("theorem t (s : Finset ℕ) : #s ≤ #s + 1 := by omega", False),
        "array literal": ("def a : Array ℕ := #[1, 2]", False),
        "pattern continuation": ("def f : ℕ → ℕ\n| 0 => 1\n| n+1 => n", False),
        "words in comments": ("/- theorem x #eval -/\ntheorem t : True := trivial -- elab macro", False),
        "words in strings": ('def s : String := "import #eval elab"', False),
        "simp down": ("@[simp↓] theorem t : True := trivial", False),
        "simps bang": ("@[simps!] def f : ℕ := 1", False),
        "aesop lemma": ("@[aesop safe apply] theorem t : True := trivial", False),
        "noncomputable section": ("noncomputable section\ntheorem t : True := trivial\nend", False),
        "open in": ("open Nat in\ntheorem t : True := trivial", False),
        "#eval indented": ("theorem t : True := trivial\n  #eval 1", True),
        "#check": ("#check Nat", True),
        "unknown # command": ("#my_cmd x", True),
        "csimp": ("@[csimp] theorem t : True := trivial", True),
        "attribute extern": ('attribute [extern "x"] foo', True),
        "attribute implemented_by": ("attribute [implemented_by g] f", True),
        "decorated initialize": ("@[simp] initialize foo : Unit ← pure ()", True),
        "by_elab": ("theorem t : True := by_elab pure ()", True),
        "aesop tactic rule": ("@[aesop safe tactic] def t : Lean.Elab.Tactic.TacticM Unit := pure ()", True),
        "unknown attribute": ("@[equational_result] theorem t : True := trivial", True),
        "IO": ('def f : IO Unit := IO.println "x"', True),
        "import": ("import Mathlib\ntheorem t : True := trivial", True),
        "macro": ('macro "x" : term => `(1)', True),
        "english at column 0": ("theorem t : True := trivial\nthe rest of a broken docstring -/", True),
        "aesop unsafe rule": ("theorem t : True := by\n  aesop (add unsafe ModEq.mul)", False),
        "simps projections": ("initialize_simps_projections Foo (toFun → apply)", False),
        "where at column 0": ("def f : ℕ := g\nwhere\n  g : ℕ := 1", False),
        "unsafe def": ("unsafe def f : ℕ := 1", True),
        "private partial def": ("private partial def f : ℕ → ℕ := fun n => n", True),
        "native_decide tactic": ("theorem t : 2 + 2 = 4 := by native_decide", True),
        "native_decide axiom term": ("theorem t : True\n:= Collision._native.native_decide.ax_12_extra", True),
        "ofReduceBool": ("theorem t : True := Lean.ofReduceBool _ _ rfl", True),
        "run_meta indented": ("theorem t : True := trivial\n  run_meta pure ()", True),
        "eval% term": ("theorem t : (eval% 2 + 2) = 4 := rfl", True),
        "eval% in an interpolation hole": ('def s : String := s!"{eval% 2 + 2}"', True),
        "IO in an interpolation hole": ('def s : String := m!"x {IO.println 1} y"', True),
        "interpolation with a plain hole": ('def s (n : ℕ) : String := s!"n = {n} and {"in {eval% 1}"}"', False),
        "braces in a plain string": ('def s : String := "{eval% 1}"', False),
        "hole closed by a char literal brace": ("def s : String := s!\"{('}', eval% 1).2}\"", True),
        "hole with a block comment brace": ('def s : String := s!"{ /- } -/ eval% 1 }"', True),
        "hole with a nested interpolation": ('def s : String := s!"{s!"{eval% 1}"}"', True),
        "eval% in a raw-string interpolation hole": ('def s : String := s!"{r#"a"}"b"# ++ toString (eval% 1)}"', True),
    }

    def test_cases(self):
        sys.path.insert(0, str(CI))
        from allowlist import violations

        allowed = set(json.loads((TREE / "schemas/allowed-options.json").read_text())["allowed"])
        for name, (text, rejected) in self.CASES.items():
            with self.subTest(name):
                self.assertEqual(bool(violations(text, allowed)), rejected, violations(text, allowed))
