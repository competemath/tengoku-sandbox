"""The gates, tested against synthetic repositories: every rule has a case that must fail and one that must pass."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
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
            json.dumps({**GOOD, "name": "Lib.old", "status": "trusted", "promoted_at": "2026-01-01T00:00:00Z"}) + "\n",
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
        (self.dir / p).write_text(s)

    def append(self, p, s):
        with (self.dir / p).open("a") as f:
            f.write(s)

    def commit(self, msg, signoff=True):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg + ("\n\nSigned-off-by: t <t@t>" if signoff else ""))

    def gate(self, script, *args):
        r = subprocess.run(
            [sys.executable, str(CI / script), *(args or ("main", "pr"))],
            cwd=self.dir,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_CI_ROOT": str(self.dir)},
        )
        return r.returncode, (r.stdout + r.stderr)


class Gates(unittest.TestCase):
    def test_clean_append_passes_everything(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new"}) + "\n")
        r.commit("add")
        for s in ["classify.py", "append_only.py", "credits.py", "validate_records.py", "lint_banked.py", "dco.py"]:
            rc, out = r.gate(s)
            self.assertEqual(rc, 0, f"{s}: {out}")
        self.assertIn("class=content", r.gate("classify.py")[1])

    def test_multi_purpose_fails_classify(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new"}) + "\n")
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
        r.append("data/trusted/lib.jsonl", json.dumps({"tombstone": "Lib.old", "reason": "wrong", "by": "t", "at": "2026-09-15"}) + "\n")
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
            json.dumps({**GOOD, "name": "Lib.a", "status": "trusted"}),
            json.dumps({**GOOD, "name": "Lib.b", "source_url": "https://evil.example/x"}),
            json.dumps({**GOOD, "name": "Lib.old"}),
            "{not json",
            json.dumps({**GOOD, "name": "Lib.c", "library": "other"}),
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
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new"}) + "\n")
        r.commit("unsigned", signoff=False)
        rc, out = r.gate("dco.py")
        self.assertEqual(rc, 1)
        self.assertIn("Signed-off-by", out)

    def test_sorry_scan_is_advisory(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.s", "proof": ":= by sorry"}) + "\n")
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


if __name__ == "__main__":
    unittest.main()
