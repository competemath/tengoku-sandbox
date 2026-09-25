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
        r.append("data/staging/lib.jsonl", json.dumps({**GOOD, "name": "Lib.new", "statement": "theorem Lib.new : 1 + 1 = 2"}) + "\n")
        r.commit("add")
        for s in ["classify.py", "append_only.py", "credits.py", "validate_records.py", "lint_banked.py", "dco.py"]:
            rc, out = r.gate(s)
            self.assertEqual(rc, 0, f"{s}: {out}")
        self.assertIn("class=content", r.gate("classify.py")[1])

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
            env={**os.environ, "TENGOKU_CI_ROOT": str(r.dir), "TENGOKU_COMMENT_DRY": "1"},
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


class DeregisteredSource(unittest.TestCase):
    """A source taken off the allowlist takes its tentative/staging data with it; nothing else may be deleted."""

    GONE = {**GOOD, "name": "Gone.thm", "library": "gone", "status": "tentative", "source_url": "https://github.com/example/gone/blob/x/G.lean#L1"}

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

