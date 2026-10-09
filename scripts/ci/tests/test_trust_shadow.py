"""trust_shadow.py, trust_ledger.py, canary_gate.py and the vendored evidence contract (docs/trust-shadow.md). No network, no Lean."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))

import canary_gate  # noqa: E402
import trust_ledger  # noqa: E402
import trust_shadow as ts  # noqa: E402
from trust_vendor.juridicator_evidence import validate  # noqa: E402

HEAD = "a" * 40
BASE = "b" * 40
CASE = ts.case_dict("competemath/tengoku-sandbox", HEAD, "tooling", "someone")
CONTENT = ts.case_dict("competemath/tengoku-sandbox", HEAD, "content", "someone")


def run_of(name, conclusion="success", status="completed", id_=7):
    return {"name": name, "conclusion": conclusion, "status": status, "id": id_, "html_url": "https://github.com/x/y/runs/7"}


class Vendored(unittest.TestCase):
    def test_the_contract_copy_matches_its_pin(self):
        pin = (CI / "trust_vendor" / "EVIDENCE.sha256").read_text(encoding="utf-8").split()[0]
        got = hashlib.sha256((CI / "trust_vendor" / "juridicator_evidence.py").read_bytes()).hexdigest()
        self.assertEqual(got, pin, "trust_vendor/juridicator_evidence.py was edited: refresh it from tengoku-juridicator, never by hand")


class Records(unittest.TestCase):
    def test_everything_gathered_validates(self):
        recs = [
            ts.manifest(CASE, "2026-10-09T00:00:00Z"),
            ts.lint_record(CASE, BASE, HEAD, 0, "content lint OK", "2026-10-09T00:00:00Z"),
            ts.lint_record(
                CASE, BASE, HEAD, 1, "::error::banked content lint:\n  data/x.jsonl:3 (Foo): `axiom` is not allowed", "2026-10-09T00:00:00Z"
            ),
            ts.sorry_record(CONTENT, BASE, HEAD, 0, "no sorry/admit in added content", "2026-10-09T00:00:00Z"),
            ts.sorry_record(CONTENT, BASE, HEAD, 0, "### sorry / admit in this PR\n\n- a.lean:3\n- b.lean:4", "2026-10-09T00:00:00Z"),
        ]
        recs += ts.check_records(CASE, [run_of("pr-gate"), run_of("sonar", "failure")], "2026-10-09T00:00:00Z")
        for r in recs:
            self.assertEqual(validate(r), [], r["kind"])
        self.assertEqual([r["outcome"] for r in recs[1:5]], ["pass", "fail", "pass", "fail"])
        self.assertEqual(recs[4]["details"]["occurrences"], 2)

    def test_a_tool_error_is_inconclusive_never_a_failure_of_the_pr(self):
        crashed = ts.lint_record(CASE, BASE, HEAD, 128, "fatal: bad object", "2026-10-09T00:00:00Z")
        self.assertEqual(crashed["outcome"], "inconclusive")
        refused = ts.lint_record(CASE, BASE, HEAD, 1, "::error::banked content lint:\n  x", "2026-10-09T00:00:00Z")
        self.assertEqual(refused["outcome"], "fail")
        self.assertEqual(ts.sorry_record(CONTENT, BASE, HEAD, 1, "Traceback", "2026-10-09T00:00:00Z")["outcome"], "inconclusive")
        self.assertEqual(ts.sorry_record(CONTENT, BASE, HEAD, 0, "garbage", "2026-10-09T00:00:00Z")["outcome"], "inconclusive")

    def test_sorry_blocks_only_content_prs_and_is_noted_for_the_rest(self):
        out = "### sorry / admit in this PR\n\n- tools/x.lean:3\n- tools/y.lean:9"
        tooling = ts.sorry_record(CASE, BASE, HEAD, 0, out, "2026-10-09T00:00:00Z")
        self.assertEqual((tooling["kind"], tooling["verifiability"]), ("attested.sorry_noted", "attested"))
        self.assertEqual(ts.sorry_record(CONTENT, BASE, HEAD, 0, out, "2026-10-09T00:00:00Z")["kind"], "mechanical.no_sorry")
        self.assertEqual({e["kind"] for e in ts.manifest(CASE, "2026-10-09T00:00:00Z")["details"]["expected"]}, {"mechanical.content_lint"})
        self.assertIn("mechanical.no_sorry", {e["kind"] for e in ts.manifest(CONTENT, "2026-10-09T00:00:00Z")["details"]["expected"]})

    def test_manifest_lists_what_will_be_reported_by_subject(self):
        m = ts.manifest(CONTENT, "2026-10-09T00:00:00Z")
        self.assertEqual({e["kind"] for e in m["details"]["expected"]}, {"mechanical.content_lint", "mechanical.no_sorry"})
        self.assertEqual(m["producer"]["identity"], ts.STATIC["identity"])

    def test_required_checks_are_mechanical_and_the_rest_are_noted_not_weighed(self):
        recs = ts.check_records(CASE, [run_of("pr-gate"), run_of("fossa"), run_of("sonar", "failure")], "2026-10-09T00:00:00Z")
        kinds = sorted((r["kind"], r["outcome"]) for r in recs)
        self.assertEqual(kinds, [("attested.ci_advisory", "fail"), ("attested.ci_advisory", "pass"), ("mechanical.ci", "pass")])
        self.assertTrue(all(r["reproduce"]["command"].startswith("gh run view") for r in recs if r["kind"] == "mechanical.ci"))

    def test_skipped_running_cancelled_and_our_own_checks(self):
        runs = [
            run_of("pr-gate", "skipped"),
            run_of("a", None, "in_progress"),
            run_of("trust-shadow"),
            run_of("b", "neutral"),
            run_of("pr-gate", "cancelled"),
            {"name": 5},
            run_of("c", "timed_out"),
        ]
        recs = ts.check_records(CASE, runs, "2026-10-09T00:00:00Z")
        self.assertEqual(
            sorted((r["kind"], r["outcome"]) for r in recs), [("attested.ci_advisory", "fail"), ("mechanical.ci", "inconclusive")]
        )

    def test_a_rerun_replaces_the_earlier_run_of_the_same_check(self):
        failed_then_passed = [
            dict(run_of("pr-gate", "failure", id_=1), completed_at="2026-10-01T00:00:00Z"),
            dict(run_of("pr-gate", "success", id_=2), completed_at="2026-10-02T00:00:00Z"),
        ]
        (rec,) = ts.check_records(CASE, failed_then_passed, "2026-10-09T00:00:00Z")
        self.assertEqual(rec["outcome"], "pass")
        passed_then_failed = [dict(failed_then_passed[1]), dict(failed_then_passed[0], completed_at="2026-10-03T00:00:00Z")]
        (rec,) = ts.check_records(CASE, passed_then_failed, "2026-10-09T00:00:00Z")
        self.assertEqual(rec["outcome"], "fail")
        skipped_later = failed_then_passed + [dict(run_of("pr-gate", "skipped", id_=3), completed_at="2026-10-04T00:00:00Z")]
        self.assertEqual(ts.check_records(CASE, skipped_later, "2026-10-09T00:00:00Z"), [])

    def test_class_mapping_and_bad_input(self):
        self.assertEqual(ts.statute_class("class=content (3 files)"), "content")
        self.assertEqual(ts.statute_class("class=intake (9 files)"), "content")
        self.assertEqual(ts.statute_class("class=scope-fix (1 modules)"), "tooling")
        self.assertEqual(ts.statute_class("class=mystery"), "other")
        self.assertEqual(ts.statute_class("nothing"), "other")
        with self.assertRaises(ValueError):
            ts.case_dict("r", "nothex", "tooling", "me")
        with self.assertRaises(ValueError):
            ts.case_dict("r", HEAD, "tooling", "me; rm -rf /")
        self.assertEqual(ts.case_dict("r", HEAD, "tooling", "dependabot[bot]")["author"]["identity"], "dependabot[bot]")
        self.assertEqual(ts.case_dict("r", HEAD, "tooling", "app/dependabot")["author"]["identity"], "app/dependabot")


class Gather(unittest.TestCase):
    def test_gather_writes_a_case_and_valid_evidence_manifest_first(self):
        from unittest import mock

        def fake_run(args, cwd, env=None):
            name = Path(args[1]).name
            return {
                "classify.py": (0, "class=content (2 files)\n"),
                "lint_banked.py": (0, "content lint OK\n"),
                "sorry_scan.py": (0, "no sorry/admit in added content\n"),
            }[name]

        with tempfile.TemporaryDirectory() as d:
            checks = Path(d) / "checks.json"
            checks.write_text(json.dumps([run_of("pr-gate"), run_of("fossa")]), encoding="utf-8")
            with mock.patch.object(ts, "run", fake_run):
                code = ts.main(
                    [
                        "gather",
                        "--repo",
                        "o/r",
                        "--base",
                        BASE,
                        "--head",
                        HEAD,
                        "--author",
                        "me",
                        "--out",
                        str(Path(d) / "o"),
                        "--checks",
                        str(checks),
                    ]
                )
            self.assertEqual(code, 0)
            case = json.loads((Path(d) / "o" / "case.json").read_text(encoding="utf-8"))
            self.assertEqual((case["class"], case["author"]["identity"]), ("content", "me"))
            files = sorted((Path(d) / "o" / "evidence").iterdir())
            recs = [json.loads(f.read_text(encoding="utf-8")) for f in files]
            self.assertEqual(recs[0]["kind"], "manifest.declared")
            self.assertEqual(
                [r["kind"] for r in recs[1:]], ["mechanical.content_lint", "mechanical.no_sorry", "attested.ci_advisory", "mechanical.ci"]
            )
            self.assertTrue(all(validate(r) == [] for r in recs))

    def test_bad_commits_are_refused_with_exit_2(self):
        self.assertEqual(
            ts.main(["gather", "--repo", "o/r", "--base", "x", "--head", HEAD, "--author", "me", "--out", "/nonexistent-dir-x"]), 2
        )


class Ledger(unittest.TestCase):
    def verdict(self, decision="ACCEPT"):
        return {"schema": "tengoku-verdict/1", "decision": decision, "case": {"head_sha": HEAD}}

    def test_only_a_real_verdict_is_accepted(self):
        trust_ledger.validate_verdict(self.verdict())
        for bad in (
            None,
            [],
            {"schema": "other"},
            dict(self.verdict(), decision="MAYBE"),
            dict(self.verdict(), case={"head_sha": "x"}),
            dict(self.verdict(), pad="x" * 70000),
        ):
            with self.assertRaises(ValueError):
                trust_ledger.validate_verdict(bad)

    def test_chain_is_checked_before_every_append(self):
        tools = os.environ.get("TRUST_TOOLS")
        if not tools or not (Path(tools) / "tengoku-juridicator" / "juridicator" / "ledger.py").is_file():
            self.skipTest("no tengoku-juridicator checkout in $TRUST_TOOLS")
        text = trust_ledger.append_entry("", "verdict", self.verdict())
        text = trust_ledger.append_entry(text, "label", {"repo": "r", "head_sha": HEAD, "label": "accept", "by": "me"})
        self.assertEqual(len(text.splitlines()), 2)
        broken = text.replace("ACCEPT", "REJECT", 1)
        with self.assertRaises(ValueError):
            trust_ledger.append_entry(broken, "verdict", self.verdict())


MERGE_BASE = "c" * 40
DIGEST = "sha256:" + "1" * 64
POLICY = "sha256:" + "2" * 64
SHIM = """#!{python}
import json, os, sys
a = sys.argv[1:]
d = os.environ["SHIM_DIR"]
if "POST" in a:
    body = json.load(sys.stdin)
    json.dump(body, open(os.path.join(d, "posted.json"), "w"))
    sys.exit(int(os.environ.get("SHIM_POST_RC", "0")))
posted = json.load(open(os.path.join(d, "posted.json")))
posted.update(id=5, app={{"id": int(os.environ["SHIM_APP_ID"])}})
posted["head_sha"] = os.environ.get("SHIM_HEAD", posted["head_sha"])
print(json.dumps({{"total_count": 1, "check_runs": [posted]}}))
print(json.dumps({{"total_count": 1, "check_runs": []}}))
"""


class Eligibility(unittest.TestCase):
    """The third job of trust-shadow.yml: the `merge eligibility` check run, built from the validated verdict and read back through verify_check."""

    def verdict(self, decision="ACCEPT", **kw):
        return {
            "schema": "tengoku-verdict/1",
            "decision": decision,
            "case": {"head_sha": HEAD},
            "evidence_digest": DIGEST,
            "policy_sha256": POLICY,
            **kw,
        }

    def artifact(self, **kw):
        d = Path(tempfile.mkdtemp())
        (d / "verdict.json").write_text(json.dumps(kw.get("verdict", self.verdict())))
        (d / "case.json").write_text(json.dumps(kw.get("case", {"repo": "o/r", "head_sha": HEAD, "class": "tooling"})))
        (d / "meta.json").write_text(json.dumps(kw.get("meta", {"pr": 7, "base": BASE, "merge_base": MERGE_BASE})))
        return d

    def run_main(self, d, app_id="15368", shim_app="15368", post_rc="0", head=None):
        shim_dir = Path(tempfile.mkdtemp())
        shim = shim_dir / "gh"
        shim.write_text(SHIM.format(python=sys.executable))
        shim.chmod(0o755)
        env = {
            **os.environ,
            "PATH": f"{shim_dir}{os.pathsep}{os.environ['PATH']}",
            "SHIM_DIR": str(shim_dir),
            "SHIM_APP_ID": shim_app,
            "SHIM_POST_RC": post_rc,
        }
        if head:
            env["SHIM_HEAD"] = head
        done = subprocess.run(
            [sys.executable, str(CI / "trust_shadow.py"), "eligibility", "--dir", str(d), "--repo", "o/r", "--app-id", app_id],
            capture_output=True,
            text=True,
            env=env,
        )
        posted = shim_dir / "posted.json"
        return done, json.loads(posted.read_text()) if posted.exists() else None

    def test_the_conclusion_follows_the_verdict_and_the_check_binds_what_it_was_reached_on(self):
        for decision, conclusion in (("ACCEPT", "success"), ("HOLD", "neutral"), ("ESCALATE", "neutral"), ("REJECT", "failure")):
            done, posted = self.run_main(self.artifact(verdict=self.verdict(decision)))
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual((posted["name"], posted["head_sha"], posted["conclusion"]), ("merge eligibility", HEAD, conclusion))
            bound = json.loads(posted["external_id"])
            self.assertEqual(
                (bound["pr"], bound["head_sha"], bound["merge_base"], bound["evidence_digest"], bound["policy_sha256"]),
                (7, HEAD, MERGE_BASE, DIGEST, POLICY),
            )
        self.assertIn('"decision": "admit"', self.run_main(self.artifact())[0].stdout)
        self.assertIn('"decision": "cancel"', self.run_main(self.artifact(verdict=self.verdict("REJECT")))[0].stdout)

    def test_nothing_from_the_verdicts_free_text_reaches_the_check(self):
        done, posted = self.run_main(
            self.artifact(verdict=self.verdict(summary="@everyone <script>alert(1)</script> [x](http://evil)", reasons=["see @someone"]))
        )
        self.assertEqual(done.returncode, 0)
        self.assertNotIn("everyone", json.dumps(posted))
        self.assertNotIn("evil", json.dumps(posted))

    def test_a_check_that_is_not_read_back_as_the_expected_app_fails_the_job(self):
        done, _ = self.run_main(self.artifact(), app_id="424242")  # the Actions identity made it; the pin says another App should have
        self.assertEqual(done.returncode, 1)
        self.assertIn("not read back as app 424242", done.stderr)

    def test_a_check_for_another_head_is_not_an_eligibility(self):
        done, _ = self.run_main(self.artifact(), head="d" * 40)
        self.assertEqual(done.returncode, 1)

    def test_a_check_run_that_could_not_be_created_fails_the_job(self):
        done, _ = self.run_main(self.artifact(), post_rc="1")
        self.assertEqual(done.returncode, 1)
        self.assertIn("was not created", done.stderr)

    def test_the_artifact_is_validated_again_here(self):
        bad = [
            dict(verdict=self.verdict("APPROVED")),
            dict(verdict=self.verdict(evidence_digest="sha256:abc")),
            dict(verdict={**self.verdict(), "case": {"head_sha": "e" * 40}}),
            dict(case={"repo": "other/repo", "head_sha": HEAD}),
            dict(case={"repo": "o/r", "head_sha": "main"}),
            dict(meta={"pr": 0, "base": BASE, "merge_base": MERGE_BASE}),
            dict(meta={"pr": True, "base": BASE, "merge_base": MERGE_BASE}),
            dict(meta={"pr": 7, "base": BASE, "merge_base": "main"}),
            dict(meta={"pr": 7, "base": BASE}),
        ]
        for kw in bad:
            done, posted = self.run_main(self.artifact(**kw))
            self.assertEqual(done.returncode, 2, kw)
            self.assertIsNone(posted, kw)

    def test_a_missing_meta_file_publishes_nothing(self):
        d = self.artifact()
        (d / "meta.json").unlink()
        done, posted = self.run_main(d)
        self.assertEqual(done.returncode, 2)
        self.assertIsNone(posted)

    def test_check_runs_are_read_from_every_page(self):
        text = json.dumps({"check_runs": [{"id": 1}]}) + "\n" + json.dumps({"check_runs": [{"id": 2}, {"id": 3}]})
        self.assertEqual([c["id"] for c in ts.parse_pages(text)], [1, 2, 3])
        self.assertEqual(ts.parse_pages(""), [])

    def test_gather_binds_the_merge_base_when_it_is_given_the_pr(self):
        from unittest import mock

        def fake_run(args, cwd, env=None):
            name = Path(args[1]).name
            return {
                "classify.py": (0, "class=docs (1 files)\n"),
                "lint_banked.py": (0, "ok\n"),
                "sorry_scan.py": (0, "no sorry/admit in added content\n"),
                "merge-base": (0, MERGE_BASE + "\n"),
            }[name]

        with tempfile.TemporaryDirectory() as d:
            with mock.patch.object(ts, "run", fake_run):
                self.assertEqual(
                    ts.main(["gather", "--repo", "o/r", "--pr", "9", "--base", BASE, "--head", HEAD, "--author", "me", "--out", d]), 0
                )
            self.assertEqual(json.loads((Path(d) / "meta.json").read_text()), {"pr": 9, "base": BASE, "merge_base": MERGE_BASE})
            with mock.patch.object(ts, "run", fake_run):
                with tempfile.TemporaryDirectory() as d2:
                    ts.main(["gather", "--repo", "o/r", "--base", BASE, "--head", HEAD, "--author", "me", "--out", d2])
                    self.assertFalse((Path(d2) / "meta.json").exists())  # no PR number: no check can be built


class CanaryGate(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "Main.lean").write_text(source, encoding="utf-8")
            return canary_gate.check(Path(d))

    def test_inert_theorem_passes_with_its_import_dropped(self):
        self.assertEqual(self.check("import Mathlib\ntheorem t : 1 + 1 = 2 := rfl\n"), [])

    def test_an_axiom_added_by_a_metaprogram_is_refused(self):
        src = 'import Lean\nopen Lean Elab Command\nelab "mk" : command => pure ()\nmk\ntheorem t : True := trivial\n'
        self.assertTrue(self.check(src))

    def test_keyword_in_a_comment_is_not_a_violation(self):
        self.assertEqual(self.check("-- we do not use axiom or native_decide here\ntheorem t : True := trivial\n"), [])

    def test_command_line(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "Main.lean").write_text("axiom a : False\n", encoding="utf-8")
            r = subprocess.run([sys.executable, str(CI / "canary_gate.py"), d], capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)
            self.assertEqual(subprocess.run([sys.executable, str(CI / "canary_gate.py"), d + "/nope"], capture_output=True).returncode, 2)


if __name__ == "__main__":
    unittest.main()
