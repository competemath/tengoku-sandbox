"""trust_shadow.py, trust_ledger.py, canary_gate.py and the vendored evidence contract (docs/trust-shadow.md). No network, no Lean."""

from __future__ import annotations

import hashlib
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
            ts.sorry_record(CASE, BASE, HEAD, "no sorry/admit in added content", "2026-10-09T00:00:00Z"),
            ts.sorry_record(CASE, BASE, HEAD, "### sorry / admit in this PR\n\n- a.lean:3\n- b.lean:4", "2026-10-09T00:00:00Z"),
        ]
        recs += ts.check_records(CASE, [run_of("pr-gate"), run_of("sonar", "failure")], "2026-10-09T00:00:00Z")
        for r in recs:
            self.assertEqual(validate(r), [], r["kind"])
        self.assertEqual([r["outcome"] for r in recs[1:5]], ["pass", "fail", "pass", "fail"])
        self.assertEqual(recs[4]["details"]["occurrences"], 2)

    def test_manifest_lists_what_will_be_reported_by_subject(self):
        m = ts.manifest(CASE, "2026-10-09T00:00:00Z")
        self.assertEqual({e["kind"] for e in m["details"]["expected"]}, {"mechanical.content_lint", "mechanical.no_sorry"})
        self.assertEqual(m["producer"]["identity"], ts.STATIC["identity"])

    def test_required_checks_are_mechanical_and_the_rest_are_noted_not_weighed(self):
        recs = ts.check_records(CASE, [run_of("pr-gate"), run_of("fossa"), run_of("pr-gate", "failure")], "2026-10-09T00:00:00Z")
        kinds = sorted((r["kind"], r["outcome"]) for r in recs)
        self.assertEqual(kinds, [("attested.ci_advisory", "pass"), ("mechanical.ci", "fail"), ("mechanical.ci", "pass")])
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

    def test_identical_check_runs_are_recorded_once(self):
        recs = ts.check_records(CASE, [run_of("pr-gate"), run_of("pr-gate", id_=8)], "2026-10-09T00:00:00Z")
        self.assertEqual(len(recs), 1)

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
