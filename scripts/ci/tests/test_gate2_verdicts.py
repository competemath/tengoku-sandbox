"""The intake and extend gate: a bundle must prove that Gate 2 judged every module it ships.

2026-10-17: navier-stokes-euler part 1 (#588, merged) shipped 89 modules, 84 of them with theorem statements (504 theorem/lemma commands), that Gate 2 never judged: two of its 32
shards ran out of memory and time, the factory's driver wrote the modules to gate2-killed.json, and nothing read the file. The factory (emissary-archangel, bundle.py compose) now cuts
such modules with their importers and records `gate2_unjudged` (empty by construction) in the report inside the archive it attests; this gate refuses a report without the field, with
anything but an empty list in it, and a bundle whose attestation is not of a build from the factory's main branch (the only code that is reviewed)."""

from __future__ import annotations

import json
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import test_extend as te  # noqa: E402 (the module, not its test class: unittest would collect the class here too)

ROOT = HERE.parents[2]


class Verdicts(unittest.TestCase):
    """Extend (part 2 of fx-lib) and intake (part 1) PRs, with the report's field set every way a careless or a dishonest factory could."""

    A, B = te.Extend.A, te.Extend.B
    repo, part2, check = te.Extend.repo, te.Extend.part2, te.Extend.check  # the fixtures of test_extend.py, without its tests

    def part2_with(self, field):
        r = self.repo()
        report = {"library": "fx-lib", "part": 2}
        if field is not ABSENT:
            report["gate2_unjudged"] = field
        self.part2(r, report=json.dumps(report) + "\n")
        return r

    def part1_with(self, field):
        r = self.repo(with_library=False)
        r.write("Tengoku/FxLib/Fx/A.lean", "import Tengoku\nnamespace Fx\n\ntheorem a : 1 + 1 = 2 := rfl\n\nend Fx\n")
        r.write("Tengoku/FxLib.lean", f"import {self.A}\n")
        r.write("data/intake/fx-lib/manifest.jsonl", te.record("a", self.A))
        report = {"library": "fx-lib", "part": 1}
        if field is not ABSENT:
            report["gate2_unjudged"] = field
        r.write("data/intake/fx-lib/report.json", json.dumps(report) + "\n")
        r.write("Tengoku/All.lean", "import Tengoku.Lib\nimport Tengoku.FxLib\n")
        r.commit("part 1")
        return r

    def refused(self, r, what):
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0, f"{what}: the gate accepted it\n{out}")
        self.assertIn("gate2_unjudged", out, what)

    def test_an_empty_list_passes_an_extend_and_an_intake_pr(self):
        rc, out = self.check(self.part2_with([]))
        self.assertEqual(rc, 0, out)
        rc, out = self.check(self.part1_with([]))
        self.assertEqual(rc, 0, out)

    def test_a_report_without_the_field_is_refused_in_both(self):
        # a bundle cut before the factory recorded it: nothing says Gate 2 judged every module
        self.refused(self.part2_with(ABSENT), "extend, field absent")
        self.refused(self.part1_with(ABSENT), "intake, field absent")

    def test_modules_in_the_list_are_refused(self):
        self.refused(self.part2_with(["Euler.BaseFirstPacketSupport"]), "extend, one module")
        self.refused(self.part1_with(["Euler.A", "Euler.B"]), "intake, two modules")

    def test_every_other_shape_of_the_field_is_refused_too(self):
        # `if not unjudged` or `== []`-by-truthiness would let these through
        for what, value in (
            ("null", None),
            ("false", False),
            ("zero", 0),
            ("empty string", ""),
            ("string", "[]"),
            ("empty object", {}),
            ("list in a list", [[]]),
            ("blank name", [""]),
        ):
            self.refused(self.part2_with(value), f"extend, {what}")

    def test_a_report_that_is_not_json_or_not_an_object_is_refused(self):
        for text in ("not json", "[]", "null", '"gate2_unjudged"', ""):
            r = self.repo()
            self.part2(r, report=text)
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, text)

    def test_an_intake_report_that_is_not_json_is_refused(self):
        # no other check reads the first part's report: only this one stops a bundle whose report cannot say anything
        for text in ("not json\n", "[]\n", "null\n", ""):
            r = self.part1_with([])
            r.write("data/intake/fx-lib/report.json", text)
            r.commit("a report that says nothing")
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, repr(text))
            self.assertIn("report.json", out)

    def test_the_field_in_the_wrong_file_does_not_count(self):
        # the part's own report is what is checked: the tree's part 1 report, or an extra file, cannot vouch for it
        r = self.repo()
        self.part2(
            r,
            report=json.dumps({"library": "fx-lib", "part": 2}) + "\n",
            extra={"data/intake/fx-lib/report.json": json.dumps({"library": "fx-lib", "part": 1, "gate2_unjudged": []}) + "\n"},
        )
        self.refused(r, "field only in the old report")

    def test_the_field_must_be_a_real_key_not_a_word_in_another_one(self):
        r = self.repo()
        self.part2(
            r, report=json.dumps({"library": "fx-lib", "part": 2, "note": "gate2_unjudged: []", "gate2_unjudged_modules": []}) + "\n"
        )
        self.refused(r, "a look-alike")

    def test_the_gate_still_names_the_factory_requirement(self):
        rc, out = self.check(self.part2_with(["Euler.A"]))
        self.assertIn("proves Gate 2 judged every module", out)


ABSENT = object()


class Provenance(unittest.TestCase):
    """The attestation step: a bundle built by the factory's workflow on a branch is as validly attested as one built on main, so the check names the branch."""

    def step(self) -> str:
        text = (ROOT / ".github" / "workflows" / "pr-gate.yml").read_text()
        i = text.index("gh attestation verify")
        return text[i : text.index("\n\n", i)]

    def test_every_attestation_check_of_a_bundle_requires_the_main_branch(self):
        text = (ROOT / ".github" / "workflows" / "pr-gate.yml").read_text()
        verifies = [m.start() for m in re.finditer(r"gh attestation verify", text)]
        self.assertGreaterEqual(len(verifies), 1)
        for i in verifies:
            command = text[i : text.index("; then", i)]
            self.assertIn("--source-ref refs/heads/main", command)
            self.assertIn("--signer-workflow", command)
            self.assertIn("--repo competemath/emissary-archangel", command)

    def test_both_factory_workflows_are_still_accepted_and_nothing_else(self):
        step = self.step()
        self.assertIn("for wf in bump-library bump-sharded; do", (ROOT / ".github" / "workflows" / "pr-gate.yml").read_text())
        self.assertNotIn('--signer-workflow "competemath/emissary-archangel/.github/workflows/$wf.yml" ||', step)

    def test_a_missing_attestation_fails_the_job(self):
        text = (ROOT / ".github" / "workflows" / "pr-gate.yml").read_text()
        self.assertIn('[ "${ok:-0}" = 1 ] || {', text)
        self.assertIn("exit 1", text[text.index('[ "${ok:-0}" = 1 ] ||') :][:400])


if __name__ == "__main__":
    unittest.main()
