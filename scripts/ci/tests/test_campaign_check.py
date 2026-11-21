"""ci_paths.py and campaign_check.py: a CI-class change needs a campaign or the approver's waiver, and what is CI-class is decided by the files.

Real case (tengoku#1025/#1026, 2026-11-21): scripts/roots_tree.py is outside scripts/ci/, yet scripts/ci/roots_check.py imports it inside a function to recompute what a roots PR must be, and
classify.py imports roots_check: a change to it changes a gate. It went in without a campaign because it was judged "a library module". The fixture reproduces exactly those relations.
"""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import campaign_check as cc
import ci_paths as cp

SHA = "a" * 40
OLD = "b" * 40
APPROVER = "mikaelbashir14096545"

TREE = {
    ".github/workflows/pr-gate.yml": 'jobs:\n  classify:\n    steps:\n      - run: python3 scripts/ci/classify.py "$BASE" "$HEAD"\n',
    ".github/workflows/leakscan-tests.yml": "jobs:\n  fixture:\n    steps:\n      - run: python3 scripts/ci/roots_gate.py < report.txt\n",
    "scripts/ci/classify.py": "from _git import changed_files\nfrom roots_check import is_roots\n",
    "scripts/ci/_git.py": "import os\n",
    "scripts/ci/roots_check.py": "import sys\n\n\ndef is_roots(base, head):\n    sys.path.insert(0, 'scripts')\n    import roots_tree  # a late import, inside the function\n    return roots_tree.roots_of(head)\n",
    "scripts/ci/roots_gate.py": "import re\n",
    "scripts/roots_tree.py": "import re\nfrom autonames import pascal\n",
    "scripts/autonames.py": "X = 1\n",
    "scripts/generate.py": "import roots_tree_unused_name\nprint('a generator no gate runs')\n",
    "scripts/ci/campaign/gate.sh": "scripts/ci/classify.py\n",
    "scripts/helper.sh": "echo scripts/generate.py\n",
}


class CiPaths(unittest.TestCase):
    def test_a_module_outside_scripts_ci_that_a_gate_imports_is_ci_class(self):
        ci = cp.ci_files(["scripts/roots_tree.py"], TREE)
        self.assertIn("scripts/roots_tree.py", ci)
        self.assertIn("scripts/ci/roots_check.py", ci["scripts/roots_tree.py"])  # and says who uses it

    def test_the_closure_goes_all_the_way(self):
        self.assertIn("scripts/autonames.py", cp.ci_files(["scripts/autonames.py"], TREE))  # roots_tree imports it

    def test_direct_paths(self):
        for p in (".github/workflows/anything.yml", "scripts/ci/new_gate.py", "scripts/ci/tests/test_x.py", ".github/CODEOWNERS"):
            self.assertIn(p, cp.ci_files([p], TREE), p)

    def test_not_ci_class(self):
        for p in (
            "scripts/generate.py",
            "scripts/helper.sh",
            "docs/x.md",
            "README.md",
            "Tengoku/Foo.lean",
            "data/tentative/a.jsonl",
            "scripts/ci/campaign/README.md",
        ):
            self.assertNotIn(p, cp.ci_files([p], TREE), p)

    def test_a_late_import_counts_and_an_unparseable_file_imports_nothing(self):
        self.assertEqual(cp.python_imports("def f():\n    import roots_tree\n"), {"roots_tree"})
        self.assertEqual(cp.python_imports("def f(:\n"), set())

    def test_an_unknown_module_is_not_a_file(self):
        self.assertEqual(cp.references("scripts/ci/x.py", "import json\nimport nothing_here\n", set(TREE)), set())


class RealTree(unittest.TestCase):
    """the repository's own scripts and workflows (the checkout CI runs in; TENGOKU_CI_ROOT points elsewhere): the case that was missed is true of the real files, not only of the fixture"""

    ROOT = Path(__import__("os").environ.get("TENGOKU_CI_ROOT") or Path(__file__).resolve().parents[3])

    def test_roots_tree_is_a_gate_dependency_in_the_real_tree(self):
        files = cc.tree_files(self.ROOT)
        if "scripts/roots_tree.py" not in files:
            self.skipTest("no checkout of the repository here")
        self.assertIn("scripts/roots_tree.py", cp.ci_files(["scripts/roots_tree.py"], files))
        self.assertNotIn("scripts/harvest.py", cp.ci_files(["scripts/harvest.py"], files))  # a tool no gate reaches stays out


def review(login, body, commit=SHA, at="2026-11-21T12:00:00Z", state="COMMENTED"):
    return {"user": {"login": login}, "body": body, "commit_id": commit, "submitted_at": at, "state": state}


GOOD = "campaign-waiver: only a comment of the roots_tree docstring changes, no behaviour"


class Waiver(unittest.TestCase):
    def verdict(self, changed, reviews):
        return cc.verdict(changed, TREE, reviews, APPROVER, SHA)

    def test_not_ci_class_passes_without_anything(self):
        ok, msg = self.verdict(["docs/x.md", "scripts/generate.py"], [])
        self.assertTrue(ok)
        self.assertIn("no campaign needed", msg)

    def test_ci_class_without_a_waiver_fails_and_says_what_to_do(self):
        ok, msg = self.verdict(["scripts/roots_tree.py"], [])
        self.assertFalse(ok)
        self.assertIn("scripts/roots_tree.py", msg)
        self.assertIn("campaign-waiver", msg)

    def test_the_approvers_waiver_on_the_head_passes(self):
        ok, msg = self.verdict(["scripts/roots_tree.py"], [review(APPROVER, GOOD)])
        self.assertTrue(ok)
        self.assertIn("waived by " + APPROVER, msg)

    def test_a_waiver_by_anyone_else_is_refused(self):
        for who in ("mikael-bashir", "gitar-bot", "somebody"):
            ok, msg = self.verdict(["scripts/roots_tree.py"], [review(who, GOOD)])
            self.assertFalse(ok, who)
            self.assertIn("not by " + APPROVER, msg)

    def test_a_waiver_on_an_older_commit_is_void(self):
        ok, msg = self.verdict(["scripts/roots_tree.py"], [review(APPROVER, GOOD, commit=OLD)])
        self.assertFalse(ok)
        self.assertIn("a push voids it", msg)

    def test_a_short_reason_is_refused(self):
        ok, msg = self.verdict(["scripts/roots_tree.py"], [review(APPROVER, "campaign-waiver: fine")])
        self.assertFalse(ok)
        self.assertIn("under 20 characters", msg)

    def test_the_account_name_is_compared_without_case(self):
        ok, _ = self.verdict(["scripts/roots_tree.py"], [review(APPROVER.upper(), GOOD)])
        self.assertTrue(ok)

    def test_a_newer_good_waiver_beats_an_older_bad_one(self):
        reviews = [review(APPROVER, "campaign-waiver: short", at="2026-11-21T11:00:00Z"), review(APPROVER, GOOD, at="2026-11-21T12:00:00Z")]
        self.assertTrue(self.verdict(["scripts/ci/new_gate.py"], reviews)[0])

    def test_an_approval_without_the_line_is_not_a_waiver(self):
        ok, _ = self.verdict(["scripts/roots_tree.py"], [review(APPROVER, "approved, looks good")])
        self.assertFalse(ok)

    def test_only_an_approving_or_commenting_review_waives(self):
        for state, ok_expected in (
            ("APPROVED", True),
            ("COMMENTED", True),
            ("DISMISSED", False),
            ("CHANGES_REQUESTED", False),
            ("PENDING", False),
        ):
            ok, _ = self.verdict(["scripts/roots_tree.py"], [review(APPROVER, GOOD, state=state)])
            self.assertEqual(ok, ok_expected, state)

    def test_the_approver_is_a_constant_of_the_script_not_a_repository_variable(self):
        self.assertEqual(cc.APPROVER, "mikaelbashir14096545")
        workflow = Path(cc.__file__).resolve().parents[2] / ".github" / "workflows" / "campaign-gate.yml"
        if workflow.exists():
            self.assertNotIn("APPROVER", workflow.read_text())


class GateData(unittest.TestCase):
    def test_the_data_files_a_gate_reads_are_ci_class(self):
        changed = [
            "schemas/allowed-options.json",
            "schemas/command-keywords.json",
            "lean-toolchain",
            "lakefile.toml",
            "tools/CommandKeywords.lean",
        ]
        self.assertEqual(set(cp.ci_files(changed, TREE)), set(changed))

    def test_the_registry_and_other_tools_are_not(self):
        changed = ["schemas/sources.json", "tools/harvest.py", "data/staging/x.jsonl", "docs/pr-classes.md"]
        self.assertEqual(cp.ci_files(changed, TREE), {})


class TreeFiles(unittest.TestCase):
    def test_a_checkout_under_a_folder_named_tests_keeps_its_files(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d) / "tests" / "checkout"
            (root / "scripts" / "ci").mkdir(parents=True)
            (root / "scripts" / "ci" / "gate.py").write_text("import roots_tree\n")
            (root / "scripts" / "roots_tree.py").write_text("x = 1\n")
            (root / "scripts" / "ci" / "tests").mkdir()
            (root / "scripts" / "ci" / "tests" / "test_gate.py").write_text("")
            files = cc.tree_files(root)
            self.assertEqual(
                set(files), {"scripts/ci/gate.py", "scripts/roots_tree.py"}
            )  # the checkout's own tests folder is skipped, the one above it is not
            self.assertIn("scripts/roots_tree.py", cp.ci_files(["scripts/roots_tree.py"], files))


if __name__ == "__main__":
    unittest.main()
