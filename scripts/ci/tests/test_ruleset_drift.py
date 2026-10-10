"""ruleset_drift.py (docs/ci-records.md): a loosened ruleset is found, a reordered one is not, and the invariants of the default branch are asserted. No network."""

from __future__ import annotations

import copy
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
TREE = CI.parents[1]
sys.path.insert(0, str(CI))

import ruleset_drift as rd  # noqa: E402

LIVE = {
    "id": 7,
    "name": "main: PRs only",
    "target": "branch",
    "source_type": "Repository",
    "source": "o/r",
    "enforcement": "active",
    "node_id": "RRS_x",
    "created_at": "2026-09-15T15:38:57.876+01:00",
    "updated_at": "2026-10-09T11:07:53.061+01:00",
    "current_user_can_bypass": "never",
    "bypass_actors": [],
    "_links": {"self": {"href": "https://api.github.com/repos/o/r/rulesets/7"}},
    "conditions": {"ref_name": {"exclude": [], "include": ["~DEFAULT_BRANCH"]}},
    "rules": [
        {"type": "deletion"},
        {"type": "non_fast_forward"},
        {"type": "pull_request", "parameters": {"required_approving_review_count": 1, "allowed_merge_methods": ["squash", "merge"]}},
        {
            "type": "required_status_checks",
            "parameters": {
                "required_status_checks": [{"context": "pr-gate", "integration_id": 15368}, {"context": "queue-gate"}],
                "strict_required_status_checks_policy": True,
            },
        },
    ],
}
IN_FORCE = [
    {"type": "deletion", "ruleset_id": 7},
    {"type": "non_fast_forward", "ruleset_id": 7},
    {"type": "pull_request", "parameters": {"required_approving_review_count": 1}, "ruleset_id": 7},
    {
        "type": "required_status_checks",
        "parameters": {"required_status_checks": [{"context": "pr-gate", "integration_id": 15368}]},
        "ruleset_id": 7,
    },
]


def snapshots(live=LIVE, bypass=False):
    doc = rd.normalise(live, bypass)
    return {doc["name"]: ("main.json", doc)}


class Normalise(unittest.TestCase):
    def test_volatile_fields_are_dropped_and_lists_are_sorted(self):
        doc = rd.normalise(LIVE, False)
        self.assertEqual(set(doc), {"name", "target", "enforcement", "conditions", "rules"})
        self.assertEqual([r["type"] for r in doc["rules"]], ["deletion", "non_fast_forward", "pull_request", "required_status_checks"])
        self.assertEqual(doc["rules"][2]["parameters"]["allowed_merge_methods"], ["merge", "squash"])

    def test_the_bypass_actors_are_kept_only_when_asked_for(self):
        self.assertIn("bypass_actors", rd.normalise(LIVE, True))
        self.assertNotIn("bypass_actors", rd.normalise(LIVE, False))

    def test_the_slug(self):
        self.assertEqual(rd.slug("main: PRs only, checks, queue, linear history"), "main-prs-only-checks-queue-linear-history")
        self.assertEqual(rd.slug("???"), "ruleset")


class Compare(unittest.TestCase):
    def test_the_same_ruleset_in_another_order_is_no_drift(self):
        shuffled = copy.deepcopy(LIVE)
        shuffled["rules"].reverse()
        shuffled["rules"][0]["parameters"]["required_status_checks"].reverse()
        shuffled["updated_at"] = "2027-01-01T00:00:00Z"
        self.assertEqual(rd.compare([shuffled], snapshots()), ([], []))

    def test_a_loosened_ruleset_is_a_readable_diff(self):
        loosened = copy.deepcopy(LIVE)
        loosened["rules"][2]["parameters"]["required_approving_review_count"] = 0
        loosened["rules"] = [r for r in loosened["rules"] if r["type"] != "non_fast_forward"]
        drift, _ = rd.compare([loosened], snapshots())
        self.assertEqual(len(drift), 1)
        lines = [re.sub(r"^([-+])\s+", r"\1", ln.strip()) for ln in drift[0].splitlines()]
        self.assertIn('-"required_approving_review_count": 1', lines)
        self.assertIn('+"required_approving_review_count": 0', lines)
        self.assertIn('-"type": "non_fast_forward"', lines)

    def test_an_enforcement_switched_to_evaluate_is_drift(self):
        off = dict(LIVE, enforcement="evaluate")
        self.assertEqual(len(rd.compare([off], snapshots())[0]), 1)

    def test_a_new_ruleset_and_a_deleted_one_are_drift(self):
        extra = dict(LIVE, name="new one")
        drift, _ = rd.compare([LIVE, extra], snapshots())
        self.assertEqual(len(drift), 1)
        self.assertIn("not committed", drift[0])
        drift, _ = rd.compare([], snapshots())
        self.assertIn("deleted or renamed", drift[0])

    def test_bypass_actors_a_token_cannot_see_are_not_compared_and_the_report_says_so(self):
        hidden = {k: v for k, v in LIVE.items() if k != "bypass_actors"}
        drift, notices = rd.compare([hidden], snapshots(bypass=True))
        self.assertEqual(drift, [])
        self.assertIn("not visible", notices[0])

    def test_bypass_actors_an_administrator_can_see_are_compared(self):
        snap = snapshots(bypass=True)
        added = copy.deepcopy(LIVE)
        added["bypass_actors"] = [{"actor_id": 5, "actor_type": "RepositoryRole", "bypass_mode": "always"}]
        self.assertEqual(len(rd.compare([added], snap)[0]), 1)
        self.assertEqual(rd.compare([LIVE], snap), ([], []))

    def test_the_snapshot_of_this_repository_matches_the_shape_the_checker_reads(self):
        found = rd.load_snapshots(TREE / ".github" / "rulesets")
        self.assertTrue(found)
        for name, (fname, doc) in found.items():
            self.assertEqual(rd.normalise(doc, True), doc, f"{fname} is not in normal form: regenerate it with `ruleset_drift.py snapshot`")
            self.assertEqual(rd.slug(name) + ".json", fname)


class Invariants(unittest.TestCase):
    def test_a_protected_branch_has_no_failure(self):
        failures, warnings = rd.invariants(IN_FORCE)
        self.assertEqual((failures, warnings), ([], []))

    def test_each_missing_rule_is_a_failure(self):
        for missing, fragment in (
            ("deletion", "`deletion`"),
            ("non_fast_forward", "`non_fast_forward`"),
            ("required_status_checks", "required status check"),
            ("pull_request", "pull-request rule"),
        ):
            rules = [r for r in IN_FORCE if r["type"] != missing]
            failures, _ = rd.invariants(rules)
            self.assertTrue(any(fragment in f for f in failures), (missing, failures))

    def test_the_merge_queue_stands_in_for_required_approvals(self):
        rules = [r for r in IN_FORCE if r["type"] != "pull_request"] + [{"type": "merge_queue", "parameters": {}}]
        self.assertEqual(rd.invariants(rules)[0], [])

    def test_zero_required_approvals_without_a_queue_fails(self):
        rules = [dict(r, parameters={"required_approving_review_count": 0}) if r["type"] == "pull_request" else r for r in IN_FORCE]
        self.assertTrue(any("pull-request rule" in f for f in rd.invariants(rules)[0]))

    def test_a_required_check_without_an_app_is_a_warning_and_never_a_failure(self):
        rules = copy.deepcopy(IN_FORCE)
        rules[3]["parameters"]["required_status_checks"].append({"context": "queue-gate"})
        failures, warnings = rd.invariants(rules)
        self.assertEqual(failures, [])
        self.assertEqual(len(warnings), 1)
        self.assertIn("queue-gate", warnings[0])

    def test_nothing_in_force_fails_everything(self):
        self.assertEqual(len(rd.invariants([])[0]), 4)


class Fetch(unittest.TestCase):
    def test_every_ruleset_is_fetched_in_full_by_its_id_from_the_repositorys_own_endpoint(self):
        seen = []

        def get(path):
            seen.append(path)
            if path == "repos/o/r/rulesets":
                # one of them inherited from the organisation: its own link points at an endpoint the workflow's token may not read
                return [
                    {"id": 7, "name": "a", "_links": {"self": {"href": "https://api.github.com/orgs/o/rulesets/7"}}},
                    {"id": 8, "name": "b"},
                ]
            return {"path": path}

        self.assertEqual(rd.fetch_live("o/r", get), [{"path": "repos/o/r/rulesets/7"}, {"path": "repos/o/r/rulesets/8"}])
        self.assertFalse([p for p in seen if p.startswith("orgs/")])


class Cli(unittest.TestCase):
    def gh_shim(self, live, in_force):
        d = Path(tempfile.mkdtemp())
        (d / "rulesets.json").write_text(
            json.dumps([{"id": 7, "name": live["name"], "_links": {"self": {"href": "https://api.github.com/repos/o/r/rulesets/7"}}}])
        )
        (d / "ruleset7.json").write_text(json.dumps(live))
        (d / "repo.json").write_text(json.dumps({"default_branch": "main"}))
        (d / "rules.json").write_text(json.dumps(in_force))
        shim = d / "gh"
        shim.write_text(
            '#!/bin/sh\ncase "$2" in\n'
            f'  repos/o/r/rulesets) cat "{d}/rulesets.json";;\n'
            f'  repos/o/r/rulesets/7) cat "{d}/ruleset7.json";;\n'
            f'  repos/o/r) cat "{d}/repo.json";;\n'
            f'  repos/o/r/rules/branches/main) cat "{d}/rules.json";;\n'
            '  *) echo "unexpected $2" >&2; exit 1;;\nesac\n',
            encoding="utf-8",
        )
        shim.chmod(0o755)
        return d

    def run_cli(self, d, *args):
        env = {**os.environ, "PATH": f"{d}{os.pathsep}{os.environ['PATH']}"}
        return subprocess.run([sys.executable, str(CI / "ruleset_drift.py"), *args], capture_output=True, text=True, env=env)

    def test_snapshot_then_check_then_a_loosened_setting(self):
        with_queue_gate = copy.deepcopy(IN_FORCE)
        with_queue_gate[3]["parameters"]["required_status_checks"].append({"context": "queue-gate"})
        d = self.gh_shim(LIVE, with_queue_gate)
        out = Path(tempfile.mkdtemp()) / "rulesets"
        self.assertEqual(self.run_cli(d, "snapshot", "--repo", "o/r", "--dir", str(out)).returncode, 0)
        self.assertEqual([p.name for p in out.iterdir()], ["main-prs-only.json"])
        done = self.run_cli(d, "check", "--repo", "o/r", "--dir", str(out))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("warning: required check `queue-gate`", done.stdout)
        loosened = copy.deepcopy(LIVE)
        loosened["rules"] = [r for r in loosened["rules"] if r["type"] != "deletion"]
        d2 = self.gh_shim(loosened, [r for r in IN_FORCE if r["type"] != "deletion"])
        done = self.run_cli(d2, "check", "--repo", "o/r", "--dir", str(out))
        self.assertEqual(done.returncode, 1)
        self.assertIn("differs from main-prs-only.json", done.stdout)
        self.assertIn("`deletion`", done.stdout)

    def test_no_snapshots_and_a_bad_repository_are_exit_2(self):
        d = self.gh_shim(LIVE, IN_FORCE)
        self.assertEqual(self.run_cli(d, "check", "--repo", "o/r", "--dir", str(Path(tempfile.mkdtemp()) / "none")).returncode, 2)
        self.assertEqual(self.run_cli(d, "check", "--repo", "bad").returncode, 2)

    def test_an_api_failure_is_exit_2_not_a_pass(self):
        with mock.patch.object(rd, "gh_json", side_effect=rd.ApiError("HTTP 403")):
            self.assertEqual(rd.main(["check", "--repo", "o/r"]), 2)


if __name__ == "__main__":
    unittest.main()
