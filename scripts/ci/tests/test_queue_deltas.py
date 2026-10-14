"""queue-gate.yml with the deltas (scripts/lake_cache.py): the shape of the two jobs, pinned, and the verdict step run as the shell it is.

What a faulty queue merge looked like before (2026-10-13): a group refused for a stale cache (1116 modules behind a 1000 limit), a seed that
took 49 minutes applying an 807 MB cumulative top-up, a publish over GitHub's 2 GiB asset cap, a merge whose top-up was never promoted.
These pin the workflow against each: no staleness guard, no top-up, a delta per merge under a size budget, the required check green only
once the delta is published or the group needs a nightly, and the job that runs the group's code holding no write permission."""

import os
import re
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
WORKFLOW = ROOT / ".github" / "workflows" / "queue-gate.yml"
BUILD = ROOT / ".github" / "workflows" / "build.yml"
CACHE_SH = ROOT / "scripts" / "cache.sh"


def load():
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def step(job: dict, name_part: str) -> dict:
    for s in job["steps"]:
        if name_part in (s.get("name") or ""):
            return s
    raise AssertionError(f"no step named like {name_part!r}: {[s.get('name') for s in job['steps']]}")


class Shape(unittest.TestCase):
    def setUp(self):
        self.wf = load()
        self.build = self.wf["jobs"]["queue-build"]
        self.gate = self.wf["jobs"]["queue-gate"]

    def test_the_job_that_runs_the_groups_code_holds_no_write_permission(self):
        perms = self.build["permissions"]
        self.assertTrue(all(v == "read" for v in perms.values()), perms)
        self.assertEqual(self.wf["permissions"], {})

    def test_the_queue_seeds_the_nightly_base_only_and_restores_the_deltas(self):
        env = self.wf["env"]
        self.assertEqual(str(env["TENGOKU_TOPUPS"]), "0")
        self.assertEqual(str(env["LAKE_ARTIFACT_CACHE"]), "true")
        self.assertIn("LAKE_CACHE_DIR", env)
        seed = step(self.build, "restore what merged since it")
        self.assertIn("scripts/cache.sh get", seed["run"])
        self.assertIn("scripts/lake_cache.py restore --fresh", seed["run"])
        self.assertNotIn("cache_fresh.py", WORKFLOW.read_text(encoding="utf-8"))

    def test_every_lean_build_of_the_group_records_its_mappings(self):
        cand = step(self.build, "Generate candidates")
        self.assertIn("lake build $targets -o out-candidates.jsonl", cand["run"])
        self.assertIn("scripts/lake_cache.py check", cand["run"])
        whole = step(self.build, "Build the library as main will have it")
        self.assertRegex(whole["run"], r"timeout -k \d+ \d+m lake build Tengoku\.All -o out-all\.jsonl")
        self.assertIn("scripts/lake_cache.py diff |", whole["run"])
        self.assertIn('scripts/lake_cache.py pack --assets "$assets"', whole["run"])
        self.assertNotIn("topup", whole["run"])
        self.assertIn(
            "TENGOKU_DELTA_BUDGET_MB",
            whole["env"],
            "the budget is a repository variable (0 in a sandbox scenario: every delta over budget)",
        )

    def test_no_call_of_lake_cache_passes_a_path_or_a_commit(self):
        """Sonar and Snyk flag a command-line path that reaches open() or a process argument; the CLI takes none, and the workflow must not pass one."""
        text = WORKFLOW.read_text(encoding="utf-8")
        for call in re.findall(r"scripts/lake_cache\.py (?:diff|check|pack)[^\n|]*", text):
            for banned in ("--out", "--new", "--to", "--had", "--targets", "--log", "--rev"):
                self.assertNotIn(banned, call, call)

    def test_the_states_a_build_can_end_in_are_the_ones_the_gate_handles(self):
        whole = step(self.build, "Build the library as main will have it")
        states = set(re.findall(r'echo "state=([a-z-]+)"', whole["run"])) | set(
            re.findall(r'"publish": "([a-z-]+)", "empty": "([a-z-]+)"', whole["run"])[0]
        )
        self.assertEqual(states, {"needs-nightly", "complete", "empty"})
        pub = step(self.gate, "Publish it")
        for st in ("empty", "needs-nightly"):
            self.assertIn(f"{st})", pub["run"], f"the publish step handles state {st}")

    def test_the_gate_attests_the_delta_and_publishes_it_to_the_days_release(self):
        att = step(self.gate, "Attest the delta")
        self.assertIn("delta-out/d-*.tar.zst", att["with"]["subject-path"])
        pub = step(self.gate, "Publish it")
        self.assertIn('rel="lake-deltas-$tag"', pub["run"])
        self.assertIn('gh release upload "$rel" delta-out/d-*.tar.zst', pub["run"])
        self.assertIn("gh workflow run build.yml", pub["run"], "a needs-nightly merge starts the cache build")
        self.assertIn("actions", self.gate["permissions"])

    def test_a_group_whose_base_has_no_published_mappings_is_marked_needs_nightly_and_builds_nothing_more(self):
        """The tree already holds the group when the base's mappings are looked for: a second `lake build -o` there lists the group's modules as the
        base's, which empties the group's delta and publishes the group's mappings as the nightly's (CodeRabbit, #433). The group merges marked
        needs-nightly instead, and the nightly that follows publishes the mappings."""
        run = step(self.build, "Build the library as main will have it")["run"]
        self.assertEqual(run.count("lake build"), 1, "the library is built once, at the group's commit")
        self.assertNotIn("base-computed", WORKFLOW.read_text(encoding="utf-8"))
        self.assertNotIn("--with-computed-base", WORKFLOW.read_text(encoding="utf-8"))
        missing = run[run.index(".lake/.base-missing") :]
        self.assertIn("needs-nightly:base-mappings-missing", missing.split("fi\n")[0])
        self.assertIn('echo "state=needs-nightly" >> "$GITHUB_OUTPUT"; exit 0', missing.split("fi\n")[0])
        self.assertLess(run.index(".lake/.base-missing"), run.index("scripts/lake_cache.py diff"), "decided before the diff is taken")

    def test_the_nightly_publishes_its_mappings_and_opens_the_days_delta_release(self):
        b = BUILD.read_text(encoding="utf-8")
        self.assertIn("lake build Tengoku.All -o base.jsonl", b)
        self.assertIn("cache-out/base.jsonl", b)
        c = CACHE_SH.read_text(encoding="utf-8")
        self.assertIn('gh release upload "$tag" "$tmp/base.jsonl"', c)
        self.assertIn('gh release create "lake-deltas-$tag"', c)
        self.assertIn('gh release delete "lake-deltas-$old"', c)


CACHE_GH = """#!/usr/bin/env bash
echo "$*" >> "$GH_LOG"
case "$1 $2" in
  "auth status") exit 0 ;;
  "release view") exit 1 ;;
  "release upload") case "$*" in *base.jsonl*) [ -n "$FAIL_BASE_UPLOAD" ] && { echo "HTTP 502" >&2; exit 1; } ;; esac ;;
esac
exit 0
"""


class NightlyPublish(unittest.TestCase):
    """scripts/cache.sh publish with a fake gh: the mappings the queue's deltas are measured against must not be lost without a word."""

    def publish(self, fail_base_upload: bool) -> tuple[subprocess.CompletedProcess, list[str]]:
        with tempfile.TemporaryDirectory() as d:
            root, out, bin_ = Path(d) / "tree", Path(d) / "out", Path(d) / "bin"
            for p in (root, out, bin_):
                p.mkdir()
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n")
            (out / "commit").write_text("c" * 40 + "\n")
            (out / "tengoku-cache.tar.zst.part-aa").write_text("x")
            (out / "base.jsonl").write_text('"2026-03-17"\n{"i":1}\n')
            for name, text in (("gh", CACHE_GH), ("curl", "#!/usr/bin/env bash\nexit 22\n")):
                (bin_ / name).write_text(text)
                (bin_ / name).chmod(0o755)
            log = Path(d) / "gh.log"
            env = {
                **os.environ,
                "PATH": f"{bin_}{os.pathsep}{os.environ['PATH']}",
                "GH_LOG": str(log),
                "TENGOKU_ROOT": str(root),
                "TENGOKU_REPO": "o/r",
                "TENGOKU_CACHE_STAMP": "20261014T0336Z",
                "FAIL_BASE_UPLOAD": "1" if fail_base_upload else "",
            }
            r = subprocess.run(["bash", str(CACHE_SH), "publish", str(out)], env=env, capture_output=True, text=True)
            return r, (log.read_text().splitlines() if log.exists() else [])

    def test_a_failed_upload_of_the_mappings_fails_the_publish_before_the_pointer_moves(self):
        # `[[ -f f ]] && gh upload && echo` under set -e swallows the failure of the upload: the cache went out without its mappings, silently
        r, calls = self.publish(fail_base_upload=True)
        self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("base.jsonl upload failed", r.stderr)
        self.assertFalse(any("cache-latest" in c and "upload" in c for c in calls), calls)

    def test_a_good_upload_goes_on_to_the_pointer(self):
        r, calls = self.publish(fail_base_upload=False)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("base.jsonl on cache-20261014T0336Z", r.stdout)
        self.assertTrue(any(c.startswith("release upload cache-latest") for c in calls), calls)


class Verdict(unittest.TestCase):
    """The Verdict step's shell, run for real with a fake gh: green only when the build passed and the publish step passed."""

    def run_verdict(self, build: str, publish: str, event: str = "merge_group") -> tuple[int, list[str]]:
        run = step(load()["jobs"]["queue-gate"], "Verdict")["run"]
        # the expressions the runner would substitute
        run = (
            run.replace("${{ github.event_name }}", event)
            .replace("${{ github.server_url }}", "https://github.test")
            .replace("${{ github.repository }}", "o/r")
            .replace("${{ github.run_id }}", "1")
        )
        with tempfile.TemporaryDirectory() as d:
            gh = Path(d) / "gh"
            gh.write_text('#!/usr/bin/env bash\necho "$*" >> "$GH_LOG"\n')
            gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
            log = Path(d) / "gh.log"
            env = {
                **os.environ,
                "PATH": f"{d}{os.pathsep}{os.environ['PATH']}",
                "GH_LOG": str(log),
                "BUILD": build,
                "PUBLISH": publish,
                "GITHUB_REF": "refs/heads/gh-readonly-queue/main/pr-42-" + "a" * 40,
                "GITHUB_REPOSITORY": "o/r",
            }
            r = subprocess.run(["bash", "-e", "-o", "pipefail", "-c", run], env=env, capture_output=True, text=True)
            return r.returncode, (log.read_text().splitlines() if log.exists() else [])

    def test_green_only_when_the_build_and_the_publish_both_passed(self):
        self.assertEqual(self.run_verdict("success", "success")[0], 0)
        self.assertEqual(self.run_verdict("failure", "skipped")[0], 1)
        self.assertEqual(self.run_verdict("success", "failure")[0], 1)
        self.assertEqual(self.run_verdict("success", "skipped")[0], 1)

    def test_a_group_that_compiled_but_could_not_publish_is_told_it_was_not_its_fault(self):
        rc, calls = self.run_verdict("success", "failure")
        self.assertEqual(rc, 1)
        self.assertTrue(any(c.startswith("pr comment 42 ") and "not because of your change" in c for c in calls), calls)

    def test_a_failed_build_gets_no_such_comment(self):
        rc, calls = self.run_verdict("failure", "skipped")
        self.assertEqual((rc, calls), (1, []))

    def test_on_a_pull_request_the_check_passes_at_once(self):
        self.assertEqual(self.run_verdict("success", "skipped", event="pull_request")[0], 0)


if __name__ == "__main__":
    unittest.main()
