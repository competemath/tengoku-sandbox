"""cache_fresh.py: the merge queue seeds from the newest published cache, and lets a group on only when that cache is close enough to the base.
Its own file, so that tests of other gates added at the end of test_gates.py do not conflict with it."""

from __future__ import annotations

import json
import re
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import Repo  # noqa: E402


class TimeBudget(unittest.TestCase):
    """What the queue's build can take, worst case, against the queue's check timeout (the ruleset's `check_response_timeout_minutes`, 120 on tengoku).
    Measured on the real runs of 2026-10-14 (tag groups of 351 and 353 modules): checkout, toolchain and disk 3.7 min, seed 4.4, candidates 21.4,
    axioms 4.1, tags 6.1, leak report 16.6 (48 min between them; 60 leaves room for a larger group), the whole-library build 3 to 6 when the group
    is a tag group, and 25 for a part of 286 modules (the chain test of 2026-10-13), hence the 35-minute cap."""

    LIMIT = 120
    BEFORE, SEED, MIDDLE, PACK = 4, 5, 60, 3  # minutes: worst cases of the real runs; MIDDLE = candidates, axioms, tags and the leak report
    CANARY = 3  # the canary (scripts/ci/canary/Canary.lean) after the library build: its own `timeout 3m`
    WORKFLOW = HERE.parent.parent.parent / ".github" / "workflows" / "queue-gate.yml"

    def test_the_restore_and_what_follows_fit_the_queue_limit(self):
        """Since the deltas (scripts/lake_cache.py) the queue no longer waits for a fresh cache: it restores what merged since the nightly, under its
        own cap. That cap takes the old wait's place in the budget."""
        text = self.WORKFLOW.read_text(encoding="utf-8")
        self.assertNotIn("cache_fresh.py", text, "the queue no longer refuses a stale cache: it restores the deltas instead")
        restores = re.findall(r"timeout -k \d+ (\d+)m python3 scripts/lake_cache\.py restore", text)
        caps = re.findall(r"timeout -k \d+ (\d+)m lake build Tengoku\.All", text)
        self.assertEqual((len(restores), len(caps)), (1, 1), "the restore step or the build's own cap was not found")
        restore, cap = int(restores[0]), int(caps[0])
        canary = re.findall(r"timeout -k \d+ (\d+)m lake env lean \"\$canary_src\"", text)
        self.assertEqual(len(canary), 1, "the canary step or its own cap was not found")
        self.assertLessEqual(int(canary[0]), self.CANARY, "the canary's cap is what the budget below allows for it")
        worst = self.BEFORE + restore + self.SEED + self.MIDDLE + cap + int(canary[0]) + self.PACK
        job = int(re.search(r"queue-build:.*?timeout-minutes: (\d+)", text, re.S).group(1))
        self.assertLessEqual(
            job, self.LIMIT, f"the job's own timeout ({job} min) must end before the queue gives up on the check ({self.LIMIT})"
        )
        self.assertLessEqual(worst, job, f"the steps can add up to {worst} min but the job is stopped at {job}")
        self.assertLessEqual(
            worst,
            self.LIMIT,
            f"restoring for up to {restore} min, then a build capped at {cap}, can take {worst} min of the queue's {self.LIMIT}",
        )


class CommitIds(unittest.TestCase):
    """2026-10-08 (Sonar S6350): the cache pointer is read from the network, and a commit from it was passed to `git fetch` and `git cat-file` as it came."""

    def setUp(self):
        sys.path.insert(0, str(HERE.parent))
        import cache_fresh

        self.cf = cache_fresh

    def test_only_forty_hex_digits_are_a_commit_id(self):
        good = "AbC1" * 10  # 40 hex digits in mixed case, built rather than written out: detect-secrets reads a long hex literal as a key
        self.assertEqual(self.cf.sha(good), good.lower())
        for bad in ("--upload-pack=touch /tmp/x", "-c", "abc123", good + "0", good[:-1], good[:-1] + "g", "", None, 5, ["a" * 40]):
            self.assertIsNone(self.cf.sha(bad), repr(bad))

    def test_a_pointer_value_that_is_not_a_commit_never_reaches_git(self):
        from unittest import mock

        hostile = "--upload-pack=touch /tmp/pwned"
        with mock.patch.object(self.cf.subprocess, "run") as run:
            self.assertFalse(self.cf.have(hostile))
            self.assertFalse(self.cf.is_ancestor(hostile, "a" * 40))
            self.assertFalse(self.cf.is_ancestor("a" * 40, hostile))
            self.assertEqual(self.cf.reference({"commit": hostile}, "a" * 40), None)
        run.assert_not_called()


class CacheFresh(unittest.TestCase):
    """The merge queue seeds from the newest published cache: cache_fresh.py lets a group on only when that cache is close enough to the base. Regression of
    2026-10-05: the seed moved (every module renamed), five approved PRs were queued before the rebuild published, and each would have recompiled the seed."""

    def history(self, added=0, renamed=0, deleted=0):
        """A repository whose `pr` branch is the base: `cache` is the commit the cache was built for, then `added` new modules, `renamed` modules moved into
        Tengoku/Seed/ and `deleted` removed ones (and a data file, which costs nothing to build)."""
        r = Repo()
        for i in range(renamed + deleted):
            r.write(f"Tengoku/Old/F{i}.lean", "module\n")
        r.write("cache-marker.txt", "the cache is for this commit\n")
        r.commit("the commit the cache was built for")
        r.git("checkout", "-q", "-B", "main")
        r.git("checkout", "-q", "-B", "pr")
        cache = r.git("rev-parse", "HEAD").strip()
        for i in range(added):
            r.write(f"Tengoku/New/F{i}.lean", "module\n")
        if renamed:
            (r.dir / "Tengoku" / "Seed").mkdir(parents=True)
        for i in range(renamed):
            r.git("mv", f"Tengoku/Old/F{i}.lean", f"Tengoku/Seed/F{i}.lean")
        for i in range(renamed, renamed + deleted):
            r.git("rm", "-q", f"Tengoku/Old/F{i}.lean")
        r.write("data/staging/x.jsonl", "{}\n")
        r.commit("the change since the cache")
        return r, cache

    def pointer(self, r, name, commit, topup=None):
        p = r.dir / f"{name}.json"
        p.write_text(json.dumps({"tag": f"cache-{name}", "commit": commit, **({"topup": {"commit": topup}} if topup else {})}))
        return str(p)

    def run_guard(self, r, files, *args, running="0", **env):
        return r.gate(
            "cache_fresh.py",
            "pr",
            *args,
            env={"TENGOKU_CACHE_POINTER_FILES": files, "TENGOKU_BUILDS_RUNNING": running, "TENGOKU_POLL_SECONDS": "0", **env},
        )

    def test_a_cache_for_the_base_is_fresh(self):
        r, cache = self.history()
        rc, out = self.run_guard(r, self.pointer(r, "a", r.git("rev-parse", "HEAD").strip()))
        self.assertEqual(rc, 0, out)
        self.assertIn("0 module(s) differ", out)

    def test_a_few_modules_behind_is_fine(self):
        r, cache = self.history(added=3)
        rc, out = self.run_guard(r, self.pointer(r, "a", cache), "--limit", "5")
        self.assertEqual(rc, 0, out)
        self.assertIn("3 module(s) differ", out)

    def test_a_restructure_since_the_cache_is_stale(self):
        r, cache = self.history(renamed=30)
        rc, out = self.run_guard(r, self.pointer(r, "a", cache), "--limit", "10")
        self.assertEqual(rc, 1, out)
        self.assertIn("30 modules behind", out)
        self.assertIn("No cache build is running", out)

    def test_it_waits_while_a_build_runs_and_goes_on_when_the_cache_catches_up(self):
        r, cache = self.history(renamed=30)
        old, new = self.pointer(r, "old", cache), self.pointer(r, "new", r.git("rev-parse", "HEAD").strip())
        rc, out = self.run_guard(r, f"{old}:{new}", "--limit", "10", "--wait", "1", running="1")
        self.assertEqual(rc, 0, out)
        self.assertIn("waiting", out)
        self.assertIn("cache fresh enough", out)

    def test_it_gives_up_when_the_time_is_up(self):
        r, cache = self.history(renamed=30)
        rc, out = self.run_guard(r, self.pointer(r, "a", cache), "--limit", "10", "--wait", "0", running="1")
        self.assertEqual(rc, 1, out)
        self.assertIn("A cache build is running", out)

    def test_a_promoted_topup_that_covers_the_change_makes_the_cache_fresh(self):
        r, cache = self.history(renamed=30)
        head = r.git("rev-parse", "HEAD").strip()
        rc, out = self.run_guard(r, self.pointer(r, "a", cache, topup=head), "--limit", "10")
        self.assertEqual(rc, 0, out)
        self.assertIn(head[:9], out)

    def test_a_topup_outside_the_bases_history_is_ignored(self):
        r, cache = self.history(renamed=30)
        r.git("checkout", "-q", "-b", "elsewhere", "main")
        r.write("other.txt", "x\n")
        r.commit("a commit that is not in the base's history")
        stray = r.git("rev-parse", "HEAD").strip()
        r.git("checkout", "-q", "pr")
        rc, out = self.run_guard(r, self.pointer(r, "a", cache, topup=stray), "--limit", "10")
        self.assertEqual(rc, 1, out)

    def test_removed_modules_and_other_files_cost_nothing_to_build(self):
        r, cache = self.history(deleted=40)
        rc, out = self.run_guard(r, self.pointer(r, "a", cache), "--limit", "5")
        self.assertEqual(rc, 0, out)
        self.assertIn("0 module(s) differ", out)

    def test_a_cache_outside_the_bases_history_is_not_judged(self):
        r, cache = self.history(added=50)
        r.git("checkout", "-q", "-b", "elsewhere", "main")
        r.write("other.txt", "x\n")
        r.commit("elsewhere")
        stray = r.git("rev-parse", "HEAD").strip()
        r.git("checkout", "-q", "pr")
        rc, out = self.run_guard(r, self.pointer(r, "a", stray), "--limit", "5")
        self.assertEqual(rc, 0, out)
        self.assertIn("nothing to judge", out)

    def test_an_unreadable_pointer_never_blocks_the_group(self):
        r, cache = self.history(added=50)
        rc, out = self.run_guard(r, str(r.dir / "missing.json"), "--limit", "5")
        self.assertEqual(rc, 0, out)
        self.assertIn("could not read the cache pointer", out)


if __name__ == "__main__":
    unittest.main()
