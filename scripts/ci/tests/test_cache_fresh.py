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
    """The wait comes out of the queue's 40-minute check, with everything after it still to run (CodeRabbit, 2026-10-05: a 25-minute wait left 15 minutes for a seed
    of up to 4, candidates and axioms of up to 6, a build capped at 20 and a pack of 2). The durations are those of the real queue runs of 2026-10-05
    (seed 133 to 219 s, candidates 96 s, axioms 201 s, build 56 to 103 s, checkout and disk 150 to 170 s)."""

    LIMIT = 40
    BEFORE, SEED, CANDIDATES, PACK = 3, 4, 6, 2  # minutes, worst cases of the real runs
    WORKFLOW = HERE.parent.parent.parent / ".github" / "workflows" / "queue-gate.yml"

    def test_the_wait_and_what_follows_fit_the_queue_limit(self):
        text = self.WORKFLOW.read_text(encoding="utf-8")
        waits = re.findall(r"cache_fresh\.py \"\$BASE\" --wait (\d+)", text)
        caps = re.findall(r"timeout -k \d+ (\d+)m lake build Tengoku\.All", text)
        self.assertEqual((len(waits), len(caps)), (1, 1), "the step or the build's own cap was not found")
        wait, cap = int(waits[0]), int(caps[0])
        worst = self.BEFORE + wait + self.SEED + self.CANDIDATES + cap + self.PACK
        self.assertLessEqual(
            worst, self.LIMIT, f"waiting {wait} min, then a build capped at {cap}, can take {worst} min of the queue's {self.LIMIT}"
        )


class CommitIds(unittest.TestCase):
    """2026-10-08 (Sonar S6350): the cache pointer is read from the network, and a commit from it was passed to `git fetch` and `git cat-file` as it came."""

    def setUp(self):
        sys.path.insert(0, str(HERE.parent))
        import cache_fresh

        self.cf = cache_fresh

    def test_only_forty_hex_digits_are_a_commit_id(self):
        good = "0123456789abcdef0123456789ABCDEF01234567"
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
