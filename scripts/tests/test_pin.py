"""pin.sh's decisions, with Lake and cache.sh replaced by shims (no Lean, no network).

A throwaway origin + clone; `lake` is a shim whose answers come from a plan file
("ok"/"fail" per call); `scripts/cache.sh` is a shim that records how it was called.
What is checked is what pin.sh does with those answers: where the checkout ends up,
what it asked the cache script for, and how it exits."""

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

REAL_PIN = Path(__file__).resolve().parents[1] / "pin.sh"

CACHE_SHIM = """#!/usr/bin/env bash
echo "cache.sh $* TOPUPS=${TENGOKU_TOPUPS:-} FORCE=${TENGOKU_FORCE:-0}" >> "$SHIM_LOG"
case "$1" in
  latest) if [ "${TENGOKU_TOPUPS:-0}" = 1 ]; then cat "$SHIM_DIR/latest-topup"; else cat "$SHIM_DIR/latest-base"; fi ;;
  latest-tag) echo cache-test ;;
  get) mkdir -p .lake/build/lib/lean/Tengoku && touch .lake/build/lib/lean/Tengoku/All.olean ;;
  topup-reapply) [ -f "$SHIM_DIR/reapply-fails" ] && exit 1; exit 0 ;;
  *) exit 0 ;;
esac
"""
TOPUP_SHIM = """import json, os, sys
print(json.dumps({"tip": open(os.environ["SHIM_DIR"] + "/applied").read().strip() or None}))
"""
LAKE_SHIM = """#!/usr/bin/env bash
plan="$SHIM_DIR/lake-plan"; first="$(head -n 1 "$plan" 2>/dev/null)"; [ -n "$first" ] && sed -i.bak 1d "$plan"
echo "lake $* -> ${first:-ok}" >> "$SHIM_LOG"
[ "${first:-ok}" = ok ]
"""


def git(cwd, *args):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


@unittest.skipUnless(shutil.which("git") and shutil.which("bash"), "git and bash needed")
class Pin(unittest.TestCase):
    def setUp(self):
        self.d = Path(tempfile.mkdtemp())
        origin, self.shim = self.d / "origin", self.d / "shim"
        self.shim.mkdir()
        origin.mkdir()
        git(origin, "init", "-q", "-b", "main")
        git(origin, "config", "user.email", "t@example.com")
        git(origin, "config", "user.name", "t")
        (origin / "scripts").mkdir()
        shutil.copy(REAL_PIN, origin / "scripts/pin.sh")
        (origin / "scripts/cache.sh").write_text(CACHE_SHIM)
        (origin / "scripts/topup.py").write_text(TOPUP_SHIM)
        os.chmod(origin / "scripts/cache.sh", 0o755)
        os.chmod(origin / "scripts/pin.sh", 0o755)
        (origin / "f").write_text("base\n")
        git(origin, "add", "-A")
        git(origin, "commit", "-q", "-m", "base")
        self.base = git(origin, "rev-parse", "HEAD")
        (origin / "f").write_text("tip\n")
        git(origin, "commit", "-q", "-am", "tip")
        self.tip = git(origin, "rev-parse", "HEAD")
        self.clone = self.d / "clone"
        git(self.d, "clone", "-q", str(origin), str(self.clone))
        (self.shim / "lake").write_text(LAKE_SHIM)
        os.chmod(self.shim / "lake", 0o755)
        (self.shim / "latest-base").write_text(self.base + "\n")
        (self.shim / "latest-topup").write_text(self.tip + "\n")
        (self.shim / "applied").write_text("")
        (self.shim / "log").write_text("")

    def pin(self, plan, topups="1", start=None):
        (self.shim / "lake-plan").write_text("".join(p + "\n" for p in plan))
        if start:
            git(self.clone, "checkout", "-q", "-f", start)
        env = {
            **os.environ,
            "PATH": f"{self.shim}:{os.environ['PATH']}",
            "SHIM_DIR": str(self.shim),
            "SHIM_LOG": str(self.shim / "log"),
            "TENGOKU_TOPUPS": topups,
        }
        env.pop("TENGOKU_PIN_FRESH", None)
        r = subprocess.run(["bash", "scripts/pin.sh"], cwd=self.clone, env=env, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr, (self.shim / "log").read_text(), git(self.clone, "rev-parse", "HEAD")

    def test_follows_the_topup_commit_when_asked(self):
        rc, out, log, head = self.pin(["ok"])
        self.assertEqual((rc, head), (0, self.tip), out)
        self.assertIn("--no-build", log)

    def test_without_the_switch_it_pins_to_the_nightly_cache(self):
        rc, out, log, head = self.pin(["ok"], topups="0")
        self.assertEqual((rc, head), (0, self.base), out)

    def test_a_failed_replay_unpacks_the_cache_again_once_before_anything_else(self):
        rc, out, log, head = self.pin(["fail", "ok"])
        self.assertEqual((rc, head), (0, self.tip), out)
        self.assertIn("cache.sh get TOPUPS=1 FORCE=1", log)

    def test_it_returns_to_the_state_it_came_from_and_exits_4(self):
        (self.shim / "applied").write_text("prevtopup\n")
        git(self.clone, "checkout", "-q", "-f", self.base)
        (self.clone / ".lake/build/lib/lean/Tengoku").mkdir(parents=True)
        (self.clone / ".lake/build/lib/lean/Tengoku/All.olean").write_text("x")
        rc, out, log, head = self.pin(["fail", "fail", "ok"])  # newest state fails twice; the previous one replays
        self.assertEqual((rc, head), (4, self.base), out)
        self.assertIn("cache.sh topup-reapply prevtopup", log)
        self.assertIn("kept", out)

    def test_with_nothing_to_return_to_it_falls_back_to_the_nightly_cache(self):
        rc, out, log, head = self.pin(["fail", "fail", "ok"])  # fresh clone: no build yet, so no previous state
        self.assertEqual((rc, head), (0, self.base), out)
        self.assertIn("cache.sh topup-rollback", log)
        self.assertIn("cache.sh get TOPUPS=0", log)

    def test_when_nothing_replays_it_fails_loudly_and_never_builds(self):
        rc, out, log, head = self.pin(["fail", "fail", "fail", "fail"])
        self.assertNotEqual(rc, 0, out)
        self.assertNotIn("lake build Tengoku.All ->", log.replace("lake build Tengoku.All --no-build ->", ""))

    def test_it_runs_the_newest_pin_sh_even_when_its_own_copy_is_old(self):
        git(self.clone, "checkout", "-q", "-f", self.base)
        (self.clone / "scripts/pin.sh").write_text(
            '#!/usr/bin/env bash\ncd "$(dirname "$0")/.."\nif [ -z "${TENGOKU_PIN_FRESH:-}" ]; then { git fetch -q origin main && git checkout -q origin/main -- scripts/pin.sh || true; TENGOKU_PIN_FRESH=1 exec scripts/pin.sh "$@"; }; fi\necho OLD; exit 9\n'
        )
        rc, out, log, head = self.pin(["ok"])
        self.assertEqual((rc, head), (0, self.tip), out)
        self.assertNotIn("OLD", out)


if __name__ == "__main__":
    unittest.main()
