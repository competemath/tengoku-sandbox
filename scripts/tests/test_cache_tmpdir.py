"""The cache is staged on the runner's work disk (RUNNER_TEMP), not in /tmp.

On ubuntu-26.04 runners /tmp is a 7.9 GB tmpfs with a quota and the cache is ~7 GB: `scripts/cache.sh get` died with
"write …/tengoku-cache.tar.zst.part-ab: disk quota exceeded" and the merge queue threw the PR out (competemath/tengoku#668).
"""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CACHE_SH = ROOT / "scripts" / "cache.sh"


class CacheSh(unittest.TestCase):
    def test_tmpdir_is_runner_temp_before_the_first_mktemp(self):
        text = CACHE_SH.read_text()
        export = 'export TMPDIR="${RUNNER_TEMP:-${TMPDIR:-/tmp}}"'
        self.assertIn(export, text)
        self.assertLess(text.index(export), text.index('="$(mktemp -d)"'), "TMPDIR is set before the first mktemp that is code")

    def _tmpdir_after_the_export(self, env):
        out = subprocess.run(
            ["bash", "-c", 'export TMPDIR="${RUNNER_TEMP:-${TMPDIR:-/tmp}}"; d="$(mktemp -d)"; echo "$d"; rmdir "$d"'],
            env={"PATH": os.environ["PATH"], **env},
            capture_output=True,
            text=True,
            check=True,
        )
        return out.stdout.strip()

    @unittest.skipUnless(sys.platform.startswith("linux"), "BSD mktemp (macOS) ignores TMPDIR; the runners are Linux")
    def test_mktemp_lands_under_runner_temp_when_there_is_one(self):
        with tempfile.TemporaryDirectory() as work:
            self.assertTrue(
                os.path.realpath(self._tmpdir_after_the_export({"RUNNER_TEMP": work})).startswith(os.path.realpath(work) + os.sep)
            )

    @unittest.skipUnless(sys.platform.startswith("linux"), "BSD mktemp (macOS) ignores TMPDIR; the runners are Linux")
    def test_without_runner_temp_it_is_what_it_was(self):
        with tempfile.TemporaryDirectory() as other:
            self.assertTrue(os.path.realpath(self._tmpdir_after_the_export({"TMPDIR": other})).startswith(os.path.realpath(other) + os.sep))


class LakeCachePy(unittest.TestCase):
    def test_tempfile_uses_runner_temp(self):
        with tempfile.TemporaryDirectory() as work:
            code = (
                "import importlib.util, tempfile, sys; "
                f"spec = importlib.util.spec_from_file_location('lake_cache', {str(ROOT / 'scripts' / 'lake_cache.py')!r}); "
                "m = importlib.util.module_from_spec(spec); sys.modules['lake_cache'] = m; spec.loader.exec_module(m); "
                "print(tempfile.gettempdir())"
            )
            out = subprocess.run(
                [sys.executable, "-c", code],
                env={"PATH": os.environ["PATH"], "RUNNER_TEMP": work},
                capture_output=True,
                text=True,
                check=True,
            )
            self.assertEqual(os.path.realpath(out.stdout.strip()), os.path.realpath(work))


if __name__ == "__main__":
    unittest.main()
