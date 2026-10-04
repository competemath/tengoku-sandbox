"""cache.sh's pointer(): the newest cache from cache-latest.json, downloaded as data and read by python3 from an
argument (never piped into it), with curl and gh replaced by shims (no network)."""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

CACHE = Path(__file__).resolve().parents[1] / "cache.sh"

CURL_SHIM = """#!/usr/bin/env bash
for a in "$@"; do case "$a" in *cache-latest.json) cat "$SHIM_DIR/pointer" 2>/dev/null; exit $?;; esac; done
exit 22
"""


class Pointer(unittest.TestCase):
    def run_cache(self, pointer: str | None, *args: str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as d:
            bin_ = Path(d) / "bin"
            bin_.mkdir()
            (bin_ / "curl").write_text(CURL_SHIM)
            (bin_ / "gh").write_text("#!/usr/bin/env bash\nexit 1\n")  # not logged in: cache.sh reads anonymously
            (bin_ / "zstd").write_text("#!/usr/bin/env bash\nexit 0\n")
            for f in bin_.iterdir():
                f.chmod(0o755)
            if pointer is not None:
                (Path(d) / "pointer").write_text(pointer)
            # the shims shadow the real curl and gh; everything else cache.sh needs is the system's
            env = {**os.environ, "PATH": os.pathsep.join([str(bin_), os.environ["PATH"]]), "SHIM_DIR": d, "TENGOKU_TOPUPS": "0"}
            return subprocess.run(["bash", str(CACHE), *args], env=env, capture_output=True, text=True)

    def test_the_pointer_names_the_newest_cache(self):
        p = json.dumps({"tag": "cache-20260930T0917Z", "commit": "a" * 40, "published_at": "2026-09-30T09:19:12Z", "parts": []})
        self.assertEqual(self.run_cache(p, "latest-tag").stdout.strip(), "cache-20260930T0917Z")
        self.assertEqual(self.run_cache(p, "latest").stdout.strip(), "a" * 40)

    def test_any_text_in_the_pointer_stays_data(self):
        tag = "cache-x'$(id>pwned)`id>pwned`\"y"  # quotes and substitutions: printed, never run (no spaces: fields)
        r = self.run_cache(json.dumps({"tag": tag, "commit": "b" * 40, "published_at": "t"}), "latest-tag")
        self.assertEqual(r.stdout.strip(), tag)
        self.assertFalse((CACHE.parents[1] / "pwned").exists())

    def test_no_pointer_or_a_broken_one_falls_back_to_the_release_list(self):
        for p in (None, "not json", json.dumps({"tag": "t"})):
            with self.subTest(p):
                r = self.run_cache(p, "latest-tag")  # the release list is unreachable too (curl fails): no cache
                self.assertEqual((r.returncode, r.stdout.strip()), (1, ""))
                self.assertIn("no published cache", r.stderr)


if __name__ == "__main__":
    unittest.main()
