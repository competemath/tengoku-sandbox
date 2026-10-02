"""cache.sh topup-gc: it retracts top-ups that are stale, and leaves everything that is not a top-up alone.

build.yml puts LICENSE, LICENSE-THIRD-PARTY.md and NOTICE on the standing `cache-topups` release (the licences
travel with the compiled code); gc used to delete any asset whose commit it could not find on main, which would have
retracted them within two hours. `gh` and `curl` are shims: the release's assets come from a file, deletions are logged.
"""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

CACHE = Path(__file__).resolve().parents[1] / "cache.sh"

GH_SHIM = """#!/usr/bin/env bash
case "$1 $2" in
  "auth status") exit 0 ;;
  "release delete-asset") echo "$4" >> "$SHIM_DIR/deleted"; exit 0 ;;
esac
if [ "$1" = api ]; then cat "$SHIM_DIR/assets"; exit 0; fi
exit 1
"""
CURL_SHIM = """#!/usr/bin/env bash
cat "$SHIM_DIR/pointer"
"""
OLD = "2026-01-01T00:00:00Z"


class TopupGc(unittest.TestCase):
    def run_gc(self, assets: list[str], current: str) -> set[str]:
        with tempfile.TemporaryDirectory() as d:
            bin_ = Path(d) / "bin"
            bin_.mkdir()
            for name, body in (("gh", GH_SHIM), ("curl", CURL_SHIM), ("zstd", "#!/usr/bin/env bash\nexit 0\n")):
                (bin_ / name).write_text(body)
                (bin_ / name).chmod(0o755)
            (Path(d) / "assets").write_text("".join(f"{a} {OLD}\n" for a in assets))
            (Path(d) / "pointer").write_text(json.dumps({"topup": {"commit": current}}))
            env = {
                **os.environ,
                "PATH": os.pathsep.join([str(bin_), os.environ["PATH"]]),
                "SHIM_DIR": d,
                "TENGOKU_TOPUP_GRACE_S": "0",
            }
            r = subprocess.run(["bash", str(CACHE), "topup-gc"], env=env, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            deleted = Path(d) / "deleted"
            return set(deleted.read_text().split()) if deleted.exists() else set()

    def test_stale_top_ups_are_retracted_the_current_one_and_the_licence_files_stay(self):
        cur, old = "b" * 40, "a" * 40
        deleted = self.run_gc(
            [
                f"topup-{old}.tar.zst",
                f"topup-{old}.json",
                f"topup-{cur}.tar.zst",
                f"topup-{cur}.json",
                "LICENSE",
                "LICENSE-THIRD-PARTY.md",
                "NOTICE",
            ],
            cur,
        )
        self.assertEqual(deleted, {f"topup-{old}.tar.zst", f"topup-{old}.json"})

    def test_nothing_but_licence_files_is_left_alone(self):
        self.assertEqual(self.run_gc(["LICENSE", "NOTICE", "LICENSE-THIRD-PARTY.md"], "c" * 40), set())


if __name__ == "__main__":
    unittest.main()
