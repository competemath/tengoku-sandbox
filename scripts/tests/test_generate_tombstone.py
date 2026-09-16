"""A tombstone in a trusted file removes the record from the generated module and from candidates."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def rec(name: str, status: str = "trusted") -> dict:
    return {
        "name": name,
        "statement": f"theorem {name} : (1 : Nat) + 1 = 2",
        "proof": ":= rfl",
        "context": "",
        "source_path": "lib/A.lean",
        "status": status,
        "library": "lib",
        "source_url": "https://example.com/lib/A.lean",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "promoted_at": "2026-01-01T00:00:00Z",
    }


class Tombstones(unittest.TestCase):
    def test_retracted_record_is_dropped(self):
        out = Path(tempfile.mkdtemp())
        corpus = out / "corpus"
        (corpus / "lib").mkdir(parents=True)
        (corpus / "lib" / "A.lean").write_text("theorem seed : True := trivial\n")
        (out / "data" / "trusted").mkdir(parents=True)
        (out / "data" / "staging").mkdir(parents=True)
        (out / "data" / "trusted" / "lib.jsonl").write_text(
            json.dumps(rec("Lib.keep"))
            + "\n"
            + json.dumps(rec("Lib.bad"))
            + "\n"
            + json.dumps({"tombstone": "Lib.bad", "reason": "test", "by": "t", "at": "2026-01-02T00:00:00Z"})
            + "\n"
        )
        (out / "data" / "staging" / "lib.jsonl").write_text(
            json.dumps(rec("Lib.bad", "staging")) + "\n"
        )  # re-staged under a retracted name: still dropped
        os.symlink(ROOT / "scripts", out / "scripts")
        env = {**os.environ}
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib"],
            cwd=out,
            capture_output=True,
            text=True,
            env=env,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        mod = (out / "Tengoku" / "Lib" / "A.lean").read_text()
        self.assertIn("Lib.keep", mod)
        self.assertNotIn("Lib.bad", mod)
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib", "--candidate", "lib/A.lean"],
            cwd=out,
            capture_output=True,
            text=True,
            env=env,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        cand = (out / "Tengoku" / "Lib" / "_candidate_A.lean").read_text()
        self.assertNotIn("Lib.bad", cand)
        shutil.rmtree(out)


if __name__ == "__main__":
    unittest.main()
