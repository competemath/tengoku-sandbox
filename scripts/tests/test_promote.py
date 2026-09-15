"""promote.py with staging split across the flat file and per-PR files (data/staging/<lib>/<x>.jsonl).
`lake` is a shim that always succeeds, so this checks the record bookkeeping, not Lean."""

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


def rec(name: str, src: str) -> dict:
    return {
        "name": name,
        "statement": f"theorem {name} : (1 : Nat) + 1 = 2",
        "proof": ":= rfl",
        "context": "",
        "source_path": src,
        "status": "staging",
        "library": "lib",
        "source_url": f"https://example.com/{src}",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "staged_at": "2026-01-01T00:00:00Z",
    }


class PromoteSplitStaging(unittest.TestCase):
    def test_records_from_both_files_are_trusted_and_the_per_pr_file_goes(self):
        out = Path(tempfile.mkdtemp())
        corpus = out / "corpus"
        (corpus / "lib").mkdir(parents=True)
        (corpus / "lib" / "A.lean").write_text("theorem seed : True := trivial\n")
        (corpus / "lib" / "B.lean").write_text("theorem seed2 : True := trivial\n")
        (out / "data" / "staging" / "lib").mkdir(parents=True)
        (out / "data" / "trusted").mkdir(parents=True)
        (out / "data" / "staging" / "lib.jsonl").write_text(json.dumps(rec("Lib.a1", "lib/A.lean")) + "\n")
        (out / "data" / "staging" / "lib" / "pr-7.jsonl").write_text(json.dumps(rec("Lib.b1", "lib/B.lean")) + "\n")
        (out / "data" / "trusted" / "lib.jsonl").write_text("")
        (out / "lakefile.toml").write_text('name = "Tengoku"\n')
        os.symlink(ROOT / "scripts", out / "scripts")  # promote.py runs scripts/generate.py from the tree root
        shim = out / "bin"
        shim.mkdir()
        (shim / "lake").write_text("#!/bin/sh\necho 'Build completed successfully.'\n")
        (shim / "lake").chmod(0o755)
        env = {**os.environ, "PATH": f"{shim}:{os.environ['PATH']}"}
        r = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "promote.py"), "--corpus", str(corpus), "--library", "lib", "--out", str(out)],
            capture_output=True,
            text=True,
            env=env,
            cwd=out,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        trusted = [json.loads(line) for line in (out / "data" / "trusted" / "lib.jsonl").read_text().splitlines() if line.strip()]
        self.assertEqual(sorted(t["name"] for t in trusted), ["Lib.a1", "Lib.b1"], r.stdout + r.stderr)
        self.assertTrue(all(t["status"] == "trusted" and t.get("promoted_at") for t in trusted))
        self.assertFalse(
            (out / "data" / "staging" / "lib" / "pr-7.jsonl").exists(), "per-PR file should be removed once its records are trusted"
        )
        self.assertEqual(
            (out / "data" / "staging" / "lib.jsonl").read_text().strip(), "", "flat staging file should be emptied, not deleted"
        )
        shutil.rmtree(out)


if __name__ == "__main__":
    unittest.main()
