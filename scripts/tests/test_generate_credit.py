"""A credit docstring at the top of a record's statement is written into the module directly above the theorem."""

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
DOC = "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/"


class GeneratedCredit(unittest.TestCase):
    def test_docstring_is_kept_with_the_theorem(self):
        out = Path(tempfile.mkdtemp())
        corpus = out / "corpus"
        (corpus / "lib").mkdir(parents=True)
        (corpus / "lib" / "A.lean").write_text("theorem seed : True := trivial\n")
        (out / "data" / "trusted").mkdir(parents=True)
        (out / "data" / "staging").mkdir(parents=True)
        (out / "data" / "trusted" / "lib.jsonl").write_text(
            json.dumps(
                {
                    "name": "Lib.credited",
                    "statement": DOC + "\ntheorem Lib.credited : (1 : Nat) + 1 = 2",
                    "proof": ":= rfl",
                    "context": "",
                    "source_path": "lib/A.lean",
                    "status": "trusted",
                    "library": "lib",
                    "source_url": "https://example.com/lib/A.lean",
                    "toolchain": "leanprover/lean4:v4.34.0-rc2",
                    "promoted_at": "2026-01-01T00:00:00Z",
                }
            )
            + "\n"
        )
        os.symlink(ROOT / "scripts", out / "scripts")
        r = subprocess.run(
            [sys.executable, "scripts/generate.py", "--corpus", str(corpus), "--libraries", "lib"],
            cwd=out,
            capture_output=True,
            text=True,
            env={**os.environ},
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        mod = (out / "Tengoku" / "Lib" / "A.lean").read_text()
        self.assertIn(DOC + "\ntheorem Lib.credited : (1 : Nat) + 1 = 2 := rfl", mod)  # the declaration as it stood
        shutil.rmtree(out)


if __name__ == "__main__":
    unittest.main()
