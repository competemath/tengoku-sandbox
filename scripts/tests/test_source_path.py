"""safe_source_path: a record's source_path must name a file inside the corpus."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import generate  # noqa: E402


class SafeSourcePath(unittest.TestCase):
    def test_accepts_a_file_path(self):
        self.assertTrue(generate.safe_source_path("Lib/Sub/File.lean"))

    def test_refuses_paths_that_leave_the_corpus_or_name_a_directory(self):
        for sp in ["", ".", "A/.", "A/", "/etc/passwd", "../x", "A/../B", "A\\B", "-x", "~/x", "A\x00b", "A\x1fb", "A\x7fb"]:
            with self.subTest(sp=sp):
                self.assertFalse(generate.safe_source_path(sp))


if __name__ == "__main__":
    unittest.main()
