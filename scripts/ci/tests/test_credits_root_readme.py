"""credits.py: the root README.md is prose about the project, not a file of credits, and is exempt; every other Markdown file is not.

Regression (2026-10-14, tengoku#559): a rewrite of the README's Contributors section dropped the sentence that explains the `Author:` convention
and the gate refused it as a removed credit. The exemption is for exactly one path: a README.md anywhere else (a library's, a folder's) is covered,
and a credit line that is moved INTO the root README is not kept (an exempt file is no home for a credit)."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import Repo  # noqa: E402

LINE = "line starting `Author:` that names you, and any AI you used. [How credit works](docs/credit.md) ·\n"


def repo(path: str) -> Repo:
    r = Repo()
    r.write(path, "# t\n\nEvery theorem keeps its author's credit: put a docstring above it with one\n" + LINE + "\nmore\n")
    r.commit("a file that carries the credit sentence")
    return r


def credits(r: Repo):
    return r.gate("credits.py", "pr~1", "pr")


class RootReadme(unittest.TestCase):
    def test_the_root_readme_may_lose_a_line_that_names_the_author_marker(self):
        r = repo("README.md")
        r.write("README.md", "# t\n\nA shorter text.\n")
        r.commit("rewrite the README")
        rc, out = credits(r)
        self.assertEqual(rc, 0, out)

    def test_any_other_readme_is_covered(self):
        for path in ("docs/README.md", "Tengoku/Flt/README.md", "data/README.md", "readme.md.bak.md"):
            with self.subTest(path=path):
                r = repo(path)
                r.write(path, "# t\n\nA shorter text.\n")
                r.commit("rewrite it")
                rc, out = credits(r)
                self.assertEqual(rc, 1, (path, out))
                self.assertIn("Author:", out)

    def test_other_markdown_files_are_covered(self):
        r = repo("docs/credit.md")
        r.write("docs/credit.md", "# t\n")
        r.commit("drop it")
        self.assertEqual(credits(r)[0], 1)

    def test_a_credit_line_moved_into_the_root_readme_is_not_kept(self):
        r = repo("docs/credit.md")
        r.write("docs/credit.md", "# t\n")
        r.write("README.md", "# t\n\n" + LINE)
        r.commit("move it into the exempt README")
        rc, out = credits(r)
        self.assertEqual(rc, 1, out)
        self.assertIn("Author:", out)


if __name__ == "__main__":
    unittest.main()
