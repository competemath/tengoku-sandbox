"""Who may change the CI tests: the maintainer's second account only (.github/CODEOWNERS, last section).

The ruleset requires a code owner's approval; this pins WHO is the code owner of every test and every CI file. Without it, a new test directory, a renamed
workflow or a loosened pattern could leave a test owned by the main account, whose approval an agent could give. The files are found by what they are
(a test file, a workflow, a gate script), not by the patterns of CODEOWNERS, so a file the patterns forgot fails here.
"""

from __future__ import annotations

import re
import subprocess
import unittest
from pathlib import Path

TREE = Path(__file__).resolve().parents[3]
CODEOWNERS = TREE / ".github" / "CODEOWNERS"
SECOND = "@mikaelbashir14096545"
MAIN = "@mikael-bashir"
CONFIG = {
    ".pre-commit-config.yaml",
    ".secrets.baseline",
    ".coveragerc",
    "codecov.yml",
    "sonar-project.properties",
    "pyproject.toml",
    "schemas/allowed-options.json",
}
TEST_DIRS = {"tests", "test", "fuzz"}


def pattern_regex(pattern: str) -> re.Pattern[str]:
    """A CODEOWNERS pattern as a regex: anchored when it starts with / or has a / inside, otherwise it matches at any depth; `*` stays inside one path
    component, `**` crosses; a pattern that names a directory owns everything under it."""
    anchored = pattern.startswith("/") or "/" in pattern.rstrip("/")
    dir_only = pattern.endswith("/")  # a trailing slash limits the pattern to directories: a file directly under the matched level is not it
    body, i, out = pattern.strip("/"), 0, ""
    while i < len(body):
        if body.startswith("**", i):
            out, i = out + ".*", i + 2
        elif body[i] == "*":
            out, i = out + "[^/]*", i + 1
        elif body[i] == "?":
            out, i = out + "[^/]", i + 1
        else:
            out, i = out + re.escape(body[i]), i + 1
    return re.compile(("^" if anchored else "^(?:.*/)?") + out + ("/.+$" if dir_only else "(?:/.*)?$"))


def parse(text: str) -> list[tuple[re.Pattern[str], list[str]]]:
    rules = []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            pattern, *owners = line.split()
            rules.append((pattern_regex(pattern), owners))
    return rules


def owners_of(path: str, rules) -> list[str]:
    """The owners of the last rule that matches: later lines win."""
    found: list[str] = []
    for rx, owners in rules:
        if rx.match(path):
            found = owners
    return found


def is_ci_file(path: str) -> bool:
    """What the section must cover, decided from the file itself and not from CODEOWNERS."""
    parts = path.split("/")
    name = parts[-1]
    return (
        path.startswith(".github/")
        or path.startswith("scripts/ci/")
        or path.startswith("scripts/tests/")
        or path.startswith("tools/vacuity/")
        or path.startswith("tools/isnad/")
        or path.startswith(".clusterfuzzlite/")
        or path in CONFIG
        or bool(TEST_DIRS & set(parts[:-1]))
        or re.fullmatch(r"test_.*\.py|.*_test\.py|conftest\.py", name) is not None
    )


def repo_files() -> list[str]:
    out = subprocess.run(["git", "ls-files"], cwd=TREE, capture_output=True, text=True, check=True).stdout
    return [p for p in out.splitlines() if p and not p.startswith("Tengoku/")]  # the tree's own files are Lean, never CI


class Matcher(unittest.TestCase):
    def test_the_last_matching_line_wins(self):
        rules = parse("/scripts/ a b\n/scripts/ci/ c\n")
        self.assertEqual(owners_of("scripts/ci/x.py", rules), ["c"])
        self.assertEqual(owners_of("scripts/seed.py", rules), ["a", "b"])

    def test_anchoring_and_depth(self):
        rules = parse("/lakefile.toml a\ntest_*.py b\n/docs/*.md c\n")
        self.assertEqual(owners_of("lakefile.toml", rules), ["a"])
        self.assertEqual(owners_of("sub/lakefile.toml", rules), [])
        self.assertEqual(owners_of("x/y/test_z.py", rules), ["b"])
        self.assertEqual(owners_of("test_z.py", rules), ["b"])
        self.assertEqual(owners_of("docs/a.md", rules), ["c"])
        self.assertEqual(owners_of("docs/sub/a.md", rules), [])  # `*` stays inside one component

    def test_a_directory_owns_what_is_under_it(self):
        rules = parse("/.github/ a\n")
        self.assertEqual(owners_of(".github/workflows/x.yml", rules), ["a"])
        self.assertEqual(owners_of(".githubx/y", rules), [])

    def test_a_trailing_slash_limits_a_pattern_to_directories(self):
        rules = parse("/Tengoku/ a\n/Tengoku/*/\n")
        self.assertEqual(owners_of("Tengoku/Lib/X.lean", rules), [])
        self.assertEqual(owners_of("Tengoku/notes.txt", rules), ["a"])  # a top-level file is not a directory: the earlier line keeps it

    def test_no_match_is_no_owner(self):
        self.assertEqual(owners_of("data/staging/x.jsonl", parse("/scripts/ a\n")), [])


class OwnerOnly(unittest.TestCase):
    rules = parse(CODEOWNERS.read_text())

    def test_every_test_and_ci_file_is_owned_by_the_second_account_only(self):
        files = [p for p in repo_files() if is_ci_file(p)]
        self.assertGreater(len(files), 100, "the discovery found no CI files: this test would pass vacuously")
        wrong = {p: owners_of(p, self.rules) for p in files if owners_of(p, self.rules) != [SECOND]}
        self.assertEqual(
            wrong,
            {},
            "these tests or CI files are not owned by the second account alone (add them to the last section of .github/CODEOWNERS)",
        )

    def test_the_main_account_owns_none_of_them(self):
        for p in (p for p in repo_files() if is_ci_file(p)):
            self.assertNotIn(MAIN, owners_of(p, self.rules), p)

    def test_the_file_that_says_who_may_approve_is_itself_protected(self):
        self.assertEqual(owners_of(".github/CODEOWNERS", self.rules), [SECOND])

    def test_a_test_file_anywhere_is_covered_even_outside_the_known_directories(self):
        for p in (
            "anywhere/at/all/test_new.py",
            "x/conftest.py",
            "y/thing_test.py",
            "tools/vacuity/run.py",
            "scripts/ci/tests/new.py",
            ".github/workflows/new.yml",
        ):
            self.assertEqual(owners_of(p, self.rules), [SECOND], p)

    def test_the_content_lane_has_no_owner_and_the_machinery_of_the_tree_keeps_both(self):
        """The first part of a library edits Tengoku/All.lean (owned: a person reads it); everything a later part touches in the tree is the library's own folder and umbrella.
        Native is in the lane on purpose (the user counts novel proofs as content)."""
        both = [MAIN, SECOND]
        for p in (
            "Tengoku/Formalbook/FormalBook/Chapter_08.lean",
            "Tengoku/Formalbook.lean",
            "Tengoku/SomeNewLibrary/Deep/Module.lean",
            "Tengoku/SomeNewLibrary.lean",
            "Tengoku/Native/Competemath/X.lean",
            "Tengoku/Native.lean",
            "data/intake/formalbook/manifest.jsonl",
            "data/stats.json",
        ):
            self.assertEqual(owners_of(p, self.rules), [], p)
        for p in ("Tengoku/All.lean", "Tengoku/Seed/Logic/Basic.lean", "Tengoku.lean", "lean-toolchain", "scripts/seed.py"):
            self.assertEqual(owners_of(p, self.rules), both, p)

    def test_every_file_that_is_not_content_or_bot_data_is_owned_even_when_nobody_listed_it(self):
        """A review (2026-10-10) found machinery with no rule: the leak-scan, isnad and Jinshi roots, tools/*.py, .gitleaks.toml, the widget tree. The default line owns all of it, and anything new."""
        both = [MAIN, SECOND]
        for p in (
            "TengokuLeak.lean",
            "TengokuIsnad.lean",
            "TengokuJinshi.lean",
            "Jinshi/Base.lean",
            "tools/harvest.py",
            "tools/lean_extract.py",
            ".gitleaks.toml",
            "widget/js/x.js",
            "some/brand/new/tool.py",
            "Tengoku/notes.txt",  # a file directly under Tengoku/ is not a library folder
            "CONTRIBUTING.md",
            "LICENSE",
        ):
            self.assertEqual(owners_of(p, self.rules), both, p)

    def test_what_is_not_ci_keeps_both_owners_and_bot_paths_none(self):
        both = [MAIN, SECOND]
        for p in (
            "Tengoku/Seed/Logic/Basic.lean",
            "lakefile.toml",
            "scripts/seed.py",
            "schemas/sources.json",
            "data/trusted/x.jsonl",
            "Tengoku.lean",
        ):
            self.assertEqual(owners_of(p, self.rules), both, p)
        for p in ("data/staging/x.jsonl", "data/tentative/x.jsonl", "docs/testing.md", "README.md"):
            self.assertEqual(owners_of(p, self.rules), [], p)  # bot PRs and docs need no human owner


if __name__ == "__main__":
    unittest.main()
