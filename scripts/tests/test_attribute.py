"""Bulk attribution: where the credit goes, what is left alone, that a second run changes nothing."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "tools" / "attribute" / "attribute.py"
CREDIT = "Author: Ada Lovelace (https://github.com/ada), with Claude."


def run(d: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(TOOL), str(d), "--credit", CREDIT, *args], capture_output=True, text=True)


def project(files: dict[str, str | bytes]) -> Path:
    d = Path(tempfile.mkdtemp())
    for rel, text in files.items():
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(text, bytes):
            p.write_bytes(text)
        else:
            p.write_text(text, encoding="utf-8")
    return d


def credited(src: str, *args: str) -> tuple[str, subprocess.CompletedProcess]:
    d = project({"A.lean": src})
    r = run(d, *args)
    return (d / "A.lean").read_text(encoding="utf-8"), r


class Attribute(unittest.TestCase):
    def test_bare_declaration_gets_a_docstring_above_its_attributes(self):
        out, r = credited("open Nat in\n@[simp]\ntheorem foo : 1 = 1 := rfl\n")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(out, f"open Nat in\n/-- {CREDIT} -/\n@[simp]\ntheorem foo : 1 = 1 := rfl\n")

    def test_multi_line_attribute_stays_below_the_docstring(self):
        out, _ = credited("@[simp,\n  norm_cast]\nlemma foo : 1 = 1 := rfl\n")
        self.assertTrue(out.startswith(f"/-- {CREDIT} -/\n@[simp,\n  norm_cast]\nlemma foo"), out)

    def test_attribute_with_nested_brackets_and_a_string(self):
        src = '@[deprecated "use [x] instead" (since := "2026-01-01"),\n  simps (config := { attrs := [`simp] })]\ntheorem foo : 1 = 1 := rfl\n'
        out, _ = credited(src)
        self.assertEqual(out, f"/-- {CREDIT} -/\n" + src)

    def test_blank_and_comment_lines_inside_the_lead_in(self):
        out, _ = credited("@[simp]\n\n-- note\ntheorem foo : 1 = 1 := rfl\n\n/-- Doc. -/\n-- todo\ntheorem bar : 2 = 2 := rfl\n")
        self.assertEqual(
            out,
            f"/-- {CREDIT} -/\n@[simp]\n\n-- note\ntheorem foo : 1 = 1 := rfl\n\n/-- Doc.\n\n{CREDIT} -/\n-- todo\ntheorem bar : 2 = 2 := rfl\n",
        )

    def test_existing_docstring_gets_the_credit_as_its_last_line(self):
        out, _ = credited(
            "/-- One plus one. -/\ntheorem foo : 1 + 1 = 2 := rfl\n\n/-- Two.\nMore.\n-/\ndef two := 2\n\n/-- Three.\n\n-/\ndef three := 3\n"
        )
        self.assertEqual(
            out,
            f"/-- One plus one.\n\n{CREDIT} -/\ntheorem foo : 1 + 1 = 2 := rfl\n\n/-- Two.\nMore.\n\n{CREDIT}\n-/\ndef two := 2\n\n/-- Three.\n\n{CREDIT}\n-/\ndef three := 3\n",
        )

    def test_docstring_closing_on_the_declaration_line(self):
        out, _ = credited("/-- Doc.\nMore.\n-/ theorem foo : 1 = 1 := rfl\n\n/-- Doc.\nMore. -/ @[simp] theorem bar : 1 = 1 := rfl\n")
        self.assertEqual(
            out,
            f"/-- Doc.\nMore.\n\n{CREDIT}\n-/ theorem foo : 1 = 1 := rfl\n\n/-- Doc.\nMore.\n\n{CREDIT} -/ @[simp] theorem bar : 1 = 1 := rfl\n",
        )
        out2, r = credited(out)
        self.assertEqual(out2, out)
        self.assertIn("2 already carried this credit", r.stdout)

    def test_trailing_comments_after_docstrings_and_attributes(self):
        out, _ = credited(
            "/-- Doc. -/ -- todo\ntheorem foo : 1 = 1 := rfl\n\n@[simp] -- why\ntheorem bar : 1 = 1 := rfl\n\n/-- Doc. -/ @[simp,\n  norm_cast] -- why\ntheorem baz : 1 = 1 := rfl\n"
        )
        self.assertEqual(
            out,
            f"/-- Doc.\n\n{CREDIT} -/ -- todo\ntheorem foo : 1 = 1 := rfl\n\n/-- {CREDIT} -/\n@[simp] -- why\ntheorem bar : 1 = 1 := rfl\n\n"
            f"/-- Doc.\n\n{CREDIT} -/ @[simp,\n  norm_cast] -- why\ntheorem baz : 1 = 1 := rfl\n",
        )

    def test_docstring_line_carrying_the_attributes(self):
        out, _ = credited(
            "/-- Doc. -/ @[simp]\ntheorem foo : 1 = 1 := rfl\n\n/-- Doc.\nMore. -/ @[simp,\n  norm_cast]\ntheorem bar : 1 = 1 := rfl\n\n/- plain -/ @[simp]\ntheorem baz : 1 = 1 := rfl\n"
        )
        self.assertEqual(
            out,
            f"/-- Doc.\n\n{CREDIT} -/ @[simp]\ntheorem foo : 1 = 1 := rfl\n\n/-- Doc.\nMore.\n\n{CREDIT} -/ @[simp,\n  norm_cast]\ntheorem bar : 1 = 1 := rfl\n\n"
            f"/- plain -/\n/-- {CREDIT} -/\n@[simp]\ntheorem baz : 1 = 1 := rfl\n",
        )
        out2, r = credited(out)
        self.assertEqual(out2, out)
        self.assertIn("3 already carried this credit", r.stdout)

    def test_inline_docstring_and_indentation(self):
        out, _ = credited("mutual\n  /-- A. -/ theorem a : 1 = 1 := rfl\n  theorem b : 2 = 2 := rfl\nend\n")
        self.assertEqual(
            out, f"mutual\n  /-- A.\n\n  {CREDIT} -/ theorem a : 1 = 1 := rfl\n  /-- {CREDIT} -/\n  theorem b : 2 = 2 := rfl\nend\n"
        )

    def test_block_and_module_comments_above_are_not_docstrings(self):
        out, _ = credited(
            "/- notes -/\ntheorem foo : 1 = 1 := rfl\n\n/-! # Section\ntheorem inside : 1 = 1 := rfl\n-/\ntheorem bar : 2 = 2 := rfl\n"
        )
        self.assertEqual(
            out,
            f"/- notes -/\n/-- {CREDIT} -/\ntheorem foo : 1 = 1 := rfl\n\n/-! # Section\ntheorem inside : 1 = 1 := rfl\n-/\n/-- {CREDIT} -/\ntheorem bar : 2 = 2 := rfl\n",
        )

    def test_modifiers(self):
        src = "private\ntheorem a : 1 = 1 := rfl\nprotected noncomputable def b : Nat := 1\nscoped instance : Inhabited Nat := ⟨1⟩\nmeta def c : Nat := 1\n@[simp] private lemma d : 1 = 1 := rfl\n"
        out, _ = credited(src)
        self.assertEqual(
            out,
            f"/-- {CREDIT} -/\nprivate\ntheorem a : 1 = 1 := rfl\n/-- {CREDIT} -/\nprotected noncomputable def b : Nat := 1\n"
            f"/-- {CREDIT} -/\nscoped instance : Inhabited Nat := ⟨1⟩\n/-- {CREDIT} -/\nmeta def c : Nat := 1\n/-- {CREDIT} -/\n@[simp] private lemma d : 1 = 1 := rfl\n",
        )

    def test_second_run_changes_nothing(self):
        d = project({"A.lean": "/-- Doc. -/\ntheorem foo : 1 = 1 := rfl\ntheorem bar : 2 = 2 := rfl\n/-- D.\n-/ def baz := 1\n"})
        run(d)
        once = (d / "A.lean").read_text()
        r = run(d)
        self.assertEqual((d / "A.lean").read_text(), once)
        self.assertIn("credited 0 declarations in 1 files; 3 already carried this credit", r.stdout)

    def test_another_author_is_left_alone_and_listed(self):
        src = "/-- Theirs.\n\nAuthor: Someone Else. -/\ntheorem foo.{u} (α : Sort u) : α → α := id\n"
        out, r = credited(src)
        self.assertEqual(out, src)
        self.assertIn("names another author", r.stdout)
        self.assertIn("A.lean:4 foo", r.stdout)

    def test_comments_examples_and_lake_are_untouched(self):
        src = "/- theorem dead : 1 = 1 := rfl -/\n-- theorem gone : 1 = 1 := rfl\nexample : 1 = 1 := rfl\n/-- doc mentioning\ntheorem inside\n-/\n"
        d = project({"A.lean": src, ".lake/build/B.lean": "theorem cached : 1 = 1 := rfl\n"})
        r = run(d)
        self.assertEqual((d / "A.lean").read_text(), src)
        self.assertEqual((d / ".lake/build/B.lean").read_text(), "theorem cached : 1 = 1 := rfl\n")
        self.assertIn("credited 0 declarations in 1 files", r.stdout)

    def test_dry_run_and_kinds(self):
        src = "theorem foo : 1 = 1 := rfl\ndef two := 2\n"
        d = project({"A.lean": src})
        r = run(d, "--dry-run")
        self.assertEqual((d / "A.lean").read_text(), src)
        self.assertIn("would credit 2 declarations", r.stdout)
        run(d, "--kinds", "theorem")
        self.assertEqual((d / "A.lean").read_text(), f"/-- {CREDIT} -/\ntheorem foo : 1 = 1 := rfl\ndef two := 2\n")

    def test_crlf_and_non_utf8_files(self):
        d = project({"A.lean": "/-- Doc. -/\r\ntheorem foo : 1 = 1 := rfl\r\n", "B.lean": b"theorem \xff : 1 = 1 := rfl\n"})
        r = run(d)
        self.assertEqual((d / "A.lean").read_bytes(), f"/-- Doc.\r\n\r\n{CREDIT} -/\r\ntheorem foo : 1 = 1 := rfl\r\n".encode())
        self.assertEqual((d / "B.lean").read_bytes(), b"theorem \xff : 1 = 1 := rfl\n")
        self.assertIn("B.lean: not UTF-8, skipped", r.stderr)
        self.assertIn("credited 1 declarations in 1 files", r.stdout)

    def test_bad_credits_are_refused(self):
        d = project({"A.lean": "theorem foo : 1 = 1 := rfl\n"})
        for bad in ["Ada Lovelace", "Author: Ada -/ theorem"]:
            r = subprocess.run([sys.executable, str(TOOL), str(d), "--credit", bad], capture_output=True, text=True)
            self.assertNotEqual(r.returncode, 0)
        self.assertEqual((d / "A.lean").read_text(), "theorem foo : 1 = 1 := rfl\n")


if __name__ == "__main__":
    unittest.main()
