"""validate_records.py: tombstone categories, notes on where to look instead, and credit corrections."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_gates import Repo  # noqa: E402

T = "data/trusted/lib.jsonl"


def line(**kw) -> str:
    return json.dumps({"by": "t", "at": "2026-09-29", **kw}) + "\n"


class Retractions(unittest.TestCase):
    def check(self, r: Repo):
        return r.gate("validate_records.py")

    def test_a_tombstone_needs_a_known_category(self):
        r = Repo()
        r.append(T, line(tombstone="Lib.old", reason="wrong"))
        r.commit("no category")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("tombstone missing category", out)
        r.append(T, line(tombstone="Lib.old", category="mistaken", reason="wrong"))
        r.commit("bad category")
        rc, out = self.check(r)
        self.assertIn("category 'mistaken' is not one of", out)

    def test_a_tombstone_and_its_note_in_one_pr(self):
        r = Repo()
        r.append(T, line(tombstone="Lib.old", category="duplicate", reason="the same as Nat.two"))
        r.append(T, line(tombstone_note="Lib.old", note="follows from this", see=["tengoku:Nat.two"]))
        r.commit("retract with a pointer")
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)

    def test_a_tombstoned_name_written_with_escapes_matches_its_note(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.append(
            T,
            json.dumps(
                {
                    "name": "Lib.é",
                    "statement": "theorem Lib.é : True",
                    "proof": ":= trivial",
                    "status": "trusted",
                    "library": "lib",
                    "source_url": "https://github.com/leanprover-community/mathlib4/blob/x/y.lean",
                    "toolchain": "t",
                    "promoted_at": "2026-01-01T00:00:00Z",
                }
            )
            + "\n",
        )
        r.append(
            T, json.dumps({"tombstone": "Lib.é", "category": "incorrect", "reason": "r", "by": "t", "at": "2026-09-29"}) + "\n"
        )  # ascii-escaped
        r.commit("base")
        r.git("checkout", "-q", "-B", "pr")
        r.append(
            T, json.dumps({"tombstone_note": "Lib.é", "note": "see elsewhere", "by": "t", "at": "2026-09-29"}, ensure_ascii=False) + "\n"
        )
        r.commit("note")
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)

    def test_a_note_is_only_for_a_retracted_record(self):
        r = Repo()
        r.append(T, line(tombstone_note="Lib.old", note="look elsewhere"))
        r.commit("note without tombstone")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("has no tombstone", out)

    def test_a_note_can_be_replaced_by_a_newer_one(self):
        r = Repo()
        r.append(T, line(tombstone="Lib.old", category="superseded", reason="stronger version landed"))
        r.append(T, line(tombstone_note="Lib.old", note="see library A"))
        r.commit("first")
        r.git("checkout", "-q", "-B", "main")
        r.git("checkout", "-q", "-b", "pr2")
        r.append(T, line(tombstone_note="Lib.old", note="now see library B", see=["https://example.org/b"]))
        r.commit("newer note")
        rc, out = r.gate("validate_records.py", "main", "pr2")
        self.assertEqual(rc, 0, out)

    def test_a_credit_correction_needs_an_author_line_and_evidence(self):
        r = Repo()
        r.append(T, line(credit_correction="Lib.old", credit="Ada", evidence="not a link"))
        r.commit("bad correction")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("credit is one `Author:` line", out)
        self.assertIn("evidence is an http(s) link", out)

    def test_a_credit_correction_for_a_retracted_record_fails(self):
        r = Repo()
        r.append(T, line(tombstone="Lib.old", category="incorrect", reason="wrong"))
        r.append(T, line(credit_correction="Lib.old", credit="Author: Ada", evidence="https://example.org/e"))
        r.commit("correct a retracted record")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("Lib.old is retracted; a credit correction for it would have no effect", out)

    def test_a_credit_correction_names_one_author_line(self):
        for credit in ("Author: Alice\nAuthor: Mallory", "Author: Alice Author: Mallory"):
            r = Repo()
            r.append(T, line(credit_correction="Lib.old", credit=credit, evidence="https://example.org/e"))
            r.commit("two authors")
            rc, out = self.check(r)
            self.assertNotEqual(rc, 0, credit)
            self.assertIn("credit is one `Author:` line", out)

    def test_a_note_that_mentions_the_word_tombstone_is_checked_not_crashed(self):
        r = Repo()
        r.append(T, line(tombstone="Lib.old", category="duplicate", reason="same as x"))
        r.append(T, line(tombstone_note="Lib.old", note="the tombstone says why", see=["tombstone"]))
        r.commit("a note mentioning the word")
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)

    def test_a_note_finds_a_tombstone_in_a_per_library_file(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write("data/trusted/lib/pr-7.jsonl", line(tombstone="Lib.old", category="duplicate", reason="same as x"))
        r.commit("base: the tombstone in a per-library file")
        r.git("checkout", "-q", "-B", "pr")
        r.append(T, line(tombstone_note="Lib.old", note="see Nat.two", see=["tengoku:Nat.two"]))
        r.commit("note")
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)

    def test_a_tombstone_category_never_changes(self):
        r = Repo()
        r.git("checkout", "-q", "main")
        r.append(T, line(tombstone="Lib.old", category="duplicate", reason="same as x"))
        r.commit("base")
        r.git("checkout", "-q", "-B", "pr")
        r.append(T, line(tombstone="Lib.old", category="incorrect", reason="actually wrong"))
        r.commit("recategorise")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("already tombstoned as 'duplicate'", out)

    def test_a_correction_cannot_close_the_doc_comment(self):
        r = Repo()
        r.append(T, line(credit_correction="Lib.old", credit="Author: X", evidence="https://example.org/-/"))
        r.commit("delimiter")
        rc, out = self.check(r)
        self.assertNotEqual(rc, 0)
        self.assertIn("may not contain `-/`", out)

    def test_a_credit_correction_for_a_trusted_record_passes(self):
        r = Repo()
        r.append(
            T,
            line(
                credit_correction="Lib.old", credit="Author: Grace Hopper (https://example.org/gh)", evidence="https://example.org/evidence"
            ),
        )
        r.commit("correction")
        rc, out = self.check(r)
        self.assertEqual(rc, 0, out)
        self.assertEqual(r.gate("append_only.py")[0], 0)
        self.assertEqual(r.gate("credits.py")[0], 0)  # nothing removed: the record still says what it said


if __name__ == "__main__":
    unittest.main()
