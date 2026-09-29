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
        self.assertIn("credit is an `Author:` line", out)
        self.assertIn("evidence is an http(s) link", out)

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
