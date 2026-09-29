"""validate_records.py: at most ten headline records per PR, each crediting its author."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_gates import GOOD, Repo  # noqa: E402

CREDIT = "/-- What it says.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n"


def headline(i: int, credit: bool = True) -> str:
    rec = {**GOOD, "name": f"Lib.h{i}", "statement": (CREDIT if credit else "") + f"theorem Lib.h{i} : 1 + 1 = 2", "headline": True}
    return json.dumps(rec) + "\n"


class Headlines(unittest.TestCase):
    def test_ten_credited_headlines_pass(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", "".join(headline(i) for i in range(10)))
        r.commit("ten")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 0, out)

    def test_eleven_headlines_fail(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", "".join(headline(i) for i in range(11)))
        r.commit("eleven")
        rc, out = r.gate("validate_records.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("11 headline records; a PR names at most 10", out)

    def test_a_headline_without_a_credit_fails(self):
        r = Repo()
        r.append("data/staging/lib.jsonl", headline(0, credit=False))
        r.commit("uncredited")
        rc, out = r.gate("validate_records.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("a headline credits its author", out)

    def test_a_credit_outside_the_docstring_does_not_count(self):
        r = Repo()
        rec = {**GOOD, "name": "Lib.y", "statement": "theorem Lib.y : 1 + 1 = 2 -- Author: Ada", "headline": True}
        r.append("data/staging/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("comment credit")
        rc, out = r.gate("validate_records.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("a headline credits its author", out)

    def test_headline_must_be_a_boolean(self):
        r = Repo()
        rec = {**GOOD, "name": "Lib.x", "statement": CREDIT + "theorem Lib.x : 1 + 1 = 2", "headline": "yes"}
        r.append("data/staging/lib.jsonl", json.dumps(rec) + "\n")
        r.commit("string")
        rc, out = r.gate("validate_records.py")
        self.assertNotEqual(rc, 0)
        self.assertIn("headline must be boolean", out)

    def test_promotion_carries_headlines_into_trusted(self):
        r = Repo()
        lines = "".join(
            json.dumps({**json.loads(headline(i)), "status": "trusted", "promoted_at": "2026-01-02T00:00:00Z"}) + "\n" for i in range(12)
        )
        r.append("data/trusted/lib.jsonl", lines)
        r.commit("promotion")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 0, out)

    def test_records_without_headline_are_unaffected(self):
        r = Repo()
        r.append(
            "data/staging/lib.jsonl",
            "".join(json.dumps({**GOOD, "name": f"Lib.p{i}", "statement": f"theorem Lib.p{i} : 1 + 1 = 2"}) + "\n" for i in range(12)),
        )
        r.commit("plain")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main()
