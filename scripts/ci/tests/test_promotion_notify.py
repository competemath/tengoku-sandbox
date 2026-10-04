"""promotion_notify.py: each contributor PR hears once which of its records a push made trusted."""

from __future__ import annotations

import json
import os
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_gates import GOOD, Repo  # noqa: E402


def rec(name: str, tier: str = "staging", compact: bool = False) -> str:
    r = {**GOOD, "name": name, "statement": f"theorem {name} : 1 + 1 = 2", "status": tier}
    if tier == "trusted":
        r["promoted_at"] = "2026-09-29T00:00:00Z"
    return (json.dumps(r, separators=(",", ":")) if compact else json.dumps(r)) + "\n"


def promote(r: Repo, names: list[str], subject: str):
    """As promote.py does: the records go to trusted and leave every staging file (a per-PR file left empty goes)."""
    r.append("data/trusted/lib.jsonl", "".join(rec(n, "trusted") for n in names))
    for f in [r.dir / "data/staging/lib.jsonl", *sorted((r.dir / "data/staging/lib").glob("*.jsonl"))]:
        if not f.exists():
            continue
        kept = [x for x in f.read_text().splitlines(keepends=True) if not any(f'"{n}"' in x for n in names)]
        if kept or f.name == "lib.jsonl":
            f.write_text("".join(kept))
        else:
            f.unlink()
    r.commit(subject)


class PromotionNotify(unittest.TestCase):
    def setUp(self):
        self.r = Repo()
        self.r.git("checkout", "-q", "main")
        self.base = self.r.git("rev-parse", "HEAD").strip()

    def notify(self, env=None):
        head = self.r.git("rev-parse", "HEAD").strip()
        return self.r.gate("promotion_notify.py", self.base, head, env={"TENGOKU_COMMENT_DRY": "1", **(env or {})})

    def test_each_pr_hears_once_across_the_push(self):
        r = self.r
        r.write("data/staging/lib/pr-12.jsonl", rec("Lib.a") + rec("Lib.b"))
        r.commit("Stage lib: 2 records (#12)")
        r.append("data/staging/lib.jsonl", rec("Lib.c", compact=True))  # another spelling of a record
        r.commit("Stage lib: 1 record (#13)")
        self.base = r.git("rev-parse", "HEAD").strip()
        promote(r, ["Lib.a"], "Promote: 1 record (#20)")
        promote(r, ["Lib.b", "Lib.c"], "Promote: 2 records (#21)")
        rc, out = self.notify()
        self.assertEqual(rc, 0, out)
        self.assertEqual(out.count("would comment on #12"), 1)
        self.assertIn("**2 of the records this PR added are now trusted** (promotion #20, #21): `Lib.a`, `Lib.b`", out)
        self.assertIn("would comment on #13", out)
        self.assertIn("**1 of the records this PR added is now trusted** (promotion #21): `Lib.c`", out)

    def test_a_record_added_to_the_flat_file_during_the_push_is_attributed(self):
        r = self.r
        r.append("data/staging/lib.jsonl", rec("Lib.a"))
        r.commit("Stage lib: 1 record (#13)")
        self.base = r.git("rev-parse", "HEAD").strip()
        promote(r, ["Lib.a"], "Promote: 1 record (#20)")  # reads the flat file's history as of here
        r.append("data/staging/lib.jsonl", rec("Lib.b"))
        r.commit("Stage lib: 1 record (#14)")  # later in the same push
        promote(r, ["Lib.b"], "Promote: 1 record (#21)")
        rc, out = self.notify()
        self.assertEqual(rc, 0, out)
        self.assertIn("would comment on #13", out)
        self.assertIn("would comment on #14", out)
        self.assertIn("(promotion #21): `Lib.b`", out)

    def test_a_record_without_a_pr_is_not_told(self):
        self.r.append("data/trusted/lib.jsonl", rec("Lib.z", "trusted"))
        self.r.commit("direct push")
        rc, out = self.notify()
        self.assertEqual(rc, 0, out)
        self.assertIn("no contributor PR to tell", out)

    def test_a_comment_that_fails_fails_the_job(self):
        r = self.r
        r.write("data/staging/lib/pr-12.jsonl", rec("Lib.a"))
        r.commit("Stage lib: 1 record (#12)")
        self.base = r.git("rev-parse", "HEAD").strip()
        promote(r, ["Lib.a"], "Promote: 1 record (#20)")
        shim = r.dir / "bin"
        shim.mkdir()
        (shim / "gh").write_text("#!/bin/sh\necho 'HTTP 403' >&2\nexit 1\n")
        (shim / "gh").chmod(0o755)
        head = r.git("rev-parse", "HEAD").strip()
        rc, out = r.gate("promotion_notify.py", self.base, head, env={"PATH": f"{shim}:{os.environ['PATH']}"})
        self.assertNotEqual(rc, 0)
        self.assertIn("could not tell #12", out)


if __name__ == "__main__":
    unittest.main()
