"""validate_records.py: a statement correction replaces the text of a tentative record by moving text between its statement and its proof (or dropping it from the end), never by adding any.

The records are real: 543 tentative records of 13 libraries whose statement was cut too early by the extractor (tengoku#811), exactly as they are stored. A correction is built from
each by moving a few words of the proof into the statement, which is the shape of the real fix, and the whole set goes through the gate in one run.
"""

from __future__ import annotations

import gzip
import json
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_gates import CI, Repo  # noqa: E402

REAL = json.load(gzip.open(Path(__file__).parent / "fixtures" / "real-truncated-tentative-2026-11-13.json.gz", "rt", encoding="utf-8"))[
    "records"
]
P = "data/tentative/lib.jsonl"


def rec(r: dict) -> dict:
    return {
        "name": r["name"],
        "statement": r["statement"],
        "proof": r["proof"],
        "status": "tentative",
        "library": r["lib"],
        "source_url": "https://github.com/x/y/blob/z/a.lean#L1",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
    }


def move(r: dict, words: int = 3) -> tuple[str, str]:
    """The record's text with the first words of its proof moved into the statement: the same text, split later."""
    parts = re.split(r"(\s+)", r["proof"], maxsplit=2 * words)
    head = "".join(parts[: 2 * words])
    return r["statement"] + " " + head.strip(), "".join(parts[2 * words :]).lstrip()


def corr(name: str, statement: str, proof: str, **kw) -> dict:
    return {
        "statement_correction": name,
        "statement": statement,
        "proof": proof,
        "reason": "the statement ended at a let",
        "by": "t",
        "at": "2026-11-13",
        **kw,
    }


def lines(*rs: dict) -> str:
    return "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rs)


def movable() -> list[dict]:
    """Real records whose proof has more than a few words, so moving some of them changes the text."""
    return [r for r in REAL if len(r["proof"].split()) > 5]


class StatementCorrection(unittest.TestCase):
    def repo(self, recs: list[dict], tomb: list[str] = ()) -> Repo:
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write(
            P,
            lines(*map(rec, recs))
            + lines(*({"tombstone": n, "category": "duplicate", "reason": "x", "by": "t", "at": "2026-11-12"} for n in tomb)),
        )
        r.commit("tentative records")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "main")
        return r

    def run_gate(self, r: Repo, body: str):
        r.append(P, body)
        r.commit("correct")
        return r.gate("validate_records.py")

    def one(self):
        return movable()[0]

    def test_moving_words_from_the_proof_into_the_statement_is_accepted(self):
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s, p)))
        self.assertEqual(rc, 0, out)

    def test_all_real_records_at_once(self):
        """every movable real record's correction, over 13 per-library files in one PR, each accepted; the same run with one added word in each is refused once per record."""
        by = defaultdict(list)
        for x in REAL:
            if len(x["proof"].split()) > 5:
                by[x["lib"]].append(x)
        n = sum(len(v) for v in by.values())
        self.assertGreater(n, 300)
        r = Repo()
        r.git("checkout", "-q", "main")
        for lib, xs in by.items():
            r.write(f"data/tentative/{lib}.jsonl", lines(*map(rec, xs)))
        r.commit("tentative records")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "main")
        for lib, xs in by.items():
            r.append(f"data/tentative/{lib}.jsonl", lines(*(corr(x["name"], *move(x)) for x in xs)))
        r.commit("correct")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 0, out)
        r.git("reset", "-q", "--hard", "HEAD~1")
        for lib, xs in by.items():
            r.append(f"data/tentative/{lib}.jsonl", lines(*(corr(x["name"], x["statement"], x["proof"] + " extra") for x in xs)))
        r.commit("add a word")
        rc, out = r.gate("validate_records.py")
        self.assertNotEqual(rc, 0)
        shown = out.count("with the seam between them moved")
        more = re.search(r"… (\d+) more", out)
        self.assertEqual(shown + int(more.group(1)), n, out[:600])  # the gate prints 25 and counts the rest
        self.assertEqual(len(by), 13)

    def test_a_correction_may_drop_text_from_the_end(self):
        x = self.one()
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], x["statement"], x["proof"][: len(x["proof"]) // 2])))
        self.assertEqual(rc, 0, out)

    def test_whitespace_may_differ_at_the_seam_only(self):
        """The seam between the fields is where the extractor strips whitespace: more or less of it there is the same text."""
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s + "\n\n  ", "   " + p)))
        self.assertEqual(rc, 0, out)

    def test_whitespace_inside_a_field_is_text(self):
        """`(a b : N)` is not `(ab : N)`, and a newline ends a `--` comment (gitar on #815): a space or newline added, removed or changed inside a field is refused, in each field."""
        x = next(r for r in movable() if " " in r["statement"] and len(r["proof"].split()) > 8)
        s, p = move(x)
        i = s.index(" ")
        j = p.index(" ")
        edits = {
            "joined tokens in the statement": (s[:i] + s[i + 1 :], p),
            "doubled space in the statement": (s.replace(" ", "  ", 1), p),
            "space made a newline in the statement": (s[:i] + "\n" + s[i + 1 :], p),
            "joined tokens in the proof": (s, p[:j] + p[j + 1 :]),
            "space made a newline in the proof": (s, p[:j] + "\n" + p[j + 1 :]),
            "whitespace between a comment and the next line": (s.replace(" ", " -- c ", 1), p),
        }
        for what, (cs, cp) in edits.items():
            rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], cs, cp)))
            self.assertNotEqual(rc, 0, what)
            self.assertIn("with the seam between them moved", out, what)

    def test_a_record_already_trusted_is_refused(self):
        x = self.one()
        s, p = move(x)
        r = self.repo(
            [{**x, "name": "Lib.old", "statement": "theorem Lib.old : 1 + 1 = 2 " + x["statement"]}]
        )  # trusted in the base: Lib.old
        rc, out = self.run_gate(r, lines(corr("Lib.old", "theorem Lib.old : 1 + 1 = 2 " + s, p)))
        self.assertNotEqual(rc, 0)
        self.assertIn("is already trusted", out)

    def test_adding_text_is_refused(self):
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s, p + " sorry")))
        self.assertNotEqual(rc, 0)
        self.assertIn("with the seam between them moved", out)

    def test_changing_a_word_is_refused(self):
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s.replace("theorem", "lemma", 1), p)))
        self.assertNotEqual(rc, 0)
        self.assertIn("with the seam between them moved", out)

    def test_a_statement_that_is_not_a_prefix_of_the_old_nor_the_old_of_it_is_refused(self):
        x = self.one()
        rc, out = self.run_gate(
            self.repo([x]), lines(corr(x["name"], x["name"].rsplit(".", 1)[-1] + " :=", x["statement"] + " " + x["proof"]))
        )
        self.assertNotEqual(rc, 0)
        self.assertIn("one a prefix of the other", out)

    def test_an_unknown_name_is_refused(self):
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr("Lib.nothing", s, p)))
        self.assertNotEqual(rc, 0)
        self.assertIn("no record of this file", out)

    def test_a_record_of_another_file_is_refused(self):
        x, y = movable()[0], next(r for r in movable() if r["lib"] != movable()[0]["lib"])
        r = self.repo([x])
        r.git("checkout", "-q", "main")
        r.write("data/tentative/other.jsonl", lines(rec(y)))
        r.commit("other file")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "main")
        s, p = move(y)
        r.append("data/tentative/other.jsonl", lines(corr(y["name"], s, p)))
        r.commit("its own file")
        rc, out = r.gate("validate_records.py")
        self.assertEqual(rc, 0, out)
        r.append(P, lines(corr(y["name"], s, p)))
        r.commit("wrong file")
        rc, out = r.gate("validate_records.py")
        self.assertIn("no record of this file", out)

    def test_staging_and_trusted_are_refused(self):
        x = self.one()
        s, p = move(x)
        for tier, name in (("staging", "Lib.good"), ("trusted", "Lib.old")):
            r = Repo()
            r.append(f"data/{tier}/lib.jsonl", lines(corr(name, s, p)))
            r.commit("correct")
            rc, out = r.gate("validate_records.py")
            self.assertNotEqual(rc, 0, tier)
            self.assertIn("goes in data/tentative/", out)

    def test_a_retracted_record_is_refused(self):
        x = self.one()
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x], tomb=[x["name"]]), lines(corr(x["name"], s, p)))
        self.assertNotEqual(rc, 0)
        self.assertIn("is retracted", out)

    def test_a_correction_that_changes_nothing_is_refused(self):
        x = self.one()
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], x["statement"], x["proof"])))
        self.assertNotEqual(rc, 0)
        self.assertIn("changes nothing", out)

    def test_two_corrections_of_a_name_in_one_pr_are_refused(self):
        x = self.one()
        s, p = move(x, 2)
        s2, p2 = move(x, 4)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s, p), corr(x["name"], s2, p2)))
        self.assertNotEqual(rc, 0)
        self.assertIn("a second statement_correction", out)

    def test_the_newest_correction_of_an_earlier_pr_is_the_text_to_correct(self):
        x = self.one()
        s, p = move(x, 2)
        r = self.repo([x])
        r.git("checkout", "-q", "main")
        r.append(P, lines(corr(x["name"], s, p)))
        r.commit("first correction, merged")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "main")
        s2, p2 = move(x, 4)
        rc, out = self.run_gate(r, lines(corr(x["name"], s2, p2)))
        self.assertEqual(rc, 0, out)
        r.git("reset", "-q", "--hard", "HEAD~1")
        rc, out = self.run_gate(r, lines(corr(x["name"], x["statement"], x["proof"] + " more")))
        self.assertNotEqual(rc, 0)
        self.assertIn("with the seam between them moved", out)

    def test_missing_fields_and_a_bad_date(self):
        x = self.one()
        s, p = move(x)
        for k in ("reason", "by", "at", "proof"):
            c = corr(x["name"], s, p)
            del c[k]
            rc, out = self.run_gate(self.repo([x]), lines(c))
            self.assertNotEqual(rc, 0, k)
            self.assertIn(f"statement_correction missing {k}", out)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s, p, at="yesterday")))
        self.assertIn("at is a UTC date", out)

    def test_the_reason_is_one_short_line(self):
        x = self.one()
        s, p = move(x)
        for reason in ("a\nb", "x" * 301, "  "):
            rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s, p, reason=reason)))
            self.assertNotEqual(rc, 0, repr(reason[:5]))
            self.assertIn("reason is one line of at most 300", out)

    def test_the_statement_must_declare_the_name(self):
        x = self.one()
        last = x["name"].rsplit(".", 1)[-1]
        s, p = move(x)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], s.replace(last, "other_name"), p)))
        self.assertNotEqual(rc, 0)
        self.assertIn("does not declare", out)

    def test_the_name_must_be_a_string_and_the_statement_not_empty(self):
        x = self.one()
        rc, out = self.run_gate(self.repo([x]), lines(corr(["a"], "t", "p")))
        self.assertIn("is the name of a record (a string)", out)
        rc, out = self.run_gate(self.repo([x]), lines(corr(x["name"], " ", "p")))
        self.assertIn("the statement not empty", out)

    def test_a_record_line_still_follows_the_ordinary_rules(self):
        x = self.one()
        bad = {**rec(x), "name": "Lib.dup"}
        r = self.repo([x])
        rc, out = self.run_gate(r, lines(bad, bad))
        self.assertNotEqual(rc, 0)


class Mutants(unittest.TestCase):
    """The gate with one rule taken out lets a real bad correction through: each rule is tested by something."""

    def mutated(self, old: str, new: str) -> Path:
        d = Path(tempfile.mkdtemp())
        shutil.copytree(CI, d / "ci", ignore=shutil.ignore_patterns("__pycache__", "tests", "fuzz"))
        f = d / "ci" / "validate_records.py"
        s = f.read_text(encoding="utf-8")
        self.assertEqual(s.count(old), 1, old)
        f.write_text(s.replace(old, new), encoding="utf-8")
        self.addCleanup(shutil.rmtree, d, ignore_errors=True)
        return f

    def run_with(self, script: Path, r: Repo):
        p = subprocess.run(
            [sys.executable, str(script), "main", "pr"],
            cwd=r.dir,
            capture_output=True,
            text=True,
            env={**__import__("os").environ, "TENGOKU_CI_ROOT": str(r.dir)},
        )
        return p.returncode, p.stdout + p.stderr

    def case(self, body_for, tomb=False, pick=None):
        x = pick or movable()[0]
        r = StatementCorrection().repo([x], tomb=[x["name"]] if tomb else [])
        r.append(P, body_for(x))
        r.commit("c")
        return r

    def test_without_the_prefix_rule_added_text_passes(self):
        r = self.case(lambda x: lines(corr(x["name"], *move(x)[:1], move(x)[1] + " sorry")))
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated("if not moves_only(old_stmt, old_proof, stmt, proof):", "if False:")
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_with_whitespace_ignored_a_joined_token_passes(self):
        """The first version (squash: delete all whitespace before comparing) let `(a b : N)` become `(ab : N)`."""
        x = next(r for r in movable() if len(r["proof"].split()) > 8)
        s, p = move(x)
        j = p.index(" ")
        r = self.case(lambda _: lines(corr(x["name"], s, p[:j] + p[j + 1 :])), pick=x)
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated(
            "if not moves_only(old_stmt, old_proof, stmt, proof):",
            'if not "".join((old_stmt + old_proof).split()).startswith("".join((stmt + proof).split())):',
        )
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_without_the_trusted_rule_a_promoted_record_passes(self):
        x = movable()[0]
        base = {**x, "name": "Lib.old", "statement": "theorem Lib.old : 1 + 1 = 2 " + x["statement"]}
        r = StatementCorrection().repo([base])
        r.append(P, lines(corr("Lib.old", "theorem Lib.old : 1 + 1 = 2 " + move(x)[0], move(x)[1])))
        r.commit("c")
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated("if n in trusted_names():", "if False:")
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_without_the_tombstone_rule_a_retracted_record_passes(self):
        r = self.case(lambda x: lines(corr(x["name"], *move(x))), tomb=True)
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated('if n in f["tombstoned"]:', "if False:")
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_without_the_one_per_pr_rule_two_pass(self):
        r = self.case(lambda x: lines(corr(x["name"], *move(x, 2)), corr(x["name"], *move(x, 4))))
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated('if n in f["corrected"]:', "if False:")
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_without_the_tier_rule_a_staging_correction_passes(self):
        x = movable()[0]
        r = Repo()
        r.append("data/staging/lib.jsonl", lines(corr("Lib.good", *move(x))))
        r.commit("c")
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated('if t != "tentative":', "if False:")
        self.assertNotIn("goes in data/tentative/", self.run_with(m, r)[1])

    def test_without_the_no_op_rule_a_no_change_passes(self):
        r = self.case(lambda x: lines(corr(x["name"], x["statement"], x["proof"])))
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated("if (stmt, proof) == (old_stmt, old_proof):", "if False:")
        self.assertEqual(self.run_with(m, r)[0], 0)

    def test_without_the_unknown_name_rule_it_cannot_be_read(self):
        r = self.case(lambda x: lines(corr("Lib.nothing", *move(x))))
        self.assertNotEqual(r.gate("validate_records.py")[0], 0)
        m = self.mutated('if n not in f["texts"]:', "if False:")
        self.assertNotEqual(self.run_with(m, r)[0], 0)  # it fails differently (a missing key), still a failure, not a pass of the rule

    def test_without_the_statement_prefix_rule_a_rewritten_statement_passes(self):
        r = self.case(lambda x: lines(corr(x["name"], x["name"].rsplit(".", 1)[-1] + " :=", x["statement"] + " " + x["proof"])))
        self.assertIn("one a prefix of the other", r.gate("validate_records.py")[1])
        m = self.mutated("if not (a.startswith(b) or b.startswith(a)):", "if False:")
        self.assertNotIn("one a prefix of the other", self.run_with(m, r)[1])


class CampaignScenarios(unittest.TestCase):
    """scripts/ci/campaign/gate.sh builds its correction scenarios with a helper; here it is run on real tentative records of this tree and its output goes through the gate, so the scenarios mean what their labels say."""

    GATE = CI / "campaign" / "gate.sh"

    def helper(self) -> str:
        m = re.search(r"correct\(\) \{.*?<<'PY'\n(.*?)\nPY\n", self.GATE.read_text(encoding="utf-8"), re.S)
        self.assertIsNotNone(m)
        return m.group(1)

    def real_file(self) -> str:
        """The lines of a real tentative file of this tree with at least one record the helper can use (empty when the tree has no data)."""
        for p in sorted((CI.parents[1] / "data" / "tentative").glob("*.jsonl")):
            out = []
            for line in p.read_text(encoding="utf-8").splitlines():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                pr = r.get("proof")
                if (
                    isinstance(pr, str)
                    and len(pr.split()) >= 4
                    and "  " not in pr
                    and "\n" not in pr
                    and r.get("name", "~").rsplit(".", 1)[-1] in r.get("statement", "")
                ):
                    out.append(line)
                    if len(out) == 3:
                        return "\n".join(out) + "\n"
        return ""

    def run_mode(self, mode: str):
        text = self.real_file()
        if not text:
            self.skipTest("this checkout has no tentative data")
        r = Repo()
        r.git("checkout", "-q", "main")
        r.write(P, text)
        r.commit("real tentative records")
        r.git("checkout", "-q", "pr")
        r.git("merge", "-q", "main")
        p = subprocess.run([sys.executable, "-", mode], input=self.helper(), cwd=r.dir, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        r.commit("scenario")
        return r.gate("validate_records.py")

    def test_cut_passes(self):
        rc, out = self.run_mode("cut")
        self.assertEqual(rc, 0, out)

    def test_the_others_are_refused_by_the_record_rules(self):
        for mode, msg in (
            ("add", "with the seam between them moved"),
            ("space", "with the seam between them moved"),
            ("unknown", "no record of this file"),
        ):
            rc, out = self.run_mode(mode)
            self.assertNotEqual(rc, 0, mode)
            self.assertIn(msg, out, mode)


if __name__ == "__main__":
    unittest.main()
