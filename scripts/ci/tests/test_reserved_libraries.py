"""Library keys whose folder is not a library's (Tengoku/Seed/ holds the seeded code, Tengoku/Native/ is kept for a later folder) are refused
wherever the gates learn a key: a library there would be generated over that folder, and its prefix would make the folder "derived"."""

from __future__ import annotations

import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
CI = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(CI))
import _git  # noqa: E402
from test_gates import GOOD, Repo  # noqa: E402

RESERVED = ["seed", "Seed", "SEED", "se-ed", "-seed", "native", "Native", "na_tive"]
FINE = ["lib", "equational-theories", "mathlib", "seeded", "seed-lib", "a-seed", "nativex", "seed2"]


def refused(call, *args) -> str:
    """The message of the gate failure `call(*args)` ends in; fails the test when it does not."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            call(*args)
        except SystemExit:
            return buf.getvalue()
    raise AssertionError(f"{call.__name__}{args} was not refused")


class Keys(unittest.TestCase):
    def test_a_reserved_key_is_refused_however_it_is_spelled(self):
        for key in RESERVED:
            with self.subTest(key):
                out = refused(_git.check_key, key)
                self.assertIn("reserved", out)
                self.assertIn(f"Tengoku/{_git._pascal(key)}/", out)

    def test_other_keys_are_not(self):
        for key in FINE:
            with self.subTest(key):
                self.assertEqual(_git.check_key(key), key)
                self.assertEqual(_git.pascal(key), _git._pascal(key))

    def test_the_directory_name_is_refused_too(self):
        for key in RESERVED:
            with self.subTest(key):
                self.assertIn("reserved", refused(_git.pascal, key))

    def test_the_library_of_a_data_file(self):
        self.assertEqual(_git.library_of("data/staging/lib.jsonl"), "lib")
        self.assertEqual(_git.library_of("data/staging/lib/pr-1.jsonl"), "lib")
        for path in ("data/staging/seed.jsonl", "data/trusted/seed.jsonl", "data/staging/seed/pr-1.jsonl", "data/tentative/native.jsonl"):
            with self.subTest(path):
                self.assertIn("reserved", refused(_git.library_of, path))

    def test_the_seed_folder_is_never_a_derived_prefix(self):
        with tempfile.TemporaryDirectory() as d, mock.patch.object(_git, "ROOT", Path(d)):
            (Path(d) / "data" / "trusted").mkdir(parents=True)
            (Path(d) / "data" / "trusted" / "lib-x.jsonl").write_text("{}\n")
            self.assertEqual(sorted(_git.derived_prefixes()), ["Tengoku/LibX.lean", "Tengoku/LibX/"])
            self.assertEqual(_git.tier_of("Tengoku/LibX/A.lean"), "derived")
            for seeded in ("Tengoku/Seed/Algebra/X.lean", "Tengoku/Seed/Std.lean", "Tengoku/Algebra/X.lean", "Tengoku.lean"):
                self.assertEqual(_git.tier_of(seeded), "tooling", seeded)
            (Path(d) / "data" / "staging").mkdir()
            (Path(d) / "data" / "staging" / "seed.jsonl").write_text("{}\n")  # a stray file, wherever it came from
            self.assertIn("reserved", refused(_git.derived_prefixes))
            self.assertIn("reserved", refused(_git.tier_of, "Tengoku/Seed/Algebra/X.lean"))


class Registry(unittest.TestCase):
    def test_no_registered_library_has_a_reserved_key(self):
        """schemas/sources.json is not read by a gate that refuses a key, so this test is the check on what the registry holds."""
        corpora = json.loads((CI.parents[1] / "schemas" / "sources.json").read_text(encoding="utf-8"))["corpora"]
        self.assertGreater(len(corpora), 50)
        for key in corpora:
            self.assertEqual(_git.check_key(key), key)


class GateRefusals(unittest.TestCase):
    """The gates themselves, over a repository: a PR that brings a reserved key is refused, and one that brings another key is not."""

    def validate(self, path: str, library: str) -> tuple[int, str]:
        r = Repo()
        self.addCleanup(shutil.rmtree, r.dir, True)
        r.write(path, json.dumps({**GOOD, "library": library, "name": "Other.good", "statement": "theorem Other.good : 1 + 1 = 2"}) + "\n")
        r.commit("a library")
        return r.gate("validate_records.py")

    def test_records_of_a_reserved_key_are_refused(self):
        for key in ("seed", "native"):
            for path in (f"data/staging/{key}.jsonl", f"data/staging/{key}/pr-1.jsonl", f"data/tentative/{key}.jsonl"):
                with self.subTest(path):
                    rc, out = self.validate(path, key)
                    self.assertEqual(rc, 1, out)
                    self.assertIn("reserved", out)

    def test_records_of_another_key_pass(self):
        rc, out = self.validate("data/staging/other.jsonl", "other")
        self.assertEqual(rc, 0, out)

    def test_an_intake_bundle_of_a_reserved_key_is_refused(self):
        for key in ("seed", "native"):
            r = Repo()
            self.addCleanup(shutil.rmtree, r.dir, True)
            r.write(f"data/intake/{key}/manifest.jsonl", json.dumps({"name": "X.t", "library": key}) + "\n")
            r.commit("a bundle")
            rc, out = r.gate("intake_check.py")
            self.assertEqual(rc, 1, out)
            self.assertIn("reserved", out)


if __name__ == "__main__":
    unittest.main()
