"""Library keys whose folder is not a library's (Tengoku/Seed/ holds the seeded code, Tengoku/Native/ is kept for a later folder) are refused by
the generator and what drives it: a library generated there would delete the seed as "no record backs it"."""

from __future__ import annotations

import contextlib
import io
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS))
sys.path.append(str(SCRIPTS / "ci"))
import _git  # noqa: E402
import generate  # noqa: E402
import promote  # noqa: E402
import seed  # noqa: E402


class ReservedKeys(unittest.TestCase):
    def setUp(self):
        self.out = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.out)
        (self.out / "Tengoku" / "Seed").mkdir(parents=True)
        (self.out / "Tengoku" / "Seed" / "Init.lean").write_text("module\n")
        (self.out / "corpus").mkdir()

    def refused(self, main, *argv: str) -> str:
        with mock.patch.object(sys, "argv", [main.__module__ + ".py", "--corpus", str(self.out / "corpus"), "--out", str(self.out), *argv]):
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as e:
                main()
        return str(e.exception)

    def test_the_generator_and_the_gates_keep_the_same_list(self):
        self.assertEqual(seed.RESERVED, _git.RESERVED_KEYS)

    def test_no_library_is_generated_over_the_seed(self):
        for key in ("seed", "Seed", "native"):
            with self.subTest(key):
                self.assertIn("reserved", self.refused(generate.main, "--libraries", key))
                self.assertEqual(
                    (self.out / "Tengoku" / "Seed" / "Init.lean").read_text(), "module\n"
                )  # not deleted as "no record backs it"
                self.assertEqual([p.name for p in (self.out / "Tengoku").iterdir()], ["Seed"])  # and nothing written beside it

    def test_promotion_stops_too(self):
        self.assertIn("reserved", self.refused(promote.main, "--library", "seed"))

    def test_the_promote_loop_stops_instead_of_adding_every_path_under_tengoku(self):
        # a copy of the scripts: the loop acts on the checkout it is in
        shutil.copytree(SCRIPTS, self.out / "scripts", ignore=shutil.ignore_patterns("tests", "ci", "__pycache__"))
        r = subprocess.run(
            ["bash", str(self.out / "scripts" / "promote-loop.sh"), str(self.out / "corpus"), "native"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("reserved", r.stderr)

    def test_ordinary_keys_map_to_their_directory_as_before(self):
        self.assertEqual(generate.pascal("equational-theories"), "EquationalTheories")
        self.assertEqual(generate.pascal("lib_x"), "LibX")
        self.assertEqual(generate.pascal("seeded"), "Seeded")


if __name__ == "__main__":
    unittest.main()
