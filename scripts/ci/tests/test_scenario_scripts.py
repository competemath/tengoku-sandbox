"""selftest.sh and campaign/gate.sh edit a seeded module in some scenarios: whichever of Tengoku/Seed/Logic (the Seed layout) and
Tengoku/Logic (the earlier one) the tree has."""

from __future__ import annotations

import re
import subprocess
import tempfile
import unittest
from pathlib import Path

CI = Path(__file__).resolve().parents[1]
SCRIPTS = ("selftest.sh", "campaign/gate.sh")


HELPER = re.compile(r"seeded_logic\(\) \{.*?\}")


def helper(script: str) -> tuple[str, list[str]]:
    """The `seeded_logic` definition of a script (it may share a line with another definition), and the script's lines without it."""
    text = (CI / script).read_text()
    found = HELPER.findall(text)
    assert len(found) == 1, script
    return found[0], HELPER.sub("", text).splitlines()


def pick(fn: str, *folders: str) -> str:
    with tempfile.TemporaryDirectory() as d:
        for folder in folders:
            (Path(d) / folder).mkdir(parents=True)
        return subprocess.run(["bash", "-c", f"{fn}\nseeded_logic"], cwd=d, capture_output=True, text=True).stdout.strip()


class SeededFolder(unittest.TestCase):
    def test_the_helper_finds_the_folder_of_either_layout(self):
        for script in SCRIPTS:
            fn, _ = helper(script)
            for folder in ("Tengoku/Logic", "Tengoku/Seed/Logic"):
                with self.subTest(script=script, folder=folder):
                    self.assertEqual(pick(fn, folder), folder)

    def test_the_seed_folder_wins_when_both_exist(self):
        for script in SCRIPTS:
            self.assertEqual(pick(helper(script)[0], "Tengoku/Logic", "Tengoku/Seed/Logic"), "Tengoku/Seed/Logic")

    def test_no_scenario_names_the_earlier_folder_itself(self):
        for script in SCRIPTS:
            self.assertEqual([ln for ln in helper(script)[1] if "Tengoku/Logic" in ln], [], script)


if __name__ == "__main__":
    unittest.main()
