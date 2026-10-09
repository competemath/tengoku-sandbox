"""The vendored tengoku-warden modules (scripts/ci/warden/) are the pinned ones, byte for byte.

Every `PIN*` file in that folder names the warden commit and the sha256 of each module it vendors (`sha256sum -c` format). A file that was
edited here, a module that no PIN lists, a PIN that lists a missing module, or two PINs that name different commits fail this test:
change the code in tengoku-warden and refresh the copy, never by hand."""

from __future__ import annotations

import hashlib
import re
import unittest
from pathlib import Path

WARDEN = Path(__file__).resolve().parents[1] / "warden"
COMMIT = re.compile(r"^# Vendored byte for byte from https://github\.com/competemath/tengoku-warden at commit ([0-9a-f]{40})\b")
ENTRY = re.compile(r"^([0-9a-f]{64})  ([A-Za-z_][A-Za-z0-9_]*\.py)$")


def pins() -> dict:
    """{pin file name: (commit, {module file: sha256})}"""
    out = {}
    for pin in sorted(WARDEN.glob("PIN*")):
        commit, entries = None, {}
        for line in pin.read_text(encoding="utf-8").splitlines():
            if m := COMMIT.match(line):
                commit = m.group(1)
            elif m := ENTRY.match(line):
                entries[m.group(2)] = m.group(1)
            elif line.strip() and not line.startswith("#"):
                raise AssertionError(f"{pin.name}: cannot read the line {line!r}")
        out[pin.name] = (commit, entries)
    return out


class VendoredWarden(unittest.TestCase):
    def test_there_is_a_pin_and_it_names_the_commit(self):
        found = pins()
        self.assertIn("PIN", found)
        for name, (commit, entries) in found.items():
            self.assertIsNotNone(commit, f"{name} does not name the tengoku-warden commit it was taken from")
            self.assertTrue(entries, f"{name} lists no module")

    def test_all_pins_name_one_commit(self):
        self.assertEqual(len({commit for commit, _ in pins().values()}), 1, "the PIN files name different tengoku-warden commits")

    def test_every_module_is_what_its_pin_says(self):
        for name, (_commit, entries) in pins().items():
            for module, digest in entries.items():
                path = WARDEN / module
                self.assertTrue(path.is_file(), f"{name} lists {module}, which is not here")
                self.assertEqual(
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                    digest,
                    f"{module} was edited here: refresh it from tengoku-warden (and its pin), never by hand",
                )

    def test_no_module_is_here_without_a_pin(self):
        listed = {m for _c, entries in pins().values() for m in entries}
        here = {p.name for p in WARDEN.glob("*.py")}
        self.assertEqual(here - listed, set(), "a module in scripts/ci/warden/ that no PIN file lists")

    def test_the_modules_import_as_the_package_the_scripts_use(self):
        import importlib
        import sys

        sys.path.insert(0, str(WARDEN.parent))
        for module in ("scope", "secretscan", "ownership"):
            self.assertTrue(hasattr(importlib.import_module(f"warden.{module}"), "main"))


if __name__ == "__main__":
    unittest.main()
