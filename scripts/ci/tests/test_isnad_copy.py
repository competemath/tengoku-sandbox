"""`scripts/bump/isnad_tag.py` in competemath/emissary-archangel is a verbatim copy of `scripts/isnad_tag.py`: the factory's attest job holds the OIDC token and the attestation
permission, so it runs no code fetched while it runs, and archives each intake module in the canonical form this gate rebuilds from the PR (docs/isnad.md, "Born tagged").
The same pin and the same cases are in emissary-archangel's scripts/bump/tests/test_canonicalise_bundle.py: a change to this file fails a test in each repository until the
copy is changed too (without that the first intake PR would fail attestation, loudly, which is the other way this is caught)."""

import hashlib
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
TREE = HERE.parents[2]
sys.path.insert(0, str(TREE / "scripts"))
import isnad_tag as tg  # noqa: E402

PIN = "1b6127b2e5853f057c35bc177d7f5565966304e07e0d15c294c9d78e02a8bac2"  # pragma: allowlist secret (a file hash). sha256 of scripts/isnad_tag.py in competemath/tengoku, which scripts/bump/isnad_tag.py here is a verbatim copy of
GOLDEN = {
    "one-line docstring": ("/-- Words. -/\ntheorem a : True := trivial\n", "/-- Words.-/\ntheorem a : True := trivial\n"),
    "two-line docstring": ("/-- Two\nlines. -/\ntheorem g : True := trivial\n", "/-- Two\nlines.-/\ntheorem g : True := trivial\n"),
    "a tag in the docstring": (
        "/-- Words.\n  @isnad1 from=novel sha=abc123\n-/\ntheorem t : True := trivial\n",
        "/-- Words.-/\ntheorem t : True := trivial\n",
    ),
    "a tag, translated": (
        "/-- Words.\n@isnad1 from=translated sha=ff\n-/\ntheorem u : True := trivial\n",
        "/-- Words.-/\ntheorem u : True := trivial\n",
    ),
    "closing marker in a string": ('def s : String := "x -/ y"\n', 'def s : String := "x -/ y"\n'),
    "no docstring": ("theorem v : True := trivial\n", "theorem v : True := trivial\n"),
    "module header": (
        "module\n\npublic import Tengoku\n\n/-- Mod. -/\ntheorem w : True := trivial\n",
        "module\n\npublic import Tengoku\n\n/-- Mod.-/\ntheorem w : True := trivial\n",
    ),
}


class IsnadCopy(unittest.TestCase):
    def test_the_file_is_the_one_emissary_archangel_copies(self):
        self.assertEqual(
            hashlib.sha256((TREE / "scripts" / "isnad_tag.py").read_bytes()).hexdigest(),
            PIN,
            "scripts/isnad_tag.py changed: copy it verbatim to competemath/emissary-archangel scripts/bump/isnad_tag.py and update PIN in both test files",
        )

    def test_the_golden_cases(self):
        for name, (text, want) in GOLDEN.items():
            self.assertEqual(tg.canonical_text(text), want, name)
            self.assertEqual(tg.canonical_text(want), want, f"{name}: idempotent")


if __name__ == "__main__":
    unittest.main()
