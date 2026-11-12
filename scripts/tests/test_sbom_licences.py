"""A corpus library with files under another licence lists both in the SBOM (derived-alg-geo-lean: MIT, eleven files Apache-2.0)."""

import importlib.util
import unittest
from pathlib import Path

SPEC = importlib.util.spec_from_file_location("sbom", Path(__file__).resolve().parents[1] / "sbom.py")
sbom = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sbom)

REPO = "https://github.com/o/lib"
REGISTRY = {
    "corpora": {
        "lib": {"repo": REPO, "commit": "c" * 40, "roots": ["Lib"]},
        "plain": {"repo": "https://github.com/o/plain", "commit": "d" * 40, "roots": ["P"]},
    },
    "licences": {
        REPO: "MIT",
        f"{REPO}/blob/{'c' * 40}/Lib/A.lean": "Apache-2.0",
        f"{REPO}/blob/{'c' * 40}/Lib/B.lean": "Apache-2.0",
        "https://github.com/o/plain": "Apache-2.0",
    },
}


def ids(component):
    return [entry["license"]["id"] for entry in component.get("licenses", [])]


class SbomLicences(unittest.TestCase):
    def test_a_library_with_files_under_another_licence_lists_both_once(self):
        rows = [{"name": "x", "source_url": f"{REPO}/blob/{'c' * 40}/Lib/A.lean#L1"}]
        self.assertEqual(ids(sbom.source_component("lib", rows, REGISTRY)), ["MIT", "Apache-2.0"])

    def test_a_library_with_one_licence_lists_one(self):
        rows = [{"name": "y", "source_url": "https://github.com/o/plain/blob/" + "d" * 40 + "/P/A.lean#L1"}]
        self.assertEqual(ids(sbom.source_component("plain", rows, REGISTRY)), ["Apache-2.0"])

    def test_an_entry_for_another_commit_does_not_describe_the_pinned_one(self):
        registry = {**REGISTRY, "licences": {**REGISTRY["licences"], f"{REPO}/blob/{'e' * 40}/Lib/C.lean": "GPL-3.0"}}
        rows = [{"name": "x", "source_url": f"{REPO}/blob/{'c' * 40}/Lib/A.lean#L1"}]
        self.assertEqual(ids(sbom.source_component("lib", rows, registry)), ["MIT", "Apache-2.0"])

    def test_a_longer_entry_of_another_repository_with_a_similar_name_is_not_taken(self):
        registry = {**REGISTRY, "licences": {**REGISTRY["licences"], f"{REPO}-fork/blob/x/Lib/A.lean": "GPL-3.0"}}
        rows = [{"name": "x", "source_url": f"{REPO}/blob/{'c' * 40}/Lib/A.lean#L1"}]
        self.assertEqual(ids(sbom.source_component("lib", rows, registry)), ["MIT", "Apache-2.0"])


if __name__ == "__main__":
    unittest.main()
