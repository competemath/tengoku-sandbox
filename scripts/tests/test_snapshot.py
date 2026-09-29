"""snapshot.py: the dataset carries what each trusted record states, where it came from, its licence and credit."""

from __future__ import annotations

import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def rec(name: str, statement: str, **kw) -> dict:
    return {
        "name": name,
        "statement": statement,
        "proof": ":= rfl",
        "status": "trusted",
        "library": "lib",
        "source_url": "https://github.com/fpvandoorn/Carleson/blob/abc/X.lean",
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "promoted_at": "2026-09-01T00:00:00Z",
        **kw,
    }


class Snapshot(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        (self.root / "schemas").mkdir()
        # its own registry: the test must not depend on what the real one lists
        (self.root / "schemas" / "sources.json").write_text(
            json.dumps({"licences": {"https://github.com/fpvandoorn/Carleson": "Apache-2.0"}})
        )
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
        (self.root / "data" / "trusted").mkdir(parents=True)
        (self.root / "data" / "staging" / "lib").mkdir(parents=True)
        doc = "/-- One plus one.\n\nAuthor: Ada Lovelace (https://github.com/ada), with Claude. -/\n"
        lines = [
            rec("Lib.a", doc + "theorem Lib.a : 1 + 1 = 2", headline=True),
            rec("Lib.b", "theorem Lib.b : True"),
            rec("Lib.gone", "theorem Lib.gone : True"),
            {"tombstone": "Lib.gone", "category": "duplicate", "reason": "same as Lib.b", "by": "x", "at": "2026-09-02"},
            {"tombstone_note": "Lib.gone", "note": "see Lib.b", "by": "x", "at": "2026-09-02"},
            {
                "credit_correction": "Lib.b",
                "credit": "Author: Grace Hopper (https://example.org/gh)",
                "evidence": "https://example.org/e",
                "by": "x",
                "at": "2026-09-03",
            },
        ]
        (self.root / "data" / "trusted" / "lib.jsonl").write_text("".join(json.dumps(x) + "\n" for x in lines))
        (self.root / "data" / "staging" / "lib" / "pr-1.jsonl").write_text(
            json.dumps({**rec("Lib.s", "theorem Lib.s : True"), "status": "staging"}) + "\n"
        )

    def tearDown(self):
        shutil.rmtree(self.root)

    def test_dataset_and_manifest(self):
        out = self.root / "out"
        r = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "snapshot.py"), "--out", str(out), "--root", str(self.root)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        import gzip

        raw = gzip.decompress((out / "tengoku-dataset.jsonl.gz").read_bytes())
        rows = [json.loads(x) for x in raw.decode().splitlines()]
        by = {x["name"]: x for x in rows}
        self.assertEqual(sorted(by), ["Lib.a", "Lib.b"])  # the retracted record is left out; staging is not in the dataset
        self.assertEqual(by["Lib.a"]["licence"], "Apache-2.0")
        self.assertEqual(by["Lib.a"]["credit"], "Author: Ada Lovelace (https://github.com/ada), with Claude.")
        self.assertTrue(by["Lib.a"]["headline"])
        self.assertEqual(by["Lib.b"]["credit"], "Author: Grace Hopper (https://example.org/gh)")
        self.assertEqual(by["Lib.b"]["credit_corrected_evidence"], "https://example.org/e")
        m = json.loads((out / "snapshot.json").read_text())
        self.assertEqual(m["dataset"]["records"], 2)
        self.assertEqual(m["dataset"]["file"], "tengoku-dataset.jsonl.gz")
        self.assertEqual(m["dataset"]["sha256"], hashlib.sha256((out / "tengoku-dataset.jsonl.gz").read_bytes()).hexdigest())
        self.assertEqual(m["dataset"]["uncompressed_sha256"], hashlib.sha256(raw).hexdigest())
        self.assertEqual(m["libraries"]["lib"], {"trusted": 2, "staging": 1})
        self.assertEqual(m["toolchain"], "leanprover/lean4:v4.34.0-rc2")

    def run_snapshot(self, out: Path, previous: Path | None = None) -> dict | None:
        args = [sys.executable, str(ROOT / "scripts" / "snapshot.py"), "--out", str(out), "--root", str(self.root)]
        r = subprocess.run(args + (["--previous", str(previous)] if previous else []), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        if (out / "unchanged").exists():
            return None
        return json.loads((out / "snapshot.json").read_text())

    def append(self, *rows: dict) -> None:
        with (self.root / "data" / "trusted" / "lib.jsonl").open("a") as f:
            f.write("".join(json.dumps(x) + "\n" for x in rows))

    def test_versions_follow_what_changed(self):
        first = self.run_snapshot(self.root / "v1")
        self.assertEqual(first["version"], "1.0.0")
        self.assertIn("headline", first["fields"])
        self.assertIsNone(self.run_snapshot(self.root / "same", self.root / "v1"))  # nothing changed: no release

        self.append(rec("Lib.c", "theorem Lib.c : True"))  # a theorem added: minor
        added = self.run_snapshot(self.root / "v2", self.root / "v1")
        self.assertEqual(added["version"], "1.1.0")

        self.append({"tombstone": "Lib.c", "category": "incorrect", "reason": "r", "by": "x", "at": "2026-09-04"})
        retracted = self.run_snapshot(self.root / "v3", self.root / "v2")  # a retraction: patch
        self.assertEqual(retracted["version"], "1.1.1")

        self.append(
            {
                "credit_correction": "Lib.a",
                "credit": "Author: Emmy Noether",
                "evidence": "https://example.org/n",
                "by": "x",
                "at": "2026-09-05",
            }
        )
        corrected = self.run_snapshot(self.root / "v4", self.root / "v3")  # a credit correction: patch
        self.assertEqual(corrected["version"], "1.1.2")

        self.append({"tombstone": "Lib.a", "category": "duplicate", "reason": "r", "by": "x", "at": "2026-09-06"})
        no_headline = self.run_snapshot(self.root / "v5", self.root / "v4")  # the last headline retracted: still patch
        self.assertEqual(no_headline["version"], "1.1.3")
        self.assertEqual(no_headline["fields"], first["fields"])

        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")  # a new toolchain: major
        bumped = self.run_snapshot(self.root / "v6", self.root / "v5")
        self.assertEqual(bumped["version"], "2.0.0")

    def test_a_removed_field_is_major_and_a_new_field_minor(self):
        first = self.run_snapshot(self.root / "v1")
        prev = self.root / "v1" / "snapshot.json"
        m = json.loads(prev.read_text())
        # the same theorems, but the previous release lacked a field this one has (so its rows differed): minor
        prev.write_text(
            json.dumps(
                {
                    **m,
                    "fields": [f for f in first["fields"] if f != "upstream"],
                    "dataset": {**m["dataset"], "uncompressed_sha256": "0" * 64},
                }
            )
        )
        self.assertEqual(self.run_snapshot(self.root / "v2", self.root / "v1")["version"], "1.1.0")
        # the previous release had a field this one lacks: major, whatever else changed
        prev.write_text(json.dumps({**m, "fields": first["fields"] + ["retired"]}))
        self.assertEqual(self.run_snapshot(self.root / "v3", self.root / "v1")["version"], "2.0.0")

    def test_a_library_split_over_files_is_one_library(self):
        # Mathlib's records are in data/trusted/mathlib-*.jsonl; each names library "mathlib"
        (self.root / "data" / "trusted" / "big-algebra.jsonl").write_text(
            json.dumps(rec("Big.x", "theorem Big.x : True", library="big")) + "\n"
        )
        (self.root / "data" / "trusted" / "big-topology.jsonl").write_text(
            json.dumps(rec("Big.y", "theorem Big.y : True", library="big"))
            + "\n"
            + json.dumps({"tombstone": "Big.x", "category": "duplicate", "reason": "r", "by": "x", "at": "2026-09-02"})
            + "\n"
        )
        m = self.run_snapshot(self.root / "out")
        self.assertEqual(m["libraries"]["big"], {"trusted": 1})  # one library, and the retraction in the other file applies
        self.assertNotIn("big-algebra", m["libraries"])
        raw = gzip.decompress((self.root / "out" / "tengoku-dataset.jsonl.gz").read_bytes()).decode()
        self.assertEqual([json.loads(x)["library"] for x in raw.splitlines() if "Big." in x], ["big"])

    def test_retracting_every_record_is_a_patch(self):
        first = self.run_snapshot(self.root / "v1")
        self.append(*({"tombstone": n, "category": "incorrect", "reason": "r", "by": "x", "at": "2026-09-09"} for n in ("Lib.a", "Lib.b")))
        empty = self.run_snapshot(self.root / "v2", self.root / "v1")
        self.assertEqual((empty["version"], empty["dataset"]["records"], empty["fields"]), ("1.0.1", 0, first["fields"]))


if __name__ == "__main__":
    unittest.main()
