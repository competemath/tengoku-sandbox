"""axiom_scan.py audits the theorems of intake bundles (data/intake/<library>/manifest.jsonl) like trusted records: only the three standard
axioms. They had no records and were outside the audit (16,699 theorems, 2026-10-07). A manifest name the export does not hold (an instance
Lean renamed when the module moved into the tree) is reported, not failed; a trusted RECORD missing from a compiled library still fails."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from test_gates import CI, Export  # noqa: E402


def scan(x: Export, records: list[str], manifest: list[str]):
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "tree.ndjson").write_text("\n".join(x.lines) + "\n")
        (root / "data/trusted").mkdir(parents=True)
        (root / "data/intake/bundle").mkdir(parents=True)
        (root / "Tengoku").mkdir()
        (root / "Tengoku/Lib.lean").write_text("")
        (root / "Tengoku/Bundle.lean").write_text("")
        (root / "data/trusted/lib.jsonl").write_text("".join(json.dumps({"name": r}) + "\n" for r in records))
        (root / "data/intake/bundle/manifest.jsonl").write_text(
            "".join(json.dumps({"name": n, "module": "Tengoku.Bundle.M"}) + "\n" for n in manifest)
        )
        r = subprocess.run(
            [sys.executable, str(CI / "axiom_scan.py"), "tree.ndjson", "--records", "data/trusted", "--report", "report.json"],
            cwd=d,
            capture_output=True,
            text=True,
        )
        report = json.loads((root / "report.json").read_text()) if (root / "report.json").exists() else None
    return r.returncode, r.stdout + r.stderr, report


def standard() -> Export:
    x = Export()
    for a in ("propext", "Classical.choice", "Quot.sound"):
        x.axiom(a)
    return x


class IntakeAudit(unittest.TestCase):
    def test_a_bundle_theorem_on_the_standard_axioms_passes_and_is_counted(self):
        x = standard()
        p = x.const("propext")
        x.decl("Bundle.good", p, x.app(p, p))
        code, out, report = scan(x, [], ["Bundle.good"])
        self.assertEqual(code, 0, out)
        self.assertIn(
            "1 trusted records (1 of them theorems of intake bundles), 1 in the export, 1 of them rest only on the standard axioms", out
        )
        self.assertEqual(report["trusted_records"]["intake_theorems"], 1)

    def test_a_bundle_theorem_on_a_native_axiom_fails(self):
        x = standard()
        x.axiom("Lean.ofReduceBool")
        n = x.const("Lean.ofReduceBool")
        x.decl("Bundle.native", n, n)
        code, out, _ = scan(x, [], ["Bundle.native"])
        self.assertEqual(code, 1, out)
        self.assertIn("Bundle.native rests on ['Lean.ofReduceBool']", out)

    def test_a_bundle_name_the_export_lacks_is_reported_not_failed(self):
        x = standard()
        p = x.const("propext")
        x.decl("Bundle.good", p, p)
        code, out, report = scan(x, [], ["Bundle.good", "Bundle.instRenamed"])
        self.assertEqual(code, 0, out)
        self.assertIn("1 bundle theorems are not in the export under their manifest names", out)
        self.assertEqual(report["trusted_records"]["intake_not_under_manifest_name"], ["Bundle.instRenamed"])

    def test_a_manifest_name_matches_the_export_exactly_never_by_suffix(self):
        """`Other.Bundle.good` must not stand in for the bundle's `Bundle.good` (CodeRabbit, #339): the name is reported as not held, not audited."""
        x = standard()
        n = x.axiom("Lean.ofReduceBool") or x.const("Lean.ofReduceBool")
        x.decl("Other.Bundle.good", n, n)  # the only suffix match, and it rests on a native axiom
        code, out, report = scan(x, [], ["Bundle.good"])
        self.assertEqual(code, 0, out)
        self.assertEqual(report["trusted_records"]["intake_not_under_manifest_name"], ["Bundle.good"])
        self.assertNotIn("rests on", out)

    def test_a_trusted_record_the_export_lacks_still_fails_even_when_a_manifest_names_it_too(self):
        x = standard()
        p = x.const("propext")
        x.decl("Bundle.good", p, p)
        code, out, _ = scan(x, ["Lib.gone"], ["Bundle.good"])
        self.assertEqual(code, 1, out)
        self.assertIn("trusted records of compiled libraries are not in the export", out)
        code, out, _ = scan(x, ["Bundle.both"], ["Bundle.both"])
        self.assertEqual(code, 1, out)


if __name__ == "__main__":
    unittest.main()
