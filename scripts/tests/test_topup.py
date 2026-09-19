"""Top-ups: what travels, cumulative packing, overlay with the base kept aside, rollback, refusals."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "scripts" / "topup.py"


def tree(files: dict[str, str]) -> Path:
    d = Path(tempfile.mkdtemp())
    for rel, text in files.items():
        p = d / ".lake" / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    return d


def run(root: Path, *args: str):
    r = subprocess.run([sys.executable, str(TOOL), *args], capture_output=True, text=True, env={**os.environ, "TENGOKU_TOPUP_ROOT": str(root)})
    return r.returncode, r.stdout + r.stderr


def mark(root: Path, tag: str = "cache-base aaaa") -> None:
    (root / ".lake" / ".cache-base").write_text(tag + "\n")
    m = root / ".lake" / ".topup-marker"
    m.write_text("")
    past = time.time() - 60
    for p in (root / ".lake" / "build").rglob("*"):
        if p.is_file():
            os.utime(p, (past - 60, past - 60))
    os.utime(m, (past, past))


BASE_FILES = {"build/lib/lean/Tengoku/A.olean": "A0", "build/lib/lean/Tengoku/Lib.olean": "L0", "build/lib/lean/Other.olean": "O0"}


@unittest.skipUnless(shutil.which("zstd"), "zstd not installed")
class Topups(unittest.TestCase):
    def producer(self) -> Path:
        p = tree(BASE_FILES)
        mark(p)
        (p / ".lake/build/lib/lean/Tengoku/Lib.olean").write_text("L1")  # rebuilt module
        (p / ".lake/build/lib/lean/Tengoku/New.olean").write_text("N1")  # new module
        (p / ".lake/build/ir/Tengoku/New.c").parent.mkdir(parents=True)
        (p / ".lake/build/ir/Tengoku/New.c").write_text("c")
        (p / ".lake/build/lib/lean/Tengoku/_candidate_X.olean").write_text("cand")  # never travels
        (p / ".lake/build/lib/lean/TengokuAxioms.olean").write_text("tool")  # never travels
        (p / ".lake/build/bin").mkdir(parents=True)
        (p / ".lake/build/bin/tengoku-axioms").write_text("bin")  # never travels
        return p

    def test_make_packs_only_changed_module_outputs(self):
        p = self.producer(); out = p / "out"
        rc, msg = run(p, "make", "--tip", "t1", "--out", str(out)); self.assertEqual(rc, 0, msg)
        m = json.loads((out / "topup-t1.json").read_text())
        self.assertEqual(m["files"], ["build/ir/Tengoku/New.c", "build/lib/lean/Tengoku/Lib.olean", "build/lib/lean/Tengoku/New.olean"])
        self.assertEqual(m["base_tag"], "cache-base")

    def test_apply_then_rollback_returns_the_base(self):
        p = self.producer(); out = p / "out"; run(p, "make", "--tip", "t1", "--out", str(out))
        c = tree(BASE_FILES); mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json")); self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L1")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/New.olean").read_text(), "N1")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/A.olean").read_text(), "A0")
        rc, msg = run(c, "rollback"); self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())
        self.assertFalse((c / ".lake/.topup-applied.json").exists())

    def test_a_second_topup_is_cumulative_and_rollback_still_reaches_the_base(self):
        p = self.producer(); out = p / "out"; run(p, "make", "--tip", "t1", "--out", str(out))
        q = tree(BASE_FILES); mark(q)  # a later producer starts from base + t1, builds one more module
        run(q, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        (q / ".lake/build/lib/lean/Tengoku/Newer.olean").write_text("N2")
        out2 = q / "out2"; rc, msg = run(q, "make", "--tip", "t2", "--out", str(out2)); self.assertEqual(rc, 0, msg)
        m2 = json.loads((out2 / "topup-t2.json").read_text())
        self.assertIn("build/lib/lean/Tengoku/New.olean", m2["files"]); self.assertIn("build/lib/lean/Tengoku/Newer.olean", m2["files"])
        c = tree(BASE_FILES); mark(c)
        run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        rc, msg = run(c, "apply", "--file", str(out2 / "topup-t2.tar.zst"), "--manifest", str(out2 / "topup-t2.json")); self.assertEqual(rc, 0, msg)
        run(c, "rollback")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/Newer.olean").exists())

    def test_tampered_file_is_refused_and_nothing_changes(self):
        p = self.producer(); out = p / "out"; run(p, "make", "--tip", "t1", "--out", str(out))
        with (out / "topup-t1.tar.zst").open("ab") as f:
            f.write(b"x")
        c = tree(BASE_FILES); mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 1); self.assertIn("REFUSED", msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")

    def test_manifest_naming_a_path_outside_the_module_trees_is_refused(self):
        p = self.producer(); out = p / "out"; run(p, "make", "--tip", "t1", "--out", str(out))
        m = json.loads((out / "topup-t1.json").read_text()); m["files"].append("build/bin/evil")
        (out / "topup-t1.json").write_text(json.dumps(m))
        c = tree(BASE_FILES); mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 1); self.assertIn("outside the module trees", msg)

    def test_an_empty_topup_is_valid(self):
        p = tree(BASE_FILES); mark(p); out = p / "out"
        rc, msg = run(p, "make", "--tip", "t0", "--out", str(out)); self.assertEqual(rc, 0, msg)
        self.assertEqual(json.loads((out / "topup-t0.json").read_text())["files"], [])
        c = tree(BASE_FILES); mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t0.tar.zst"), "--manifest", str(out / "topup-t0.json")); self.assertEqual(rc, 0, msg)


if __name__ == "__main__":
    unittest.main()
