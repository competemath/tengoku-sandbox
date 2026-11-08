"""Top-ups: what travels, cumulative packing, overlay with the base kept aside, rollback, refusals."""

from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
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
    r = subprocess.run(
        [sys.executable, str(TOOL), *args], capture_output=True, text=True, env={**os.environ, "TENGOKU_TOPUP_ROOT": str(root)}
    )
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
        p = self.producer()
        out = p / "out"
        rc, msg = run(p, "make", "--tip", "t1", "--out", str(out))
        self.assertEqual(rc, 0, msg)
        m = json.loads((out / "topup-t1.json").read_text())
        self.assertEqual(m["files"], ["build/ir/Tengoku/New.c", "build/lib/lean/Tengoku/Lib.olean", "build/lib/lean/Tengoku/New.olean"])
        self.assertEqual(m["base_tag"], "cache-base")

    def test_apply_then_rollback_returns_the_base(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L1")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/New.olean").read_text(), "N1")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/A.olean").read_text(), "A0")
        rc, msg = run(c, "rollback")
        self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())
        self.assertFalse((c / ".lake/.topup-applied.json").exists())

    def test_a_second_topup_is_cumulative_and_rollback_still_reaches_the_base(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        q = tree(BASE_FILES)
        mark(q)  # a later producer starts from base + t1, builds one more module
        run(q, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        (q / ".lake/build/lib/lean/Tengoku/Newer.olean").write_text("N2")
        out2 = q / "out2"
        rc, msg = run(q, "make", "--tip", "t2", "--out", str(out2))
        self.assertEqual(rc, 0, msg)
        m2 = json.loads((out2 / "topup-t2.json").read_text())
        self.assertIn("build/lib/lean/Tengoku/New.olean", m2["files"])
        self.assertIn("build/lib/lean/Tengoku/Newer.olean", m2["files"])
        c = tree(BASE_FILES)
        mark(c)
        run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        rc, msg = run(c, "apply", "--file", str(out2 / "topup-t2.tar.zst"), "--manifest", str(out2 / "topup-t2.json"))
        self.assertEqual(rc, 0, msg)
        run(c, "rollback")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/Newer.olean").exists())

    def test_a_module_that_went_back_to_its_base_content_is_undone_by_the_next_topup(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))  # t1 rewrites Lib and adds New
        q = tree(BASE_FILES)
        mark(q)  # t2 is built from the bare base: only A differs, Lib and New are as in the base
        (q / ".lake/build/lib/lean/Tengoku/A.olean").write_text("A2")
        out2 = q / "out2"
        run(q, "make", "--tip", "t2", "--out", str(out2))
        c = tree(BASE_FILES)
        mark(c)
        run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        rc, msg = run(c, "apply", "--file", str(out2 / "topup-t2.tar.zst"), "--manifest", str(out2 / "topup-t2.json"))
        self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/A.olean").read_text(), "A2")
        run(c, "rollback")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/A.olean").read_text(), "A0")

    def test_a_process_holding_the_old_file_keeps_it(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        c = tree(BASE_FILES)
        mark(c)
        lib = c / ".lake/build/lib/lean/Tengoku/Lib.olean"
        with lib.open() as held:  # a running Lean process has the base file open (mapped)
            run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
            self.assertEqual(lib.read_text(), "L1")  # a new process sees the top-up
            self.assertEqual(held.read(), "L0")  # the old one still has what it started with
            with lib.open() as held_new:
                run(c, "rollback")
                self.assertEqual(held_new.read(), "L1")
        self.assertEqual(lib.read_text(), "L0")
        self.assertEqual([f.name for f in lib.parent.iterdir() if f.name.endswith(".topup-new")], [])

    def test_tampered_file_is_refused_and_nothing_changes(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        with (out / "topup-t1.tar.zst").open("ab") as f:
            f.write(b"x")
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 1)
        self.assertIn("REFUSED", msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")

    def test_apply_streams_the_archive_it_never_holds_the_unpacked_bytes(self):
        """2026-10-11: a top-up of 772 MB packed was 10.6 GB unpacked; `zstd -d` captured whole (and joined: twice) killed the queue's runner 'with a shutdown signal' in the seed
        step of every Lean build, and the merge queue stood still. Python's own memory while it unpacks is a few megabytes, whatever the archive."""
        p = self.producer()
        (p / ".lake/build/lib/lean/Tengoku/Big.olean").write_bytes(b"\0" * (150 << 20))  # packs to a few KB, unpacks to 150 MB
        out = p / "out"
        rc, msg = run(p, "make", "--tip", "t1", "--out", str(out))
        self.assertEqual(rc, 0, msg)
        c = tree(BASE_FILES)
        mark(c)
        driver = (
            "import sys, tracemalloc; from pathlib import Path; sys.path.insert(0, sys.argv[1]); import topup; tracemalloc.start(); "
            "rc = topup.apply(Path(sys.argv[2]), Path(sys.argv[3])); print(rc, tracemalloc.get_traced_memory()[1])"
        )
        r = subprocess.run(
            [sys.executable, "-c", driver, str(ROOT / "scripts"), str(out / "topup-t1.tar.zst"), str(out / "topup-t1.json")],
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_TOPUP_ROOT": str(c)},
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        rc, peak = (int(x) for x in r.stdout.split()[-2:])
        self.assertEqual(rc, 0)
        self.assertLess(peak, 20 << 20, f"python held {peak >> 20} MB while unpacking a 150 MB archive")
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Big.olean").stat().st_size, 150 << 20)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L1")

    def test_an_archive_that_stops_halfway_is_refused_and_the_base_is_back(self):
        """The stream is unpacked as it arrives, so a broken archive has already replaced some files when it is found: they all go back (the digest still matches: it is the manifest's, of the file as published)."""
        p = self.producer()
        (p / ".lake/build/lib/lean/Tengoku/Zbig.olean").write_bytes(
            os.urandom(3 << 20)
        )  # last in the archive, incompressible: the small files are unpacked before zstd finds the missing end
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        tar = out / "topup-t1.tar.zst"
        tar.write_bytes(tar.read_bytes()[:-40])
        m = json.loads((out / "topup-t1.json").read_text())
        m["sha256"] = subprocess.run(["shasum", "-a", "256", str(tar)], capture_output=True, text=True).stdout.split()[0]
        (out / "topup-t1.json").write_text(json.dumps(m))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(tar), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 1, msg)
        self.assertIn("does not decompress", msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")  # the base again
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())
        self.assertFalse((c / ".lake/.topup-applied.json").exists())

    def test_an_unexpected_member_after_files_were_replaced_puts_the_base_back(self):
        """CodeRabbit on #442: the stream is unpacked as it arrives, so the member the manifest does not list can come after real files were replaced (rollback() reads the PREVIOUS
        top-up's state and would leave a mix of base and top-up files with no backup)."""
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        m = json.loads((out / "topup-t1.json").read_text())
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as t:  # in this order: the real files first, the member the manifest does not list last
            for rel, data in [(rel, (p / ".lake" / rel).read_bytes()) for rel in m["files"]] + [
                ("build/lib/lean/Tengoku/Zextra.olean", b"not in the manifest")
            ]:
                info = tarfile.TarInfo(rel)
                info.size = len(data)
                t.addfile(info, io.BytesIO(data))
        tar = out / "forged.tar.zst"
        subprocess.run(["zstd", "-q", "-o", str(tar)], input=buf.getvalue(), check=True)
        m["sha256"] = subprocess.run(["shasum", "-a", "256", str(tar)], capture_output=True, text=True).stdout.split()[0]
        (out / "forged.json").write_text(json.dumps(m))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(tar), "--manifest", str(out / "forged.json"))
        self.assertEqual(rc, 1, msg)
        self.assertIn("unexpected member", msg)
        self.assertEqual(
            (c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0"
        )  # replaced before the bad member arrived, put back
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())  # created before it, gone
        self.assertFalse((c / ".lake/.topup-applied.json").exists())

    def test_a_write_that_fails_halfway_puts_the_base_back_and_leaves_no_scratch_file(self):
        """CodeRabbit on #442: a full disk (the archive unpacks to gigabytes) is an OSError, not a TarError: it must undo as well."""
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        c = tree(BASE_FILES)
        mark(c)
        driver = (
            "import sys, shutil; from pathlib import Path; sys.path.insert(0, sys.argv[1]); import topup\n"
            "real, n = shutil.copyfileobj, [0]\n"
            "def failing(src, dst, *a):\n"
            "    n[0] += 1\n"
            "    if n[0] == 3: raise OSError(28, 'No space left on device')\n"
            "    return real(src, dst, *a)\n"
            "topup.shutil.copyfileobj = failing\n"
            "print(topup.apply(Path(sys.argv[2]), Path(sys.argv[3])))"
        )
        r = subprocess.run(
            [sys.executable, "-c", driver, str(ROOT / "scripts"), str(out / "topup-t1.tar.zst"), str(out / "topup-t1.json")],
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_TOPUP_ROOT": str(c)},
        )
        self.assertEqual((r.returncode, r.stdout.strip()), (0, "1"), r.stderr)
        self.assertIn("No space left on device", r.stderr)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L0")
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())
        self.assertEqual([str(f) for f in (c / ".lake").rglob("*.topup-new")], [])
        self.assertFalse((c / ".lake/.topup-applied.json").exists())

    def test_an_archive_whose_name_begins_with_a_dash_is_a_file_not_an_option(self):
        """SonarCloud S8705 (command argument injection) on #442: the path from the command line went to zstd as an argument. It goes as an absolute path after `--` now."""
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        (out / "topup-t1.tar.zst").rename(out / "-n.tar.zst")
        c = tree(BASE_FILES)
        mark(c)
        r = subprocess.run(
            [sys.executable, str(TOOL), "apply", "--file=-n.tar.zst", "--manifest", str(out / "topup-t1.json")],
            cwd=out,
            capture_output=True,
            text=True,
            env={**os.environ, "TENGOKU_TOPUP_ROOT": str(c)},
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/Lib.olean").read_text(), "L1")

    def test_manifest_naming_a_path_outside_the_module_trees_is_refused(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        m = json.loads((out / "topup-t1.json").read_text())
        m["files"].append("build/bin/evil")
        (out / "topup-t1.json").write_text(json.dumps(m))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "topup-t1.json"))
        self.assertEqual(rc, 1)
        self.assertIn("outside the module trees", msg)

    def test_an_empty_topup_is_valid(self):
        p = tree(BASE_FILES)
        mark(p)
        out = p / "out"
        rc, msg = run(p, "make", "--tip", "t0", "--out", str(out))
        self.assertEqual(rc, 0, msg)
        self.assertEqual(json.loads((out / "topup-t0.json").read_text())["files"], [])
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t0.tar.zst"), "--manifest", str(out / "topup-t0.json"))
        self.assertEqual(rc, 0, msg)


if __name__ == "__main__":
    unittest.main()
