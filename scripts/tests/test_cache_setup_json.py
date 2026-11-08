"""Lake's per-module `*.setup.json` stays out of the cache, the unpack and the top-ups.

2026-10-14: the merge queue failed every group with "No space left on device": after the seed `.lake/build` was 102 GB on a 145 GB runner, and 80 GB of it was one
file per module, `ir/Tengoku/<Module>.setup.json` (1-2 MB each, 33,654 of them). Lake writes that file as the input of compiling a module and never reads it for an
up-to-date one: on a seeded copy of the sandbox tree (19,476 modules, 34 GB, 19 GB of them setup.json) deleting every one left `lake build Tengoku.All --no-build` passing
in 7 s and a normal build compiling nothing (sandbox run 38533106714). So no cache holds them, no unpack writes them (a cache published before this still carries
them), and no top-up ships them (one published before this lists them: it is applied without them)."""

from __future__ import annotations

import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CACHE_SH = ROOT / "scripts" / "cache.sh"
sys.path.insert(0, str(HERE))
from test_topup import BASE_FILES, mark, run, tree  # noqa: E402

SJ = "build/ir/Tengoku/Mod.setup.json"
FILES = {
    "build/lib/lean/Tengoku/Mod.olean": "olean",
    "build/lib/lean/Tengoku/Mod.ilean": "ilean",
    "build/ir/Tengoku/Mod.c": "c",
    SJ: "{" + "x" * 1000 + "}",
}


def have_tools() -> bool:
    return all(shutil.which(t) for t in ("zstd", "tar", "git", "python3"))


@unittest.skipUnless(have_tools(), "zstd, tar, git or python3 missing")
class CacheSh(unittest.TestCase):
    def env(self, root: Path) -> dict:
        return {**os.environ, "TENGOKU_ROOT": str(root), "TENGOKU_ALLOW_MAC_PUT": "1"}

    def repo_with_build(self) -> Path:
        d = tree(FILES)
        for args in (
            ["init", "-q", "-b", "main"],
            ["-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-q", "--allow-empty", "-m", "x"],
        ):
            subprocess.run(["git", *args], cwd=d, check=True, capture_output=True)
        return d

    def listing(self, parts_dir: Path) -> list[str]:
        cat = subprocess.run(
            f'cat "{parts_dir}"/tengoku-cache.tar.zst.part-* | zstd -d -q | tar -tf -',
            shell=True,
            capture_output=True,
            text=True,
            check=True,
        )
        return [ln for ln in cat.stdout.splitlines() if ln and not ln.endswith("/")]

    def test_pack_leaves_the_setup_files_out(self):
        d = self.repo_with_build()
        out = d / "out"
        r = subprocess.run(["bash", str(CACHE_SH), "pack", str(out)], cwd=d, env=self.env(d), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        names = self.listing(out)
        self.assertEqual(sorted(names), ["build/ir/Tengoku/Mod.c", "build/lib/lean/Tengoku/Mod.ilean", "build/lib/lean/Tengoku/Mod.olean"])

    def test_unpack_of_a_cache_that_still_holds_them_writes_none(self):
        # a cache published before this change: setup.json inside the tarball
        src = tree(FILES)
        parts = Path(tempfile.mkdtemp())
        subprocess.run(
            f'tar -C "{src}/.lake" -cf - build | zstd -q | split -b 1900m - "{parts}/tengoku-cache.tar.zst.part-"', shell=True, check=True
        )
        self.assertIn(SJ, self.listing(parts), "the fixture must hold the file the unpack is to leave out")
        dest = Path(tempfile.mkdtemp())
        r = subprocess.run(["bash", str(CACHE_SH), "unpack", str(parts)], cwd=dest, env=self.env(dest), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        got = sorted(str(p.relative_to(dest / ".lake")) for p in (dest / ".lake").rglob("*") if p.is_file())
        self.assertEqual(got, ["build/ir/Tengoku/Mod.c", "build/lib/lean/Tengoku/Mod.ilean", "build/lib/lean/Tengoku/Mod.olean"])


@unittest.skipUnless(shutil.which("zstd"), "zstd not installed")
class Topups(unittest.TestCase):
    def producer(self) -> Path:
        p = tree(BASE_FILES)
        mark(p)
        (p / ".lake/build/lib/lean/Tengoku/New.olean").write_text("N1")
        (p / ".lake/build/ir/Tengoku").mkdir(parents=True, exist_ok=True)
        (p / ".lake/build/ir/Tengoku/New.c").write_text("c")
        (p / ".lake/build/ir/Tengoku/New.setup.json").write_text("{" + "x" * 1000 + "}")
        return p

    def test_a_new_topup_does_not_carry_the_setup_files(self):
        p = self.producer()
        out = p / "out"
        rc, msg = run(p, "make", "--tip", "t1", "--out", str(out))
        self.assertEqual(rc, 0, msg)
        files = json.loads((out / "topup-t1.json").read_text())["files"]
        self.assertEqual(files, ["build/ir/Tengoku/New.c", "build/lib/lean/Tengoku/New.olean"])

    def test_an_old_topup_that_lists_them_is_applied_without_them(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        # rebuild the archive and the manifest the way a top-up published before this change was: setup.json inside, listed
        manifest = json.loads((out / "topup-t1.json").read_text())
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as t:
            for rel in sorted([*manifest["files"], "build/ir/Tengoku/New.setup.json"]):
                data = (p / ".lake" / rel).read_bytes()
                ti = tarfile.TarInfo(rel)
                ti.size = len(data)
                t.addfile(ti, io.BytesIO(data))
        tar = out / "old.tar"
        tar.write_bytes(buf.getvalue())
        subprocess.run(["zstd", "-q", "-f", str(tar), "-o", str(out / "old.tar.zst")], check=True)
        import hashlib

        manifest["files"] = sorted([*manifest["files"], "build/ir/Tengoku/New.setup.json"])
        manifest["sha256"] = hashlib.sha256((out / "old.tar.zst").read_bytes()).hexdigest()
        (out / "old.json").write_text(json.dumps(manifest))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "old.tar.zst"), "--manifest", str(out / "old.json"))
        self.assertEqual(rc, 0, msg)
        self.assertEqual((c / ".lake/build/lib/lean/Tengoku/New.olean").read_text(), "N1")
        self.assertEqual((c / ".lake/build/ir/Tengoku/New.c").read_text(), "c")
        self.assertFalse((c / ".lake/build/ir/Tengoku/New.setup.json").exists())
        rc, msg = run(c, "rollback")
        self.assertEqual(rc, 0, msg)
        self.assertFalse((c / ".lake/build/lib/lean/Tengoku/New.olean").exists())

    def test_a_manifest_naming_a_path_outside_the_module_trees_is_still_refused(self):
        p = self.producer()
        out = p / "out"
        run(p, "make", "--tip", "t1", "--out", str(out))
        manifest = json.loads((out / "topup-t1.json").read_text())
        manifest["files"].append("build/bin/tengoku-axioms")
        (out / "bad.json").write_text(json.dumps(manifest))
        c = tree(BASE_FILES)
        mark(c)
        rc, msg = run(c, "apply", "--file", str(out / "topup-t1.tar.zst"), "--manifest", str(out / "bad.json"))
        self.assertEqual(rc, 1)
        self.assertIn("outside the module trees", msg)


if __name__ == "__main__":
    unittest.main()
