"""scripts/lake_cache.py restore / pack / decide: the store half, with gh, curl, lake and zstd replaced by shims (no network, no Lean).

A real git repository stands in for the tree: `base` (the nightly's commit) then c1, c2, c3 on main and an orphan commit on a branch.
The fake release holds deltas for c1 and c3 (c2 published none) and for the orphan."""

import io
import json
import os
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "lake_cache.py"
sys.path.insert(0, str(SCRIPT.parent))
import lake_cache as lc  # noqa: E402

HEADER = '"2026-03-17"'

GH = r"""#!/usr/bin/env bash
case "$1 $2" in
  "auth status") exit 0 ;;
  "api repos"*) ;;
esac
if [ "$1" = api ]; then
  name="${2##*/}"; f="$SHIM_DIR/releases/$name.json"; [ -f "$f" ] && cat "$f" && exit 0; echo "not found" >&2; exit 1
fi
if [ "$1" = attestation ]; then
  base="$(basename "$3")"; grep -qx "$base" "$SHIM_DIR/bad-attest.txt" 2>/dev/null && exit 1; echo "$base $*" >> "$SHIM_DIR/verified.log"; exit 0
fi
exit 2
"""
CURL = r"""#!/usr/bin/env bash
dest=""; url=""
while [ $# -gt 0 ]; do case "$1" in -o) dest="$2"; shift ;; https://*) url="$1" ;; esac; shift; done
rel="$(basename "$(dirname "$url")")"; asset="$(basename "$url")"
src="$SHIM_DIR/assets/$rel/$asset"
[ -f "$src" ] || exit 22
cp "$src" "$dest"
"""
LAKE = r"""#!/usr/bin/env bash
if [ "$1 $2" = "cache unstage" ]; then echo "unstage $3" >> "$SHIM_DIR/lake.log"; cat "$3/outputs.jsonl" >> "$SHIM_DIR/unstaged.jsonl"; exit 0; fi
if [ "$1 $2" = "cache stage" ]; then mkdir -p "$4"; cp "$3" "$4/outputs.jsonl"; n=$(($(wc -l < "$3") - 1)); for i in $(seq 1 $n); do head -c "${SHIM_LTAR_BYTES:-64}" /dev/zero > "$4/art$i.ltar"; done; exit 0; fi
exit 2
"""
ZSTD = r"""#!/usr/bin/env bash
out=""; dc=0; in=""
while [ $# -gt 0 ]; do case "$1" in -dc) dc=1 ;; -o) out="$2"; shift ;; -*) ;; *) in="$1" ;; esac; shift; done
if [ "$dc" = 1 ]; then cat "$in"; else cat > "$out"; fi
"""


def sh(cmd, cwd, env=None):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


class Store(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.shim = root / "shim"
        (self.shim / "bin").mkdir(parents=True)
        for name, text in (("gh", GH), ("curl", CURL), ("lake", LAKE), ("zstd", ZSTD)):
            p = self.shim / "bin" / name
            p.write_text(text)
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
        (self.shim / "releases").mkdir()
        (self.shim / "assets").mkdir()
        (self.shim / "bad-attest.txt").write_text("")
        # the tree: a git repository with base, c1, c2, c3 on main and an orphan on a branch
        self.repo = root / "tree"
        self.repo.mkdir()
        g = lambda *a: sh(["git", *a], self.repo)  # noqa: E731
        g("init", "-q", "-b", "main")
        g("config", "user.email", "t@example.invalid")
        g("config", "user.name", "t")
        self.sha = {}
        for name in ("base", "c1", "c2", "c3"):
            (self.repo / f"{name}.txt").write_text(name)
            g("add", "-A")
            g("commit", "-qm", name)
            self.sha[name] = g("rev-parse", "HEAD").stdout.strip()
        g("checkout", "-qb", "side", self.sha["base"])
        (self.repo / "orphan.txt").write_text("x")
        g("add", "-A")
        g("commit", "-qm", "orphan")
        self.sha["orphan"] = g("rev-parse", "HEAD").stdout.strip()
        g("checkout", "-q", "main")
        (self.repo / ".lake").mkdir()
        (self.repo / ".lake" / ".cache-base").write_text(f"cache-20261014T0336Z {self.sha['base']}\n")
        self.env = {
            **os.environ,
            "PATH": f"{self.shim / 'bin'}{os.pathsep}{os.environ['PATH']}",
            "SHIM_DIR": str(self.shim),
            "TENGOKU_REPO": "org/repo",
            "TENGOKU_VERIFY": "require",
        }
        # the store: the cache release carries base.jsonl, the delta release the deltas of c1, c3 and the orphan
        self.release = "lake-deltas-cache-20261014T0336Z"
        self.put_asset("cache-20261014T0336Z", "base.jsonl", (HEADER + '\n{"m":"base1"}\n{"m":"base2"}\n').encode())
        for name in ("c1", "c3", "orphan"):
            self.put_asset(self.release, f"d-{self.sha[name]}.tar.zst", self.delta(name))
        (self.shim / "releases" / "cache-20261014T0336Z.json").write_text(json.dumps({"assets": [{"name": "base.jsonl"}]}))
        (self.shim / "releases" / f"{self.release}.json").write_text(
            json.dumps({"assets": [{"name": "LICENSE"}] + [{"name": f"d-{self.sha[n]}.tar.zst"} for n in ("c3", "orphan", "c1")]})
        )

    def tearDown(self):
        self.tmp.cleanup()

    def put_asset(self, release, name, data: bytes):
        d = self.shim / "assets" / release
        d.mkdir(exist_ok=True)
        (d / name).write_bytes(data)

    def delta(self, name) -> bytes:
        """A packed staging directory: outputs.jsonl (header + one mapping) and one artifact (the zstd shim is a pass-through)."""
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w") as t:
            for fname, data in (("outputs.jsonl", f'{HEADER}\n{{"m":"{name}"}}\n'.encode()), (f"{name}.ltar", b"\0" * 16)):
                ti = tarfile.TarInfo(fname)
                ti.size = len(data)
                t.addfile(ti, io.BytesIO(data))
        return buf.getvalue()

    def restore(self, *args):
        r = sh([sys.executable, str(SCRIPT), "restore", *args], self.repo, self.env)
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout.strip().splitlines()[-1]), r

    def test_the_deltas_of_the_merges_since_the_base_are_applied_oldest_first_and_only_those(self):
        s, _ = self.restore()
        self.assertEqual(
            s["applied"], [f"d-{self.sha['c1']}.tar.zst", f"d-{self.sha['c3']}.tar.zst"]
        )  # c2 has none, the orphan is not in main's history
        self.assertEqual((s["skipped"], s["refused"], s["revs"], s["base_mappings"]), ([], [], 3, "present"))
        log = (self.shim / "lake.log").read_text().splitlines()
        self.assertEqual(len(log), 2)
        self.assertEqual((self.repo / ".lake" / ".deltas-applied").read_text().split(), s["applied"])

    def test_what_the_store_knows_is_the_base_plus_the_applied_deltas_with_one_header(self):
        self.restore()
        had = (self.repo / ".lake" / "deltas-had.jsonl").read_text().splitlines()
        self.assertEqual(had, [HEADER, '{"m":"base1"}', '{"m":"base2"}', '{"m":"c1"}', '{"m":"c3"}'])

    def test_a_second_restore_applies_nothing_again(self):
        self.restore()
        s, _ = self.restore()
        self.assertEqual(s["applied"], [])
        self.assertEqual(len((self.shim / "lake.log").read_text().splitlines()), 2)

    def test_require_mode_skips_a_delta_without_a_valid_attestation_and_lake_compiles_instead(self):
        (self.shim / "bad-attest.txt").write_text(f"d-{self.sha['c3']}.tar.zst\n")
        s, _ = self.restore()
        self.assertEqual(s["applied"], [f"d-{self.sha['c1']}.tar.zst"])
        self.assertEqual(len(s["refused"]), 1)
        self.assertIn("no valid build attestation", s["refused"][0])
        self.assertNotIn('{"m":"c3"}', (self.repo / ".lake" / "deltas-had.jsonl").read_text())

    def test_warn_mode_applies_it_with_a_warning(self):
        (self.shim / "bad-attest.txt").write_text(f"d-{self.sha['c3']}.tar.zst\n")
        self.env["TENGOKU_VERIFY"] = "warn"
        s, r = self.restore()
        self.assertEqual(len(s["applied"]), 2)
        self.assertIn("warning", r.stderr)

    def test_every_accepted_file_was_checked_against_the_right_workflow(self):
        self.restore()
        lines = (self.shim / "verified.log").read_text().splitlines()
        self.assertTrue(any(ln.startswith("base-") and "build.yml" in ln for ln in lines), lines)
        self.assertTrue(all("queue-gate.yml" in ln for ln in lines if ln.startswith("d-")), lines)

    def test_a_base_without_published_mappings_is_reported_and_the_deltas_still_apply(self):
        (self.shim / "assets" / "cache-20261014T0336Z" / "base.jsonl").unlink()
        s, _ = self.restore()
        self.assertTrue(s["base_mappings"].startswith("missing"))
        self.assertTrue((self.repo / ".lake" / ".base-missing").exists())
        self.assertEqual(len(s["applied"]), 2)
        self.assertEqual((self.repo / ".lake" / "deltas-had.jsonl").read_text().splitlines(), ['{"m":"c1"}', '{"m":"c3"}'])

    def test_a_base_with_no_delta_release_yet_restores_nothing_and_succeeds(self):
        (self.shim / "releases" / f"{self.release}.json").unlink()
        s, _ = self.restore()
        self.assertEqual(s["applied"], [])
        self.assertIn("no release", s["note"])

    def test_restoring_to_an_older_commit_applies_only_its_history(self):
        s, _ = self.restore("--want", self.sha["c2"])
        self.assertEqual(s["applied"], [f"d-{self.sha['c1']}.tar.zst"])

    def test_an_archive_that_does_not_unpack_is_refused_not_fatal(self):
        self.put_asset(self.release, f"d-{self.sha['c1']}.tar.zst", b"not a tar at all")
        s, _ = self.restore()
        self.assertEqual(s["applied"], [f"d-{self.sha['c3']}.tar.zst"])
        self.assertEqual(len(s["refused"]), 1)
        self.assertIn("could not unpack", s["refused"][0])

    def test_a_base_file_that_is_not_what_cache_sh_writes_is_refused_before_any_path_or_url_is_built(self):
        for tag in ("../../etc", "cache/../x", ".hidden", "a b", "x;y"):
            (self.repo / ".lake" / ".cache-base").write_text(f"{tag} {self.sha['base']}\n")
            r = subprocess.run([sys.executable, str(SCRIPT), "restore"], cwd=self.repo, env=self.env, capture_output=True, text=True)
            self.assertEqual(r.returncode, 2, (tag, r.stdout, r.stderr))
            self.assertIn("is not what it may be", r.stderr)
        self.assertFalse((self.repo / ".lake" / ".delta-store").exists() and any((self.repo / ".lake" / ".delta-store").iterdir()))
        (self.repo / ".lake" / ".cache-base").write_text("cache-20261014T0336Z not-a-commit\n")
        r = subprocess.run([sys.executable, str(SCRIPT), "restore"], cwd=self.repo, env=self.env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)

    def test_a_repository_that_is_not_owner_slash_name_is_refused(self):
        for repo in ("../x", "a/b/c", "a b/c", "org/repo;rm"):
            r = subprocess.run(
                [sys.executable, str(SCRIPT), "restore"],
                cwd=self.repo,
                env={**self.env, "TENGOKU_CACHE_SOURCE": repo},
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 2, (repo, r.stderr))

    def test_no_unpacked_base_is_an_error(self):
        (self.repo / ".lake" / ".cache-base").unlink()
        r = sh([sys.executable, str(SCRIPT), "restore"], self.repo, self.env)
        self.assertEqual(r.returncode, 1)
        self.assertIn("cache.sh get", r.stderr)


class Pack(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.shim = root / "shim"
        (self.shim / "bin").mkdir(parents=True)
        for name, text in (("lake", LAKE), ("zstd", ZSTD)):
            p = self.shim / "bin" / name
            p.write_text(text)
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
        self.env = {**os.environ, "PATH": f"{self.shim / 'bin'}{os.pathsep}{os.environ['PATH']}", "SHIM_DIR": str(self.shim)}
        self.new = root / "new.jsonl"
        self.new.write_text(HEADER + "\n" + "".join(f'{{"m":{i}}}\n' for i in range(5)))
        self.out = root / "out"

    def tearDown(self):
        self.tmp.cleanup()

    def pack(self, *args):
        r = subprocess.run(
            [sys.executable, str(SCRIPT), "pack", "--rev", "a" * 40, "--new", str(self.new), "--out", str(self.out), *args],
            env=self.env,
            capture_output=True,
            text=True,
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout.strip().splitlines()[-1])

    def test_within_budget_the_delta_is_packed_as_one_file_named_by_the_commit(self):
        s = self.pack()
        self.assertEqual((s["decision"], s["files"], s["asset"]), ("publish", 6, "d-" + "a" * 40 + ".tar.zst"))
        self.assertTrue((self.out / s["asset"]).exists())
        with tarfile.open(self.out / s["asset"]) as t:  # the zstd shim is a pass-through, so the file is a plain tar
            names = sorted(os.path.basename(m.name) for m in t.getmembers() if m.isfile())
        self.assertEqual(names, ["art1.ltar", "art2.ltar", "art3.ltar", "art4.ltar", "art5.ltar", "outputs.jsonl"])

    def test_over_budget_leaves_a_marker_and_no_file(self):
        self.env["SHIM_LTAR_BYTES"] = str(1024 * 1024)
        s = self.pack("--budget-mb", "2")
        self.assertEqual(s["decision"], "needs-nightly:over-budget")
        self.assertEqual((self.out / "needs-nightly").read_text().strip(), "needs-nightly:over-budget")
        self.assertEqual(list(self.out.glob("d-*")), [])

    def test_a_nearly_full_release_leaves_a_marker(self):
        s = self.pack("--assets", "990")
        self.assertEqual(s["decision"], "needs-nightly:release-full")

    def test_a_rev_that_is_not_a_commit_id_is_refused_before_anything_is_written(self):
        for bad in ("../../etc/x", "a" * 39, "A" * 40, "a" * 40 + "; rm -rf /", ""):
            r = subprocess.run(
                [sys.executable, str(SCRIPT), "pack", "--rev", bad, "--new", str(self.new), "--out", str(self.out)],
                env=self.env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(r.returncode, 2, (bad, r.stderr))
        self.assertFalse(self.out.exists())

    def test_nothing_new_is_an_empty_marker_not_a_delta(self):
        self.new.write_text(HEADER + "\n")
        s = self.pack()
        self.assertEqual(s["decision"], "empty")
        self.assertTrue((self.out / "empty").exists())


class Decide(unittest.TestCase):
    def test_boundaries(self):
        self.assertEqual(lc.decide(100, 0, 100), "publish")
        self.assertEqual(lc.decide(101, 0, 100), "needs-nightly:over-budget")
        self.assertEqual(lc.decide(1, 989, 100), "publish")
        self.assertEqual(lc.decide(1, 990, 100), "needs-nightly:release-full")
        self.assertEqual(lc.decide(10**12, 990, 100), "needs-nightly:release-full")  # a full release is reported before the size


if __name__ == "__main__":
    unittest.main()
