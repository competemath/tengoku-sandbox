#!/usr/bin/env python3
"""Promote staging translations into the trusted tree.

A staging record passed both gates as a standalone script. It is TRUSTED
only once its module builds in the tree. For every source file that has
staging records (or just --only <source_path>):

  1. generate the file's module from its trusted AND staging records into a
     `_candidate_` sibling file (scripts/generate.py --candidate) — the real
     module and the aggregator are untouched;
  2. `lake build` that candidate — no errors, no `sorry`;
  3. only then move the file's staging records to data/trusted/<library>.jsonl
     (status "trusted", promoted_at) and regenerate the real module;
  4. on failure the records stay in staging with build_error.

Trusted never gains a record whose module has not built. Nothing that does
not build is importable through Tengoku.All.

  python3 scripts/promote.py --corpus <corpus checkout> --library equational-theories
        [--only <source_path>] [--quiescent SECONDS]

--quiescent skips a file that received a staging record in the last SECONDS
(a file being banked every few seconds would otherwise rebuild its whole
module per bank); records without `staged_at` count as quiet. Concurrent
promotions serialise on data/.promote.lock, and each file's state is read
fresh under the lock.

Exit 0 when everything promoted (or nothing was due), 2 when some file did
not build.
"""

import argparse
import fcntl
import json
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate import pascal  # noqa: E402


def load(p: Path) -> list[dict]:
    return [json.loads(l) for l in p.read_text(encoding="utf-8").splitlines() if l.strip()] if p.exists() else []


def dump(p: Path, recs: list[dict]) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(p.suffix + ".tmp")
    tmp.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs), encoding="utf-8")
    tmp.replace(p)


def module_of(lib_ns: str, corpus_prefix: str, source_path: str, lib_dir: Path) -> tuple[str, Path]:
    rel = Path(source_path)
    if rel.parts and rel.parts[0] == corpus_prefix:
        rel = Path(*rel.parts[1:])
    return f"Tengoku.{lib_ns}." + ".".join(rel.with_suffix("").parts), lib_dir / rel


def run(cmd: list[str], cwd: Path, timeout: float) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return 124, f"timed out after {timeout:.0f}s: {' '.join(cmd)} {(e.stdout or '')[-500:]}"
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def newest_staged_at(recs: list[dict]) -> float:
    t = 0.0
    for r in recs:
        s = r.get("staged_at")
        if not s:
            continue
        try:
            t = max(t, datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp())
        except ValueError:
            pass
    return t


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="checkout of the corpus (dir containing e.g. equational_theories/)")
    ap.add_argument("--library", required=True)
    ap.add_argument("--only", default=None, help="promote just this source_path's records")
    ap.add_argument("--quiescent", type=float, default=0.0, help="skip files with a record staged in the last N seconds")
    ap.add_argument("--out", default=".")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    lib = args.library
    lib_ns = pascal(lib)
    corpus_prefix = lib.replace("-", "_")
    lib_dir = out / "Tengoku" / lib_ns
    staging_p = out / "data" / "staging" / f"{lib}.jsonl"
    trusted_p = out / "data" / "trusted" / f"{lib}.jsonl"
    staging_dir = out / "data" / "staging" / lib  # one file per contributor PR

    def staging_files():
        return ([staging_p] if staging_p.exists() else []) + (sorted(staging_dir.glob("*.jsonl")) if staging_dir.is_dir() else [])

    def load_staging():
        return [r for f in staging_files() for r in load(f)]

    def dump_staging(recs):
        """Write the remaining records back to the files they came from (names are unique per library);
        a per-PR file with nothing left is removed, the flat file is kept (possibly empty)."""
        keep = {r.get("name") for r in recs}
        for f in staging_files():
            mine = [r for r in load(f) if r.get("name") in keep]
            if mine or f == staging_p:
                dump(f, mine)
            else:
                f.unlink()

    lock_p = out / "data" / ".promote.lock"
    lock_p.parent.mkdir(parents=True, exist_ok=True)
    gen = [sys.executable, "scripts/generate.py", "--corpus", args.corpus, "--libraries", lib]

    files = sorted(
        {
            r["source_path"]
            for r in load_staging()
            if r.get("source_path") and r.get("context") is not None and (not args.only or r["source_path"] == args.only)
        }
    )
    if not files:
        print(f"{lib}: nothing to promote")
        return 0

    promoted = 0
    skipped = 0
    failed: list[tuple[str, int, str]] = []
    for sp in files:
        with open(lock_p, "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            staging = load_staging()
            recs = [r for r in staging if r.get("source_path") == sp and r.get("context") is not None]
            if not recs:
                continue
            if args.quiescent and time.time() - newest_staged_at(recs) < args.quiescent:
                skipped += 1
                continue
            mod, real_path = module_of(lib_ns, corpus_prefix, sp, lib_dir)
            cand_path = real_path.with_name("_candidate_" + real_path.name)
            head, leaf = mod.rsplit(".", 1)
            cand_mod = f"{head}._candidate_{leaf}"
            try:
                rc, o = run(gen + ["--candidate", sp], out, 600)
                if rc == 0:
                    rc, o = run(["lake", "build", cand_mod], out, 3600)
                    if rc == 0 and "declaration uses `sorry`" in o:
                        rc, o = 1, "a trusted module may not use sorry\n" + o
                if rc != 0:
                    err = " ".join(o.split())[-1500:]
                    ids = {id(r) for r in recs}
                    for r in staging:
                        if id(r) in ids:
                            r["build_error"] = err[-600:]
                    dump_staging(staging)
                    failed.append((sp, len(recs), err))
                    print(f"NOT promoted ({len(recs)}) {sp}: {err[-500:]}")
                    continue
                now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
                moved = []
                for r in recs:
                    m = dict(r, status="trusted", promoted_at=now)
                    m.pop("build_error", None)
                    moved.append(m)
                ids = {id(r) for r in recs}
                trusted = load(trusted_p) + moved
                staging = [r for r in staging if id(r) not in ids]
                dump(trusted_p, trusted)
                dump_staging(staging)
                rc, o = run(gen + ["--only", sp], out, 600)
                if rc != 0:
                    print(f"WARNING: regeneration after promotion failed for {sp}: {' '.join(o.split())[-300:]}")
                promoted += len(moved)
                print(f"promoted {len(moved)} -> {mod}")
            finally:
                try:
                    cand_path.unlink()
                except FileNotFoundError:
                    pass
    print(
        f"{lib}: promoted {promoted}; not promoted {sum(n for _, n, _ in failed)} in {len(failed)} file(s); {skipped} file(s) still being banked"
    )
    return 0 if not failed else 2


if __name__ == "__main__":
    sys.exit(main())
