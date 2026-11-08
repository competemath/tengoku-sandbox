#!/usr/bin/env python3
"""topup.py — the small, frequent half of the build cache.

The nightly cache is the whole compiled tree (gigabytes, once a day). A top-up
is only what differs from it at a later commit: the build outputs of the modules
that changed, a few megabytes. Top-ups are cumulative (always relative to the
base), so a consumer needs the base plus exactly one top-up, never a chain.

  topup.py make --tip <sha> --out <dir>     pack what was built after the base was unpacked
  topup.py apply --file <tar.zst> --manifest <json>   overlay it, keeping the base's files aside
  topup.py rollback                          put the base's files back
  topup.py status                            what is overlaid right now

Only module outputs under build/lib/lean/Tengoku* and build/ir/Tengoku* travel;
candidate modules and tool binaries never do. `apply` refuses a file whose
digest differs from the manifest and any path outside those two trees.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time
from pathlib import Path

ROOT = Path(os.environ.get("TENGOKU_TOPUP_ROOT") or Path(__file__).resolve().parents[1])
LAKE = ROOT / ".lake"
MARKER = LAKE / ".topup-marker"  # touched right after the base cache is unpacked
BASE = LAKE / ".cache-base"  # "<tag> <commit>" of the unpacked base
APPLIED = LAKE / ".topup-applied.json"
BACKUP = LAKE / ".topup-backup"
KEEP = re.compile(r"^build/(lib/lean|ir)/Tengoku([/.]|$)")


SETUP_JSON = ".setup.json"  # Lake's scratch input for compiling one module (1-2 MB each, 80 of the tree's 102 GB): never read for an up-to-date module, never shipped


def wanted(rel: str) -> bool:
    return bool(KEEP.match(rel)) and "/_candidate_" not in rel and ".." not in Path(rel).parts and not rel.endswith(SETUP_JSON)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def applied() -> dict:
    try:
        return json.loads(APPLIED.read_text())
    except Exception:
        return {}


def make(tip: str, out: Path) -> int:
    if not MARKER.exists():
        print("no base marker: unpack a base cache with `cache.sh get` first", file=sys.stderr)
        return 1
    cut = MARKER.stat().st_mtime_ns
    files: set[str] = set()
    build = LAKE / "build"
    for p in build.rglob("*"):
        if p.is_file() and not p.is_symlink():
            rel = p.relative_to(LAKE).as_posix()
            if wanted(rel) and p.stat().st_mtime_ns > cut:
                files.add(rel)
    # Cumulative: whatever an earlier top-up laid down is still a difference from the base.
    for rel in applied().get("files", []):
        if (LAKE / rel).is_file() and wanted(rel):
            files.add(rel)
    ordered = sorted(files)
    out.mkdir(parents=True, exist_ok=True)
    tar_path = out / f"topup-{tip}.tar.zst"
    zstd = subprocess.Popen(["zstd", "-T0", "-3", "-q", "-f", "-o", str(tar_path)], stdin=subprocess.PIPE)
    with tarfile.open(fileobj=zstd.stdin, mode="w|") as tar:
        for rel in ordered:
            tar.add(LAKE / rel, arcname=rel, recursive=False)
    zstd.stdin.close()
    if zstd.wait() != 0:
        print("zstd failed", file=sys.stderr)
        return 1
    base_tag, _, base_commit = (BASE.read_text().strip() if BASE.exists() else "").partition(" ")
    manifest = {
        "tip": tip,
        "base_tag": base_tag,
        "base_commit": base_commit,
        "files": ordered,
        "bytes": tar_path.stat().st_size,
        "sha256": sha256(tar_path),
        "made_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    (out / f"topup-{tip}.json").write_text(json.dumps(manifest, indent=1) + "\n")
    print(f"top-up for {tip[:12]}: {len(ordered)} files, {manifest['bytes']} bytes (base {base_tag or '?'})")
    return 0


def put_back(rel: str) -> None:
    """Move a kept-aside base file back into place (a rename: atomic, and a process that has the
    top-up's version mapped keeps it)."""
    target = LAKE / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    os.replace(BACKUP / rel, target)


def keep_aside(rel: str) -> None:
    """Keep the base version of a file the top-up is about to replace. A hard link: instant, and the
    base file's contents stay alive for any running process that has them mapped."""
    keep = BACKUP / rel
    keep.parent.mkdir(parents=True, exist_ok=True)
    keep.unlink(missing_ok=True)
    try:
        os.link(LAKE / rel, keep)
    except OSError:
        shutil.copy2(LAKE / rel, keep)


def rollback(quiet: bool = False) -> int:
    state = applied()
    if not state:
        if not quiet:
            print("no top-up is applied")
        return 0
    for rel in state.get("created", []):
        (LAKE / rel).unlink(missing_ok=True)
    for rel in state.get("overwritten", []):
        if (BACKUP / rel).is_file():
            put_back(rel)
    shutil.rmtree(BACKUP, ignore_errors=True)
    APPLIED.unlink(missing_ok=True)
    if not quiet:
        print(f"rolled back the top-up for {state.get('tip', '?')[:12]}: the build directory is the base again")
    return 0


def undo(created: set[str], overwritten: set[str]) -> None:
    """Back to the base after an apply that stopped halfway: what it created goes, what it replaced is put back from the kept-aside copies (the previous top-up's files too)."""
    for rel in created:
        (LAKE / rel).unlink(missing_ok=True)
    for rel in overwritten:
        if (BACKUP / rel).is_file():
            put_back(rel)
    shutil.rmtree(BACKUP, ignore_errors=True)
    APPLIED.unlink(missing_ok=True)


def apply(tar_path: Path, manifest_path: Path) -> int:
    manifest = json.loads(manifest_path.read_text())
    if sha256(tar_path) != manifest.get("sha256"):
        print("REFUSED: the top-up's digest does not match its manifest — not unpacking", file=sys.stderr)
        return 1
    # a top-up published before 2026-10-14 lists *.setup.json files: they are skipped below, the rest is applied
    bad = [f for f in manifest.get("files", []) if not f.endswith(SETUP_JSON) and not wanted(f)]
    if bad:
        print(f"REFUSED: the top-up names paths outside the module trees: {bad[:3]}", file=sys.stderr)
        return 1
    prev = applied()
    if prev.get("tip") == manifest["tip"]:
        print(f"top-up for {manifest['tip'][:12]} is already applied")
        return 0
    created = set(prev.get("created", []))
    overwritten = set(prev.get("overwritten", []))
    listed = {f for f in manifest["files"] if not f.endswith(SETUP_JSON)}
    # A module that went back to its base content is absent from the newer top-up: undo it here too.
    for rel in sorted((created | overwritten) - listed):
        target = LAKE / rel
        if rel in overwritten and (BACKUP / rel).is_file():
            put_back(rel)
        else:
            target.unlink(missing_ok=True)
        created.discard(rel)
        overwritten.discard(rel)
    for rel in listed:
        if rel in created or rel in overwritten:
            continue  # its base version (or absence) is already recorded
        target = LAKE / rel
        if target.is_file():
            keep_aside(rel)
            overwritten.add(rel)
        else:
            created.add(rel)
    # A stream, never the whole archive in memory: a top-up grows with every merge since the nightly base (772 MB packed, 10.6 GB unpacked on 2026-10-11, after the
    # openai-math parts) and holding it as bytes (twice, with the copy `capture_output` joins) killed the queue's runner 'with a shutdown signal' in every Lean build.
    # the archive's absolute path after `--`: a name that begins with a dash is a file here, never an option of zstd (SonarCloud S8705 on the argument that came from the command line)
    zstd = subprocess.Popen(["zstd", "-d", "-q", "-c", "--", str(tar_path.resolve(strict=True))], stdout=subprocess.PIPE)
    assert zstd.stdout is not None
    problem = ""
    fresh: Path | None = None
    try:
        with tarfile.open(fileobj=zstd.stdout, mode="r|") as tar:
            for member in tar:
                if member.isfile() and member.name.endswith(SETUP_JSON):
                    continue  # an old top-up's scratch file: not written
                if not member.isfile() or member.name not in listed:
                    problem = f"names an unexpected member {member.name!r}"
                    break
                target = LAKE / member.name
                target.parent.mkdir(parents=True, exist_ok=True)
                # Never write into a file in place: the services keep serving from a Lean process that has the
                # old file mapped while the new one arrives. Write beside it, then rename over it.
                fresh = target.with_name(target.name + ".topup-new")
                with tar.extractfile(member) as src, fresh.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
                os.utime(fresh, (member.mtime, member.mtime))
                os.replace(fresh, target)
                fresh = None
        if not problem:
            while zstd.stdout.read(
                1 << 20
            ):  # the padding after the end-of-archive blocks: read it, or zstd dies of SIGPIPE and a good archive looks broken
                pass
    except tarfile.TarError:
        problem = "does not decompress"  # a stream that stops short or is not a tar
    except Exception as e:  # noqa: BLE001  a full disk, anything: files are replaced as the stream arrives, so every failure must put the base back
        problem = f"could not be unpacked ({type(e).__name__}: {e})"
    finally:
        if problem and zstd.poll() is None:
            zstd.kill()
        zstd.stdout.close()
        if fresh is not None:
            fresh.unlink(missing_ok=True)
    if zstd.wait() != 0 and not problem:
        problem = "does not decompress"
    if problem:
        undo(created, overwritten)
        print(f"REFUSED: the top-up {problem}", file=sys.stderr)
        return 1
    APPLIED.write_text(
        json.dumps(
            {
                "tip": manifest["tip"],
                "base_tag": manifest.get("base_tag"),
                "files": sorted(listed),
                "created": sorted(created),
                "overwritten": sorted(overwritten),
            }
        )
        + "\n"
    )
    print(f"applied the top-up for {manifest['tip'][:12]}: {len(listed)} files over base {manifest.get('base_tag') or '?'}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("make")
    m.add_argument("--tip", required=True)
    m.add_argument("--out", required=True)
    a = sub.add_parser("apply")
    a.add_argument("--file", required=True)
    a.add_argument("--manifest", required=True)
    sub.add_parser("rollback")
    sub.add_parser("status")
    args = ap.parse_args()
    if args.cmd == "make":
        return make(args.tip, Path(args.out))
    if args.cmd == "apply":
        return apply(Path(args.file), Path(args.manifest))
    if args.cmd == "rollback":
        return rollback()
    state = applied()
    print(
        json.dumps(
            {"tip": state.get("tip"), "files": len(state.get("files", [])), "base": BASE.read_text().strip() if BASE.exists() else None}
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
