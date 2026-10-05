#!/usr/bin/env python3
"""restructure_check.py <base> <head> — the checks of a RESTRUCTURE PR.

A restructure PR moves the seed into Tengoku/Seed/ (scripts/restructure.py). Nothing of it is read as a diff: it is
recomputed. The script of the BASE commit (the gate's, never the PR's) runs on the base tree, and the PR must be exactly its
output: every file the script owns, every byte, the executable bits, and no other file touched. A PR that differs from what anyone
can regenerate in a clean checkout by a single line is refused. The script changes only imports and `include_str` paths; the
queue's cache build compiles the result.

    restructure_check.py <base> <head>
"""

from __future__ import annotations

import io
import os
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

from _git import ROOT, changed_files, fail, run, run_bytes

OWNED = ("Tengoku.lean", "SEED.md", "LICENSE-THIRD-PARTY.md")  # besides everything under Tengoku/, the files the script may write
NEEDED = (*OWNED, "Tengoku", "NOTICE", "widget")  # what the script and its verify step read from the base tree


def has_seed(rev: str) -> bool:
    """An unreadable revision has none: the probe fails towards "not a restructure", the stricter classes."""
    return bool(run("ls-tree", "--name-only", rev, "Tengoku/Seed", check=False).strip())


def is_restructure(base: str, head: str) -> bool:
    """A change that creates Tengoku/Seed/ in a tree that has none (never for the index: `--staged`)."""
    return head != "--staged" and not has_seed(base) and has_seed(head)


def owned(path: str) -> bool:
    return path.startswith("Tengoku/") or path in OWNED


def extract_base(base: str, dest: Path) -> None:
    present = set(run("ls-tree", "--name-only", base).split("\n"))
    archive = run_bytes("archive", base, *[p for p in NEEDED if p in present])
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(
            dest, **({"filter": "data"} if hasattr(tarfile, "data_filter") else {})
        )  # the base commit's own files, in a private directory


def head_state(head: str) -> dict[str, tuple[str, str]]:
    """path -> (mode, blob) of everything the script owns, as the PR has it."""
    state = {}
    for entry in filter(None, run("ls-tree", "-r", "-z", head, "--", "Tengoku", *OWNED).split("\0")):
        meta, path = entry.split("\t", 1)
        mode, _kind, blob = meta.split()
        state[path] = (mode, blob)
    return state


def commit_of(rev: str) -> str:
    """The commit a revision names, as a full hash: what the git commands below are given, never the argument itself."""
    sha = run("rev-parse", "--verify", "--end-of-options", f"{rev}^{{commit}}", check=False).strip()
    if not sha:
        fail(f"{rev!r} names no commit")
    return sha


def blob_ids(paths: list[Path]) -> list[str]:
    r = subprocess.run(
        ["git", "hash-object", "--stdin-paths"],
        cwd=ROOT,
        input="\n".join(map(str, paths)) + "\n",
        capture_output=True,
        text=True,
        check=True,
    )
    return r.stdout.split()


def expected_state(tree: Path) -> dict[str, tuple[str, str]]:
    files = sorted(p for p in [*(tree / "Tengoku").rglob("*"), *(tree / f for f in OWNED)] if p.is_file())
    state = {}
    for p, blob in zip(files, blob_ids(files)):
        state[p.relative_to(tree).as_posix()] = ("100755" if os.stat(p).st_mode & 0o111 else "100644", blob)
    return state


def differences(expected: dict, actual: dict) -> list[str]:
    errors = [f"{p}: the PR does not have it" for p in sorted(expected.keys() - actual.keys())]
    errors += [f"{p}: the PR has a file the script does not produce" for p in sorted(actual.keys() - expected.keys())]
    errors += [f"{p}: differs from the script's output" for p in sorted(expected.keys() & actual.keys()) if expected[p] != actual[p]]
    return errors


def main(base: str, head: str) -> None:
    sys.path.insert(0, str(ROOT / "scripts"))
    import restructure

    base, head = commit_of(base), commit_of(head)
    if not is_restructure(base, head):
        fail("not a restructure: the base already has Tengoku/Seed, or the head has none")
    stray = [p for _, p in changed_files(base, head) if not owned(p)]
    if stray:
        fail(f"a restructure PR touches only what scripts/restructure.py owns; also: {', '.join(stray[:10])}")
    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp)
        extract_base(base, tree)
        done = restructure.apply(tree, restructure.libs_from_paths(run("ls-tree", "-r", "--name-only", base, "data").splitlines()))
        errors = restructure.verify(tree) + differences(expected_state(tree), head_state(head))
    if errors:
        fail("restructure PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    print(
        "restructure ok: the PR is exactly scripts/restructure.py's output on the base ("
        + ", ".join(f"{v} {k}" for k, v in sorted(done.items()))
        + ")"
    )


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
