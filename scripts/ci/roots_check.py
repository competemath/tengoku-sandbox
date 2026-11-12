#!/usr/bin/env python3
"""roots_check.py <base> <head> — the checks of a ROOTS PR.

A roots PR gives the declarations that sit in the root namespace in the modules of some libraries the namespace of their library (`Tengoku.<Library>.<name>`), the way the factory has done for
every bundle since emissary-archangel#179 (scripts/roots_tree.py). Nothing of it is read as a diff: it is recomputed, as for a restructure PR (docs/pr-classes.md, section 5). The PR adds the
reports it was computed from, `data/roots/<id>/<Library>.txt` (the `root:` lines of tengoku-leakscan, the root-inventory workflow's artifact); the script of the BASE commit (the gate's, never the
PR's) runs on the base's files of those libraries and on the intake manifests, and the PR must be exactly its output: every module of those libraries, every manifest, every byte. A PR that
differs from what anyone can regenerate in a clean checkout by one line, or touches one other file, is refused. The merge queue builds the libraries and the whole tree.

    roots_check.py <base> <head>
"""

from __future__ import annotations

import re
import subprocess
import sys

from _git import ROOT, changed_files, fail, run
from restructure_check import commit_of

REPORT = re.compile(r"data/roots/([A-Za-z0-9][A-Za-z0-9._-]*)/([A-Za-z][A-Za-z0-9]*)\.txt")
MANIFEST = re.compile(r"data/intake/[^/]+/manifest\.jsonl")


def added_reports(base: str, head: str) -> dict[str, str]:
    """library -> path of the report a PR adds under data/roots/ (a library once)"""
    out: dict[str, str] = {}
    for status, path in changed_files(base, head):
        if status == "A" and (m := REPORT.fullmatch(path)):
            out[m.group(2)] = path
    return out


def is_roots(base: str, head: str) -> bool:
    """A change that adds a root report (never for the index: `--staged`)."""
    return head != "--staged" and bool(added_reports(base, head))


def base_manifests(base: str) -> list[str]:
    return [p for p in run("ls-tree", "-r", "--name-only", base, "data/intake").splitlines() if MANIFEST.fullmatch(p)]


def listing(rev: str, libs: list[str], manifests: list[str]) -> dict[str, str]:
    """path -> mode of the files of the libraries and of the manifests, at a revision"""
    state = {}
    for entry in filter(None, run("ls-tree", "-r", "-z", rev, "--", *(f"Tengoku/{lib}" for lib in libs), *manifests).split("\0")):
        meta, path = entry.split("\t", 1)
        state[path] = meta.split()[0]
    return state


def read_blobs(rev: str, paths: list[str]) -> dict[str, bytes]:
    """The contents of files at a revision, in one `git cat-file --batch` (git objects only: nothing is written to disk)."""
    request = "".join(f"{rev}:{p}\n" for p in paths).encode()
    out = subprocess.run(["git", "cat-file", "--batch"], cwd=ROOT, input=request, capture_output=True, check=True).stdout
    blobs: dict[str, bytes] = {}
    at = 0
    for path in paths:
        end = out.index(b"\n", at)
        header = out[at:end].split()
        if len(header) != 3 or header[1] != b"blob":
            fail(f"{path}: not a file at {rev}")
        size = int(header[2])
        blobs[path] = out[end + 1 : end + 1 + size]
        at = end + 1 + size + 1
    return blobs


def differences(expected: dict[str, bytes], actual: dict[str, bytes]) -> list[str]:
    errors = [f"{p}: the PR does not have it" for p in sorted(expected.keys() - actual.keys())]
    errors += [f"{p}: the PR has a file the script does not produce" for p in sorted(actual.keys() - expected.keys())]
    errors += [f"{p}: differs from the script's output" for p in sorted(expected.keys() & actual.keys()) if expected[p] != actual[p]]
    return errors


def main(base: str, head: str) -> None:
    sys.path.insert(0, str(ROOT / "scripts"))
    import roots_tree  # the base's: this gate runs from the base commit's checkout

    base, head = commit_of(base), commit_of(head)
    reports = added_reports(base, head)
    if not reports:
        fail("not a roots PR: it adds no data/roots/<id>/<Library>.txt")
    libs = sorted(reports)
    ids = {REPORT.fullmatch(p).group(1) for p in reports.values()}  # type: ignore[union-attr]
    if len(ids) != 1:
        fail(f"a roots PR adds the reports of one id (data/roots/<id>/); these have {sorted(ids)}")
    manifests = base_manifests(base)
    allowed_report = set(reports.values())
    stray = []
    for status, path in changed_files(base, head):
        if path in allowed_report and status == "A":
            continue
        if status == "M" and (MANIFEST.fullmatch(path) or any(path.startswith(f"Tengoku/{lib}/") for lib in libs)):
            continue
        stray.append(f"{path} ({status})")
    if stray:
        fail(
            f"a roots PR adds its reports and modifies modules of their libraries and the intake manifests, nothing else; also: {', '.join(stray[:10])}"
        )
    base_modes = listing(base, libs, manifests)
    missing = [lib for lib in libs if not any(p.startswith(f"Tengoku/{lib}/") for p in base_modes)]
    if missing:
        fail(f"no such library at the base: {', '.join(missing)}")
    # the base's files of the libraries and the manifests, as text, and the transformation of the BASE's script on them
    base_blobs = read_blobs(base, sorted(base_modes))
    files = {p: b.decode("utf-8", errors="surrogateescape") for p, b in base_blobs.items()}
    texts = {lib: run("show", f"{head}:{path}") for lib, path in reports.items()}
    changed, done = roots_tree.qualify_files(files, texts)
    expected = {p: changed[p].encode("utf-8", errors="surrogateescape") if p in changed else b for p, b in base_blobs.items()}
    head_modes = listing(head, libs, manifests)
    head_blobs = read_blobs(head, sorted(head_modes))
    errors = differences(expected, head_blobs)
    errors += [f"{p}: its mode changed" for p in sorted(base_modes.keys() & head_modes.keys()) if base_modes[p] != head_modes[p]]
    if errors:
        fail("roots PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    print(
        "roots ok: the PR is exactly scripts/roots_tree.py's output on the base ("
        + ", ".join(f"{lib} {v['qualified']}" for lib, v in sorted(done.items()))
        + ")"
    )


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
