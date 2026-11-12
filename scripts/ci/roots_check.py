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

import io
import re
import sys
import tarfile
import tempfile
from pathlib import Path

from _git import ROOT, changed_files, fail, run, run_bytes
from restructure_check import blob_ids, commit_of, differences

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


def extract(base: str, paths: list[str], dest: Path) -> None:
    archive = run_bytes("archive", base, *paths)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(
            dest, **({"filter": "data"} if hasattr(tarfile, "data_filter") else {})
        )  # the base commit's own files, in a private directory


def owned_head(head: str, libs: list[str], manifests: list[str]) -> dict[str, tuple[str, str]]:
    """path -> (mode, blob) of the modules of the libraries and of the manifests, as the PR has them."""
    state = {}
    for entry in filter(None, run("ls-tree", "-r", "-z", head, "--", *(f"Tengoku/{lib}" for lib in libs), *manifests).split("\0")):
        meta, path = entry.split("\t", 1)
        mode, _kind, blob = meta.split()
        state[path] = (mode, blob)
    return state


def owned_expected(tree: Path, libs: list[str], manifests: list[str]) -> dict[str, tuple[str, str]]:
    files = sorted(
        p for p in [*(f for lib in libs for f in (tree / "Tengoku" / lib).rglob("*")), *(tree / m for m in manifests)] if p.is_file()
    )
    return {p.relative_to(tree).as_posix(): ("100644", blob) for p, blob in zip(files, blob_ids(files))}


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
    missing = [lib for lib in libs if not run("ls-tree", "--name-only", base, f"Tengoku/{lib}", check=False).strip()]
    if missing:
        fail(f"no such library at the base: {', '.join(missing)}")
    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp) / "tree"
        reports_dir = Path(tmp) / "reports"
        reports_dir.mkdir()
        tree.mkdir()
        extract(base, [*(f"Tengoku/{lib}" for lib in libs), *manifests], tree)
        for lib, path in reports.items():
            (reports_dir / f"{lib}.txt").write_text(run("show", f"{head}:{path}"), encoding="utf-8")
        done = roots_tree.apply(tree, reports_dir)
        errors = differences(owned_expected(tree, libs, manifests), owned_head(head, libs, manifests))
    if errors:
        fail("roots PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    print(
        "roots ok: the PR is exactly scripts/roots_tree.py's output on the base ("
        + ", ".join(f"{lib} {v['qualified']}" for lib, v in sorted(done.items()))
        + ")"
    )


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
