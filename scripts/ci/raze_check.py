#!/usr/bin/env python3
"""raze_check.py <base> <head> — the checks of a RAZE PR (docs/pr-classes.md, section 8).

A raze PR takes modules of a library that arrived as an intake bundle OUT of the tree, so that a corrected bundle can bring them back. It exists because a part is cut from the tree
(`from_tree`): it can only add modules, and the modules merged by an earlier part cannot be repaired (2026-10-11: the first pruner cut declarations that later parts name, and every
later part of openai-math, navier-stokes-euler and lean-pool lost the modules that named them). Razing the deficient modules lets the next cut bring them back, rebuilt.

It is the one operation that removes content from the tree, so it is judged strictly, and a code owner has to read it. The PR carries a marker, data/raze/<id>.json:

    {"library": "openai-math", "modules": ["Tengoku.OpenaiMath.OAI.Analysis.Daugavet.Enlargement", …], "reason": "…"}      or      {"library": …, "all": true, "reason": "…"}

The marker is under data/, which CODEOWNERS leaves to its default owners: that is what makes the review mandatory (no line of the content lane covers it). What this script requires:
  - exactly one marker, added by the PR, with a reason; the library is in the tree at the base as an intake bundle (data/intake/<library>/manifest.jsonl), and every module of the marker
    is a module of that library at the base (at most MAX_MODULES in a partial raze);
  - nothing but the removal: the files the PR deletes are exactly the marker's modules; the umbrella Tengoku/<Ns>.lean loses exactly their import lines and gains nothing; the manifest
    loses exactly the lines of their records, every other line unchanged and in its place; no other file changes. A whole-library raze (`all`) deletes the library's folder, umbrella
    and data/intake/<library>/ and removes the one import line of the library from Tengoku/All.lean;
  - the dependencies go with it: no module that remains in the library imports a razed module, and every record that remains names a module that remains. (Other libraries
    importing a razed module are found over the whole tree by scripts/ci/imports_resolve.py, which every PR that deletes a module runs, on the PR and again in the merge queue.)
The merge queue then builds the whole library as it will be (`lake build Tengoku.All`) and holds a group that deletes a Lean file responsible for a failure.
"""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _git import blob, changed_files, fail, module_name, module_stem, pascal, run  # noqa: E402
from imports_resolve import header_imports, read_blobs  # noqa: E402

MARKER = re.compile(r"data/raze/([A-Za-z0-9][A-Za-z0-9._-]{0,80})\.json")
MAX_MODULES = 800


def is_raze(base: str, head: str) -> bool:
    """A PR that adds a marker data/raze/<id>.json is a raze PR (whatever else it does is then judged by this script, and refused if it is not a removal)."""
    return any(st == "A" and MARKER.fullmatch(p) for st, p in changed_files(base, head))


def lines_of(rev: str, path: str) -> list[str] | None:
    data = blob(rev, path)
    return None if data is None else data.decode("utf-8", "replace").split("\n")


def library_modules(rev: str, ns: str) -> dict[str, str]:
    """{module name: path} of the .lean files below Tengoku/<ns>/ at rev."""
    out = {}
    for p in run("ls-tree", "-r", "--name-only", rev, f"Tengoku/{ns}").splitlines():
        if p.endswith(".lean"):
            out[module_name(p[: -len(".lean")])] = p
    return out


def read_marker(head: str, path: str) -> dict:
    try:
        m = json.loads(blob(head, path) or b"")  # the diff lists the marker as added, so it is there; an unreadable one is not JSON
    except Exception as e:  # noqa: BLE001
        fail(f"{path}: not JSON: {e}")
    if not isinstance(m, dict) or set(m) - {"library", "modules", "all", "reason"}:
        fail(f"{path}: a marker has the fields library, modules (or all: true) and reason, nothing else")
    if not isinstance(m.get("library"), str) or not m["library"]:
        fail(f"{path}: `library` is the library's key (the folder name of data/intake/<library>)")
    if not isinstance(m.get("reason"), str) or len(m["reason"].strip()) < 10:
        fail(f"{path}: `reason` says why in a sentence: the reviewer reads it first")
    whole = m.get("all") is True
    if whole == bool(m.get("modules")):
        fail(f"{path}: give `modules` (a list of module names) or `all: true`, not both and not neither")
    if not whole and (
        not isinstance(m["modules"], list)
        or not all(isinstance(x, str) for x in m["modules"])
        or len(set(m["modules"])) != len(m["modules"])
    ):
        fail(f"{path}: `modules` is a list of distinct module names")
    return m


@dataclass
class Raze:
    """What the PR razes, read from its marker and the base."""

    base: str
    head: str
    files: list[tuple[str, str]]
    marker_path: str
    lib: str
    ns: str
    whole: bool
    razed: set[str]
    present: dict[str, str]  # module -> path, at the base
    manifest_path: str
    old_manifest: list[str]

    @property
    def umbrella(self) -> str:
        return f"Tengoku/{self.ns}.lean"


def load(base: str, head: str) -> Raze:
    files = changed_files(base, head)
    markers = [p for st, p in files if MARKER.fullmatch(p) and st == "A"]
    if len(markers) != 1:
        fail(f"a raze PR adds exactly one marker data/raze/<id>.json (found {len(markers)})")
    m = read_marker(head, markers[0])
    lib, ns, whole = m["library"], pascal(m["library"]), m.get("all") is True
    manifest_path = f"data/intake/{lib}/manifest.jsonl"
    old_manifest = lines_of(base, manifest_path)
    if old_manifest is None:
        fail(
            f"{lib} is not a library of the tree at the base: there is no {manifest_path} (only a library that arrived as an intake bundle can be razed)"
        )
    present = library_modules(base, ns)
    if not present:
        fail(f"Tengoku/{ns}/ has no module at the base")
    # a name may be written with or without guillemets (`Tengoku.Lib.«A-B»`): both are the module the file is
    razed = set(present) if whole else {module_name(module_stem(x)) for x in m["modules"]}
    stray = sorted(x for x in razed if x not in present)
    if stray:
        fail(f"modules the marker names that are not modules of {lib} at the base (a name is `Tengoku.{ns}.…`): " + ", ".join(stray[:5]))
    if not whole and len(razed) > MAX_MODULES:
        fail(f"a partial raze removes at most {MAX_MODULES} modules (this one {len(razed)}): split it, or raze the whole library")
    return Raze(base, head, files, markers[0], lib, ns, whole, razed, present, manifest_path, old_manifest)


def file_errors(r: Raze) -> list[str]:
    """Nothing but the removal: the files deleted are exactly the marker's, and no file outside the allowed ones changes."""
    errors: list[str] = []
    expected_deleted = {r.present[x] for x in r.razed}
    allowed_other: set[str] = set()
    if r.whole:
        expected_deleted.add(r.umbrella)
        expected_deleted |= set(run("ls-tree", "-r", "--name-only", r.base, f"data/intake/{r.lib}").splitlines())
        allowed_other.add("Tengoku/All.lean")
    else:
        allowed_other |= {r.umbrella, r.manifest_path}
    deleted = {p for st, p in r.files if st == "D"}
    if deleted != expected_deleted:
        missing, extra = sorted(expected_deleted - deleted), sorted(deleted - expected_deleted)
        if missing:
            errors.append(f"the marker razes files the PR does not delete: {', '.join(missing[:4])}")
        if extra:
            errors.append(f"the PR deletes files the marker does not name: {', '.join(extra[:4])}")
    allowed = f"the files it removes, the umbrella, the manifest{' and Tengoku/All.lean' if r.whole else ''} and its marker"
    for st, p in r.files:
        if p == r.marker_path or (st == "D" and p in expected_deleted) or (st == "M" and p in allowed_other):
            continue
        errors.append(f"{p}: a raze PR changes nothing but {allowed} (this one is {st})")
    return errors


def import_line_errors(r: Raze, path: str, gone: set[str]) -> list[str]:
    """The umbrella (partial) or All.lean (whole): exactly the import lines of the razed modules go."""
    old, new = lines_of(r.base, path), lines_of(r.head, path)
    if old is None or new is None:
        return [f"{path}: not readable at the base and the head"]
    want = [ln for ln in old if not (ln.startswith("import ") and ln[len("import ") :].strip() in gone)]
    if new == want:
        return []
    return [f"{path}: must lose exactly the import line(s) of {', '.join(sorted(gone)[:3])}… and nothing else"]


def module_of_line(ln: str) -> str | None:
    try:
        return json.loads(ln).get("module")
    except Exception:  # noqa: BLE001
        return None


def manifest_errors(r: Raze) -> list[str]:
    """The manifest loses exactly the records of the razed modules, in place, and no record that remains names a module that does not."""
    new = lines_of(r.head, r.manifest_path)
    if new is None:
        return [f"{r.manifest_path}: not readable at the head"]
    errors: list[str] = []
    want = [ln for ln in r.old_manifest if ln.strip() == "" or module_of_line(ln) not in r.razed]
    if new != want:
        errors.append(
            f"{r.manifest_path}: must lose exactly the lines of the records of the razed modules, every other line unchanged and in its place"
        )
    modules = {mod for ln in new if (mod := module_of_line(ln))}
    gone_but_named = sorted(modules & r.razed)
    if gone_but_named:
        errors.append(f"{r.manifest_path}: records of razed modules remain: {', '.join(gone_but_named[:3])}")
    dangling = sorted(modules - (set(r.present) - r.razed))
    if dangling:
        errors.append(f"{r.manifest_path}: records that remain name modules that do not remain: {', '.join(dangling[:3])}")
    return errors


def dependency_errors(r: Raze) -> list[str]:
    """The dependencies go with it: nothing that remains in the library imports a razed module."""
    errors: list[str] = []
    for path, text in read_blobs(r.head, [r.present[x] for x in r.present if x not in r.razed]).items():
        used = sorted(set(header_imports(text)) & r.razed)
        if used:
            errors.append(f"{path} remains but imports {', '.join(used[:3])}, which the marker razes: raze it too, or leave the module")
    return errors


def main() -> None:
    r = load(sys.argv[1], sys.argv[2])
    errors = file_errors(r)
    if r.whole:
        errors += import_line_errors(r, "Tengoku/All.lean", {f"Tengoku.{r.ns}"})
    else:
        errors += import_line_errors(r, r.umbrella, r.razed) + manifest_errors(r) + dependency_errors(r)
    if errors:
        shown = errors[:20] + ([f"… and {len(errors) - 20} more"] if len(errors) > 20 else [])
        fail("raze PR:\n  " + "\n  ".join(shown))
    print(
        f"raze OK: {len(r.razed)} module(s) of {r.lib}{' (the whole library)' if r.whole else ''}; a code owner reads the marker {r.marker_path}"
    )


if __name__ == "__main__":
    main()
