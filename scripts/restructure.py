#!/usr/bin/env python3
"""restructure.py — move the seed into Tengoku/Seed/ and rewrite everything that names it.

Tengoku was seeded once from upstream packages (SEED.md): their files sit at Tengoku/<topic>/… next to the libraries
of verified translations. This moves every seeded file to Tengoku/Seed/<same path>, so the seed is one folder and
the origin of a module is visible from its path, and rewrites what names the moved files:

  - seeded modules: `import Tengoku.X` becomes `import Tengoku.Seed.X` in their headers, and an `include_str` path
    that climbs out of the tree gets one more `..`;
  - library modules (Tengoku/<Library>/**, Tengoku/<Library>.lean, Tengoku/All.lean): the umbrella imports that the root
    `Tengoku` re-exports are dropped, any other seeded import is renamed as above;
  - the root aggregator Tengoku.lean, and the two documents that list the seed's paths (SEED.md, LICENSE-THIRD-PARTY.md).

A library is a name in data/: data/<tier>/<library>.jsonl or folder, or data/intake/<library>/. `--libs-from REF` reads
the names from a git ref, `--libs a,b` takes them, and without either the working tree's data/ is read. Nothing else
is guessed. The change is a pure function of the tree: the merge gate (scripts/ci/restructure_check.py) runs it on the
base commit and accepts only a PR equal to its output, and anyone can repeat it in a clean checkout:

    python3 scripts/restructure.py apply     # idempotent: a tree that has Tengoku/Seed is left alone
    python3 scripts/restructure.py verify    # every `import Tengoku…` and every `include_str` path resolves
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable

SEED = "Seed"
RESERVED = {"Seed", "Native"}  # folders of the tree that no library may be named after
# What the root `Tengoku` re-exports (the root file imports each of them publicly): a library module that imports the
# root needs none of these lines.
UMBRELLAS = frozenset(
    f"Tengoku.{m}"
    for m in ("Std", "Tactic.Aesop", "Meta.Qq", "Widgets", "Testing.Random", "Search.LeanSearchClient", "Meta.ImportGraph", "Meta.Cli")
)
KEYWORD = re.compile(r"(module|prelude)\b")  # `module  -- shake: keep-all` is a header line too
IMPORT = re.compile(r"^(?P<pre>[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?)(?P<mod>\S+)(?P<post>[ \t]*(?:--.*)?)$")
INCLUDE_STR = re.compile(r'include_str(?P<ws>\s+)(?P<path>"[^"\n]*"(?:\s*/\s*"[^"\n]*")*)')
DOC_SEED_ROW = re.compile(r"`Tengoku((?:\.[A-Za-z]+)*)`")
DOC_PATH = re.compile(r"`Tengoku/(?P<top>[A-Za-z]+)(?P<rest>[/.][^`\s]*)?`")


def pascal(s: str) -> str:
    """equational-theories -> EquationalTheories (the library's folder under Tengoku/)"""
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


def libs_from_paths(paths: Iterable[str]) -> set[str]:
    """Library names from the paths under data/: a file stem or a folder name of a tier, or an intake folder."""
    libs = set()
    for p in paths:
        parts = p.split("/")
        if parts[0] != "data" or len(parts) < 3:
            continue
        if parts[1] in ("trusted", "staging", "tentative"):
            libs.add(parts[2][: -len(".jsonl")] if len(parts) == 3 and parts[2].endswith(".jsonl") else parts[2])
        elif parts[1] == "intake":
            libs.add(parts[2])
    return libs


def libs_from_git(ref: str, cwd: Path) -> set[str]:
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", ref, "data"], cwd=cwd, capture_output=True, text=True, check=True).stdout
    return libs_from_paths(out.splitlines())


def libs_from_tree(root: Path) -> set[str]:
    data = root / "data"
    return libs_from_paths(str(p.relative_to(root)).replace("\\", "/") for p in data.rglob("*") if p.is_file() or p.parent.parent == data)


def stem(entry: Path) -> str:
    return entry.name[: -len(".lean")] if entry.is_file() and entry.suffix == ".lean" else entry.name


def seed_entries(tree: Path, namespaces: set[str]) -> list[Path]:
    """The top-level entries of Tengoku/ that are not a library, not All.lean and not the Seed folder."""
    keep = namespaces | {"All", SEED}
    return [e for e in sorted(tree.iterdir()) if not e.name.startswith(".") and stem(e) not in keep]


def header_scan(lines: list[str]) -> tuple[int, list[bool]]:
    """(end, code): the index after the file header (blank lines, comments, `module`, `prelude`, imports), and for each
    line before it whether it is code, not a line of a block comment."""
    depth, code = 0, []
    for i, ln in enumerate(lines):
        s = ln.strip()
        inside = depth > 0 or s.startswith("/-")
        if inside:
            depth = max(0, depth + s.count("/-") - s.count("-/"))
        elif s and not s.startswith("--") and not KEYWORD.match(s) and not IMPORT.match(s):
            return i, code
        code.append(not inside)
    return len(lines), code


def header_end(lines: list[str]) -> int:
    return header_scan(lines)[0]


def header_imports(lines: list[str]) -> list[str]:
    end, code = header_scan(lines)
    return [m.group("mod") for ln, ok in zip(lines[:end], code) if ok and (m := IMPORT.match(ln.rstrip("\r")))]


def rename_import(mod: str, roots: set[str]) -> str:
    parts = mod.split(".")
    if parts[0] == "Tengoku" and len(parts) > 1 and parts[1] in roots:
        return ".".join(["Tengoku", SEED, *parts[1:]])
    return mod


def rewrite_header(text: str, new_name: Callable[[str, list[str]], str | None]) -> str:
    """`new_name(module, all header imports)` -> the module the line should import, or None to drop the line."""
    lines = text.split("\n")
    end, code = header_scan(lines)
    imports = header_imports(lines)
    out = []
    for i, ln in enumerate(lines):
        cr = "\r" if ln.endswith("\r") else ""
        m = IMPORT.match(ln[: len(ln) - len(cr)]) if i < end and code[i] else None
        if not m:
            out.append(ln)
            continue
        mod = new_name(m.group("mod"), imports)
        if mod is not None:
            out.append(m.group("pre") + mod + m.group("post") + cr)
    return "\n".join(out)


def seeded_name(roots: set[str]) -> Callable[[str, list[str]], str | None]:
    return lambda mod, _imports: rename_import(mod, roots)


def library_name(roots: set[str]) -> Callable[[str, list[str]], str | None]:
    def new_name(mod: str, imports: list[str]) -> str | None:
        return None if mod in UMBRELLAS and "Tengoku" in imports else rename_import(mod, roots)

    return new_name


def climbs_out(comps: list[str], depth: int) -> bool:
    up = 0
    for c in comps:
        if c != "..":
            break
        up += 1
    return up > depth


def fix_include_str(text: str, depth: int) -> str:
    """An `include_str` path that leaves the tree (Tengoku/Seed/ now) needs one more `..` after the move."""

    def repl(m: re.Match) -> str:
        path = m.group("path")
        comps = [c for lit in re.findall(r'"([^"\n]*)"', path) for c in lit.split("/")]
        if not climbs_out(comps, depth):
            return m.group(0)
        sep = re.search(r'"(\s*/\s*)"', path)
        new = '"../' + path[1:] if sep is None else '".."' + sep.group(1) + path
        return "include_str" + m.group("ws") + new

    return "\n".join(ln if ln.lstrip().startswith("--") else INCLUDE_STR.sub(repl, ln) for ln in text.split("\n"))


def read(path: Path) -> str:
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def write_if_changed(path: Path, old: str, new: str) -> bool:
    if new == old:
        return False
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(new)
    return True


def rewrite_file(path: Path, transform: Callable[[str], str]) -> bool:
    old = read(path)
    return write_if_changed(path, old, transform(old))


def rewrite_docs(root: Path, roots: set[str]) -> int:
    changed = 0
    seed_md, third = root / "SEED.md", root / "LICENSE-THIRD-PARTY.md"
    if seed_md.is_file():
        changed += rewrite_file(seed_md, lambda t: DOC_SEED_ROW.sub(lambda m: "`" + doc_module(m.group(1), roots) + "`", t))
    if third.is_file():
        changed += rewrite_file(third, lambda t: DOC_PATH.sub(lambda m: doc_path(m, roots), t))
    return changed


def doc_module(rest: str, roots: set[str]) -> str:
    """The `mapped to` cell: the module root a package was folded into (Mathlib's is the bare `Tengoku`)."""
    if not rest:
        return f"Tengoku.{SEED}"
    return rename_import("Tengoku" + rest, roots)


def doc_path(m: re.Match, roots: set[str]) -> str:
    if m.group("top") not in roots:
        return m.group(0)
    return f"`Tengoku/{SEED}/{m.group('top')}{m.group('rest') or ''}`"


def move_seed(tree: Path, entries: list[Path]) -> None:
    seed = tree / SEED
    seed.mkdir()
    for e in entries:
        e.rename(seed / e.name)


def library_files(tree: Path, namespaces: set[str]) -> list[Path]:
    files = [tree / "All.lean"] if (tree / "All.lean").is_file() else []
    for ns in sorted(namespaces):
        if (tree / f"{ns}.lean").is_file():
            files.append(tree / f"{ns}.lean")
        if (tree / ns).is_dir():
            files += sorted((tree / ns).rglob("*.lean"))
    return files


def apply(root: Path, libs: set[str]) -> Counter:
    """Move the seed and rewrite its dependents. A tree that already has Tengoku/Seed is left alone."""
    tree = root / "Tengoku"
    namespaces = {pascal(k) for k in libs}
    if namespaces & RESERVED:
        raise SystemExit(f"a library may not be named {sorted(namespaces & RESERVED)}: those are folders of the tree")
    done: Counter = Counter()
    if (tree / SEED).exists():
        return done
    entries = seed_entries(tree, namespaces)
    roots = {stem(e) for e in entries}
    move_seed(tree, entries)
    done["moved top-level entries"] = len(entries)
    for f in sorted((tree / SEED).rglob("*.lean")):
        depth = len(f.relative_to(tree / SEED).parts) - 1
        done["seeded modules rewritten"] += rewrite_file(f, lambda t: fix_include_str(rewrite_header(t, seeded_name(roots)), depth))
    for f in library_files(tree, namespaces):
        done["library modules rewritten"] += rewrite_file(f, lambda t: rewrite_header(t, library_name(roots)))
    if (root / "Tengoku.lean").is_file():
        done["root rewritten"] += rewrite_file(root / "Tengoku.lean", lambda t: rewrite_header(t, seeded_name(roots)))
    done["documents rewritten"] = rewrite_docs(root, roots)
    return done


def module_index(root: Path) -> dict[str, Path]:
    mods = {".".join(p.relative_to(root).with_suffix("").parts): p for p in (root / "Tengoku").rglob("*.lean")}
    if (root / "Tengoku.lean").is_file():
        mods["Tengoku"] = root / "Tengoku.lean"
    return mods


def include_errors(root: Path, path: Path, text: str) -> list[str]:
    errors = []
    for ln in text.split("\n"):
        if ln.lstrip().startswith("--"):
            continue
        for m in INCLUDE_STR.finditer(ln):
            target = path.parent.joinpath(*[c for lit in re.findall(r'"([^"\n]*)"', m.group("path")) for c in lit.split("/")])
            if not target.resolve().is_file():
                errors.append(f"{path.relative_to(root)}: include_str {m.group('path')} resolves to no file")
    return errors


def file_errors(root: Path, path: Path, mods: dict[str, Path]) -> list[str]:
    text = read(path)
    lines = text.split("\n")
    imports = header_imports(lines)
    errors = [
        f"{path.relative_to(root)}: import {m} resolves to no module"
        for m in imports
        if (m == "Tengoku" or m.startswith("Tengoku.")) and m not in mods
    ]
    return errors + include_errors(root, path, text)


def verify(root: Path) -> list[str]:
    """Every `import Tengoku…` names a module of the tree and every `include_str` path names a file."""
    mods = module_index(root)
    return [e for path in sorted(mods.values()) for e in file_errors(root, path, mods)]


def libs_for(args: argparse.Namespace, root: Path) -> set[str]:
    if args.libs_from:
        return libs_from_git(args.libs_from, root)
    return {x for x in args.libs.split(",") if x} if args.libs is not None else libs_from_tree(root)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("command", choices=["apply", "verify"])
    ap.add_argument("--root", default=".", help="the tengoku checkout (default: the current directory)")
    ap.add_argument("--libs-from", help="read the library names from this git ref (default: the working tree's data/)")
    ap.add_argument("--libs", help="comma-separated library names (overrides data/)")
    args = ap.parse_args(argv)
    root = Path(args.root).resolve()
    if args.command == "verify":
        errors = verify(root)
        print("\n".join(errors[:50]) or "restructure verify: every import and include_str resolves")
        return 1 if errors else 0
    done = apply(root, libs_for(args, root))
    print("\n".join(f"{k}: {v}" for k, v in sorted(done.items())) or "already restructured: nothing to do")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
