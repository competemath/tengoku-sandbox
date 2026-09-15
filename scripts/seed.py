#!/usr/bin/env python3
"""Seed the Tengoku tree from a built Lean environment.

Tengoku is one self-contained tree: a single library root `Tengoku/`, no Lake
dependencies. Seeding folds the SOURCE files of the packages that make up a
Lean environment (Mathlib and everything its build pulled in) into that tree
under topic-based paths, and rewrites every `import` accordingly. Declaration
names are untouched — `Nat.add_comm` stays `Nat.add_comm`; only module paths
change. Provenance is recorded in SEED.md.

    python3 scripts/seed.py --from ~/emissary-gate2/.lake/packages --out .

Re-runnable: wipes and regenerates the seeded part of the tree (never touches
Tengoku/EquationalTheories or other non-seed subtrees listed in KEEP).
"""

import argparse
import json
import re
import shutil
import sys
from pathlib import Path

# package name -> (source root dir inside the package, module root, mapped module root)
# Topic-based placement: Mathlib's own layout becomes the tree's layout directly;
# its dependency packages go under topics, never under an origin name.
# Seeded subtrees that are not library content: ProofWidgets' demos embed JS
# bundles that only its own npm build produces, so they can never build here.
SKIP_SUBTREES = {"proofwidgets": ("ProofWidgets/Demos",)}

PACKAGES = {
    "mathlib": ("Mathlib", "Mathlib", "Tengoku"),
    "batteries": ("Batteries", "Batteries", "Tengoku.Std"),
    "aesop": ("Aesop", "Aesop", "Tengoku.Tactic.Aesop"),
    "Qq": ("Qq", "Qq", "Tengoku.Meta.Qq"),
    "proofwidgets": ("ProofWidgets", "ProofWidgets", "Tengoku.Widgets"),
    # Mathlib's own Testing/Plausible/* extends this engine and shares leaf
    # names (Functions, Sampleable, Testable), so the engine lives one topic
    # over: Testing/Random.
    "plausible": ("Plausible", "Plausible", "Tengoku.Testing.Random"),
    "LeanSearchClient": ("LeanSearchClient", "LeanSearchClient", "Tengoku.Search.LeanSearchClient"),
    "importGraph": ("ImportGraph", "ImportGraph", "Tengoku.Meta.ImportGraph"),
    "Cli": ("Cli", "Cli", "Tengoku.Meta.Cli"),
}
# Non-.lean assets a package's sources read at compile time (include_str).
ASSETS = {
    "proofwidgets": [("widget/js", "Tengoku/widget/js")],
    # Mathlib's Tactic/Widget modules `include_str` files from `widget/src/…`
    # three levels above themselves — the PACKAGE root, which in the tree is
    # the repository root.
    "mathlib": [("widget", "widget")],
}
KEEP = {"EquationalTheories", "CompeteMath"}  # subtrees that are not seed

# Lean's module system: `import X`, `public import X`, `private import X`,
# `meta import X`, `public meta import X`, `import all X` — the module name
# is the first token after the keyword and its modifiers.
IMPORT_RE = re.compile(r"^(\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)([A-Za-z_][\w.«»]*)(.*)$", re.M)


def module_map(root_mod: str, mapped_root: str, mod: str) -> str | None:
    if mod == root_mod:
        return mapped_root
    if mod.startswith(root_mod + "."):
        return mapped_root + mod[len(root_mod) :]
    return None


def rewrite_imports(text: str, roots: list[tuple[str, str]]) -> str:
    def sub(m):
        mod = m.group(2)
        for root_mod, mapped in roots:
            new = module_map(root_mod, mapped, mod)
            if new:
                return f"{m.group(1)}{new}{m.group(3)}"
        return m.group(0)  # core (Init/Std/Lean) and anything unknown: untouched

    return IMPORT_RE.sub(sub, text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--from", dest="src", required=True, help=".lake/packages dir of a built environment")
    ap.add_argument("--out", dest="out", default=".", help="tengoku repo root")
    ap.add_argument("--manifest", default=None, help="manifest.json of that environment (for revs)")
    args = ap.parse_args()
    src = Path(args.src).expanduser().resolve()
    out = Path(args.out).resolve()
    tree = out / "Tengoku"

    manifest = {}
    # Lake keeps the manifest at the PROJECT root (<project>/lake-manifest.json),
    # two levels above <project>/.lake/packages.
    mpath = Path(args.manifest) if args.manifest else src.parent.parent / "lake-manifest.json"
    if mpath.exists():
        for p in json.load(open(mpath)).get("packages", []):
            manifest[p["name"]] = p

    roots = [(v[1], v[2]) for v in PACKAGES.values()]
    planned: dict[Path, tuple[str, Path]] = {}  # target file -> (package, source file)
    for pkg, (srcdir, root_mod, mapped) in PACKAGES.items():
        base = src / pkg / srcdir
        if not base.is_dir():
            sys.exit(f"missing package source dir: {base}")
        mapped_dir = tree.parent / Path(*mapped.split("."))  # Tengoku/... dir for the mapped root
        for f in base.rglob("*.lean"):
            rel = f.relative_to(base)
            if any(str(f.relative_to(src / pkg)).startswith(s + "/") for s in SKIP_SUBTREES.get(pkg, ())):
                continue
            target = mapped_dir / rel
            if target in planned:
                sys.exit(f"path collision: {target} from {pkg} and {planned[target][0]}")
            planned[target] = (pkg, f)
        # the package's root aggregator file (Mathlib.lean, Batteries.lean, ...)
        root_file = src / pkg / f"{srcdir}.lean"
        if root_file.exists():
            target = tree.parent / (Path(*mapped.split(".")).with_suffix(".lean"))
            if target in planned:
                sys.exit(f"path collision on root aggregator: {target}")
            planned[target] = (pkg, root_file)

    # Wipe the previous seed (everything under Tengoku/ except KEEP), then write.
    if tree.exists():
        for child in tree.iterdir():
            if child.name in KEEP:
                continue
            shutil.rmtree(child) if child.is_dir() else child.unlink()
    for name in ("Tengoku.lean",):
        p = out / name
        if p.exists():
            p.unlink()

    n = 0
    # Lean disambiguates a colliding auto-generated instance name by appending
    # `_<module root>` (`instToJsonPUnit_mathlib`); under the new root that
    # suffix is `_tengoku`, and the one explicit reference to it must follow.
    inst_suffix = re.compile(r"\b(inst[A-Za-z0-9_]*?)_mathlib\b")
    for target, (pkg, f) in sorted(planned.items()):
        target.parent.mkdir(parents=True, exist_ok=True)
        text = f.read_text(encoding="utf-8")
        text = inst_suffix.sub(r"\1_tengoku", rewrite_imports(text, roots))
        target.write_text(text, encoding="utf-8")
        n += 1
    for pkg, assets in ASSETS.items():
        for rel_src, rel_dst in assets:
            s, d = src / pkg / rel_src, out / rel_dst
            if s.is_dir():
                if d.exists():
                    shutil.rmtree(d)
                shutil.copytree(s, d)

    # Root aggregator: Mathlib's root (already mapped to Tengoku.lean by the loop
    # above) plus the other packages' roots and the non-seed subtrees.
    root = out / "Tengoku.lean"
    lines = root.read_text(encoding="utf-8").rstrip("\n").split("\n") if root.exists() else []
    # The aggregator is a `module` file (Mathlib's root is), so re-exports must be `public import`.
    extra = [
        f"public import {v[2]}"
        for k, v in PACKAGES.items()
        if k != "mathlib" and (out / (Path(*v[2].split(".")).with_suffix(".lean"))).exists()
    ]
    extra += [f"public import Tengoku.{k}" for k in sorted(KEEP) if (tree / f"{k}.lean").exists()]
    header = [
        "-- Tengoku: one self-contained tree. This file imports all of it.",
        "-- Seeded from the packages listed in SEED.md; grown by verified translations.",
    ]
    # Mathlib's root ends with a `set_option` after its imports; an import
    # after that is a parse error, so the extra roots go after the LAST import.
    last_import = max((i for i, l in enumerate(lines) if IMPORT_RE.match(l)), default=len(lines) - 1)
    lines = lines[: last_import + 1] + extra + lines[last_import + 1 :]
    root.write_text("\n".join(header + lines) + "\n", encoding="utf-8")

    # Lake project: a single root, no dependencies. Options: the toolchain
    # defaults plus the two Mathlib settings that change what ELABORATES
    # (`maxSynthPendingDepth = 3` — without it a dozen Mathlib modules fail
    # instance synthesis) or how things print. NOT Mathlib's `autoImplicit =
    # false`: the seeded sources come from packages written against different
    # settings — Mathlib forbids autoImplicit, Batteries relies on it — and the
    # permissive default is the one every one of them elaborates under.
    # Stricter-than-author settings only break files.
    (out / "lakefile.toml").write_text(
        """name = "tengoku"
defaultTargets = ["Tengoku"]

[leanOptions]
pp.unicode.fun = true
maxSynthPendingDepth = 3

[[lean_lib]]
name = "Tengoku"
# Every module under Tengoku/ is built — not just what the root file imports.
# The seeded root is a module-system file and cannot import the generated
# (legacy) translation modules; they are reached as `import Tengoku.<Library>`.
globs = ["Tengoku", "Tengoku.+"]
""",
        encoding="utf-8",
    )
    toolchain = src.parent.parent / "lean-toolchain"
    if toolchain.exists():
        (out / "lean-toolchain").write_text(toolchain.read_text(encoding="utf-8"), encoding="utf-8")

    rows = ["| package | origin | rev | mapped to |", "|---|---|---|---|"]
    for pkg, (srcdir, root_mod, mapped) in PACKAGES.items():
        m = manifest.get(pkg, {})
        rows.append(f"| {pkg} | {m.get('url', '?')} | {m.get('rev', '?')} | `{mapped}` |")
    (out / "SEED.md").write_text(
        "# Seed\n\nTengoku depends on nothing. It was SEEDED once from the following sources — their files were folded into the tree "
        "under topic paths, imports rewritten, declaration names untouched. After seeding, these origins have no relationship to Tengoku.\n\n"
        f"Toolchain: `{(out / 'lean-toolchain').read_text().strip() if (out / 'lean-toolchain').exists() else '?'}`\n\n"
        + "\n".join(rows)
        + "\n",
        encoding="utf-8",
    )
    print(f"seeded {n} files into {tree}; root aggregator {root}; lakefile + SEED.md written")


if __name__ == "__main__":
    main()
