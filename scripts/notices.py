#!/usr/bin/env python3
"""Change notices on seeded files (Apache-2.0, section 4(b)).

The seeded packages are Apache-2.0 (lean4-cli is MIT), and section 4(b) asks that
a redistributed file that was changed "carry prominent notices stating that You
changed the files". The seed copies package sources into the tree and rewrites
their import paths (and, in one file, an instance name Lean derives from the
module root). So every seeded file that differs from its source says so in one
line: inside its licence header, or in a comment block of its own at the top
when it has none. A file the seed copied byte for byte gets nothing.

    python3 scripts/notices.py            # stamp every changed seeded file (idempotent)
    python3 scripts/notices.py --check    # list changed seeded files without a notice; exit 1 if any

scripts/seed.py stamps as it writes, so a re-seed keeps the notices. Both layouts of the tree are read: the seed under
Tengoku/Seed/ (what seed.py writes) and the earlier one, topic folders straight under Tengoku/.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

MARK = "Changed for Tengoku"
HEADER_WORDS = ("Copyright", "Released under", "Authors")
SUFFIX_RE = re.compile(r"\binst[A-Za-z0-9_]*?_tengoku\b")
LABELS = {
    "mathlib": "Mathlib",
    "batteries": "Batteries",
    "aesop": "Aesop",
    "Qq": "Qq",
    "proofwidgets": "ProofWidgets",
    "plausible": "Plausible",
    "LeanSearchClient": "LeanSearchClient",
    "importGraph": "import-graph",
    "Cli": "lean4-cli",
}
ROOT_CHANGE = "import paths rewritten, and imports of the other seeded packages added"


def describe(imports: bool, suffix: bool) -> str:
    """What the seed changed in a file, in words; '' when nothing."""
    parts = []
    if imports:
        parts.append("import paths rewritten")
    if suffix:
        parts.append("instance-name suffix `_mathlib` renamed `_tengoku`")
    return ", ".join(parts)


def notice(package: str, origin: str, rev: str, what: str) -> str:
    origin = re.sub(r"^https?://github\.com/|\.git$", "", origin.strip())
    line = f"{MARK}: copied from {LABELS.get(package, package)} ({origin} at {rev[:12]}); {what}."
    # the line goes inside a block comment: it must neither open nor close one
    assert "/-" not in line and "-/" not in line, line
    return line


def stamp(text: str, line: str) -> str:
    """`text` carrying the notice `line`: an existing notice is replaced, otherwise the line goes just
    before the end of the licence header, or into a comment block of its own at the very top."""
    lines = text.split("\n")
    for k, existing in enumerate(lines[:60]):
        if existing.startswith(MARK):
            lines[k] = line
            return "\n".join(lines)
    i = next((k for k, x in enumerate(lines) if x.strip()), None)
    if i is not None:
        first = lines[i].lstrip()
        if first.startswith("/-") and not first.startswith(("/-!", "/--")):
            close = next((k for k in range(i + 1, len(lines)) if "-/" in lines[k]), None)
            if close is not None and "-/" not in lines[i] and any(w in "\n".join(lines[i : close + 1]) for w in HEADER_WORDS):
                return "\n".join(lines[:close] + [line] + lines[close:])
    return f"/-\n{line}\n-/\n" + text


def has_notice(text: str) -> bool:
    return any(x.startswith(MARK) for x in text.split("\n")[:60])


def seed_rows(root: Path) -> dict[str, tuple[str, str]]:
    """package -> (origin, rev), from the table scripts/seed.py writes into SEED.md."""
    out = {}
    for row in (root / "SEED.md").read_text(encoding="utf-8").splitlines():
        cells = [c.strip() for c in row.strip().strip("|").split("|")]
        if len(cells) == 4 and cells[0] in LABELS:
            out[cells[0]] = (cells[1], cells[2])
    return out


def seeded_files(root: Path) -> list[Path]:
    """Tengoku.lean and every module that the seed wrote (under Tengoku/Seed/, or in the earlier layout under Tengoku/ with
    no KEEP subtree, no generated library module, not the generated aggregator)."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from seed import KEEP, seed_layout  # noqa: E402  (seed imports this module; import lazily)

    libs = {f.stem.split(".")[0] for tier in ("trusted", "staging", "tentative") for f in (root / "data" / tier).glob("*.jsonl")}
    generated = {"".join(w[:1].upper() + w[1:] for w in re.split(r"[-_ ]+", lib) if w) for lib in libs}
    tree = root / "Tengoku" / "Seed" if seed_layout(root) else root / "Tengoku"
    files = [root / "Tengoku.lean"] + sorted(tree.rglob("*.lean"))
    out = []
    for f in files:
        if not f.exists():
            continue
        rel = f.relative_to(root).parts
        top = rel[1].removesuffix(".lean") if len(rel) > 1 else None
        if top in KEEP or top in generated or rel == ("Tengoku", "All.lean") or f.name.startswith("_candidate_"):
            continue
        out.append(f)
    return out


def package_of(module: str) -> str:
    """The package a seeded module came from. The module name tells the layout: only the Seed layout has `Tengoku.Seed` modules."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from seed import PACKAGES, SEED, in_layout  # noqa: E402

    best = ("mathlib", "Tengoku")
    for pkg, (_, _, mapped) in PACKAGES.items():
        mapped = in_layout(mapped, module == SEED or module.startswith(SEED + "."))
        if (module == mapped or module.startswith(mapped + ".")) and len(mapped) > len(best[1]):
            best = (pkg, mapped)
    return best[0]


def change_in(root: Path, f: Path, text: str) -> str:
    """What the seed changed, read off the seeded file: its only edits are imports of a mapped root
    (every mapped root starts with `Tengoku`) and the `_tengoku` instance suffix. Upstream files
    mention neither."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from seed import IMPORT_RE  # noqa: E402

    if f == root / "Tengoku.lean":
        return ROOT_CHANGE
    imports = any(m.group(2) == "Tengoku" or m.group(2).startswith("Tengoku.") for m in IMPORT_RE.finditer(text))
    return describe(imports, bool(SUFFIX_RE.search(text)))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", default=str(Path(__file__).resolve().parents[1]), help="tengoku checkout")
    ap.add_argument("--check", action="store_true", help="report changed seeded files without a notice")
    args = ap.parse_args()
    root = Path(args.root).resolve()
    rows = seed_rows(root)
    stamped = missing = unchanged = 0
    for f in seeded_files(root):
        text = f.read_text(encoding="utf-8")
        what = change_in(root, f, text)
        if not what:
            unchanged += 1
            continue
        module = ".".join(f.relative_to(root).with_suffix("").parts)
        pkg = package_of(module)
        origin, rev = rows.get(pkg, ("?", "?"))
        new = stamp(text, notice(pkg, origin, rev, what))
        if new == text:
            continue
        if args.check:
            missing += 1
            print(f"no change notice: {f.relative_to(root)}")
            continue
        f.write_text(new, encoding="utf-8")
        stamped += 1
    if args.check:
        print(f"{missing} changed seeded files without a notice ({unchanged} seeded files are unchanged)")
        return 1 if missing else 0
    print(f"stamped {stamped} files ({unchanged} seeded files are unchanged and need none)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
