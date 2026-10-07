#!/usr/bin/env python3
"""isnad_sweep.py — which modules the next tag PR takes (docs/pr-classes.md, section 7; docs/isnad.md, "The sweep").

  isnad_sweep.py plan [--scope seed|native|libs|all] [--prefix MODULE.PREFIX] [--max N] [--root DIR] [--list]

Prints the modules of the next part of the sweep, one per line, or with `--list` counts per scope and the first modules of every part. A module is *to do* when it is in
scope (the rule of `scripts/ci/tag_check.py`: below Tengoku/Seed/, Tengoku/Native/ or a library that arrived as an intake bundle), holds a `theorem` or `lemma` in code
(never in a comment, docstring or string) and carries no tag yet. The order is dependents first (a module before anything it imports): a tag changes a docstring, so
the olean of the module and of everything importing it, and a module tagged after its importers does not rebuild them a second time. Ties are broken by name, so the
same tree always gives the same parts. At most 400 modules a part, what a tag PR may hold.
"""

from __future__ import annotations

import argparse
import heapq
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import isnad_tag as tg  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
MAX_PART = 400
SCOPES = ("seed", "native", "libs", "all")
IMPORT = re.compile(r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(Tengoku[\w.«»']*)", re.M)
DECL_MODIFIERS = {"private", "protected", "noncomputable", "nonrec", "public", "meta", "unsafe", "partial"}


def pascal(s: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[-_ ]+", s) if w)


def intake_namespaces(root: Path) -> set[str]:
    """the libraries that arrived as intake bundles (data/intake/<library>/manifest.jsonl), as module namespaces"""
    return {pascal(p.parent.name) for p in (root / "data" / "intake").glob("*/manifest.jsonl")}


def scope_of(rel: str, intake: set[str]) -> str | None:
    """seed / native / libs for a module a tag PR may touch (the rule of tag_check.in_scope), else None"""
    m = re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", rel)
    if not m:
        return None
    if m.group(1) == "Seed":
        return "seed"
    if m.group(1) == "Native":
        return "native"
    return "libs" if m.group(1) in intake else None


def module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def code_of(text: str) -> str:
    """the text with comments, docstrings and strings blanked: what is code"""
    return "".join(text[a:b] if kind == "code" else re.sub(r"[^\n]", " ", text[a:b]) for kind, a, b in tg.scan(text))


def starts_theorem(line: str) -> bool:
    """the line is a `theorem` or `lemma` command: attributes (`@[…]`) and modifiers first, then the keyword and a name (no regular expression: the nested repeat of
    attributes backtracks exponentially on a crafted line, which CodeQL found)"""
    rest = line.lstrip()
    while rest.startswith("@["):
        end = rest.find("]")
        if end < 0:
            return False
        rest = rest[end + 1 :].lstrip()
    words = rest.split()
    while words and words[0] in DECL_MODIFIERS:
        words = words[1:]
    return len(words) >= 2 and words[0] in ("theorem", "lemma")


def has_theorem(text: str) -> bool:
    return any(starts_theorem(ln) for ln in code_of(text).split("\n"))


def is_tagged(text: str) -> bool:
    return any(tg.TAG_LINE.match(ln) for kind, a, b in tg.scan(text) if kind == "doc" for ln in text[a + 3 : b - 2].split("\n"))


def dependents_first(imports: dict[str, set[str]]) -> list[str]:
    """modules in an order where none comes after a module it imports (Kahn's algorithm from the modules nothing imports); ties by name. A cycle (Lean has none) is
    appended by name rather than lost."""
    importers: dict[str, int] = {m: 0 for m in imports}
    for m, deps in imports.items():
        for d in deps:
            if d in importers and d != m:
                importers[d] += 1
    ready = [m for m, n in importers.items() if n == 0]
    heapq.heapify(ready)
    out: list[str] = []
    done: set[str] = set()
    while ready:
        m = heapq.heappop(ready)
        out.append(m)
        done.add(m)
        for d in imports[m]:
            if d in importers and d != m and d not in done:
                importers[d] -= 1
                if importers[d] == 0:
                    heapq.heappush(ready, d)
    return out + sorted(set(imports) - done)


def todo(root: Path, scope: str = "all") -> list[str]:
    """the modules still to tag in this tree, dependents first"""
    intake = intake_namespaces(root)
    files: dict[str, str] = {}
    for p in sorted((root / "Tengoku").rglob("*.lean")):
        rel = p.relative_to(root).as_posix()
        sc = scope_of(rel, intake)
        if sc and (scope == "all" or scope == sc):
            files[module_name(rel)] = p.read_bytes().decode("utf-8", errors="replace")
    imports = {m: set(IMPORT.findall(t)) for m, t in files.items()}
    order = dependents_first(imports)
    return [m for m in order if has_theorem(files[m]) and not is_tagged(files[m])]


def plan(root: Path, scope: str, prefix: str, limit: int) -> list[str]:
    return [m for m in todo(root, scope) if m.startswith(prefix)][: min(limit, MAX_PART)]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--scope", choices=SCOPES, default="all")
    p.add_argument("--prefix", default="", help="only modules whose name starts with this")
    p.add_argument("--max", type=int, default=MAX_PART)
    p.add_argument("--root", default=str(ROOT))
    p.add_argument("--list", action="store_true", help="counts and the parts, not the next part's modules")
    a = ap.parse_args(argv)
    root = Path(a.root)
    if a.list:
        every = todo(root, a.scope)
        mine = [m for m in every if m.startswith(a.prefix)]
        parts = [mine[i : i + MAX_PART] for i in range(0, len(mine), MAX_PART)]
        print(json.dumps({"to_tag": len(mine), "parts": len(parts), "first_of_each_part": [pt[0] for pt in parts]}, indent=1))
        return 0
    mods = plan(root, a.scope, a.prefix, a.max)
    print("\n".join(mods))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
