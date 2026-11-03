#!/usr/bin/env python3
"""ic_plan.py — split the independent check into shards, and check that the shards cover everything.

  ic_plan.py plan  graph.tsv --roots-of PREFIX --cap-bytes N [--out plan.json]
  ic_plan.py cover graph.tsv shard-graph-*.tsv          (the shards' own graphs, recomputed by each shard job)

graph.tsv is ic_graph.lean's output for `Tengoku.All`: every module the tree imports. A shard is a list of ROOT modules; the shard's job
exports the closure of its roots (everything they import, Lean core included, every time: nothing is cached or assumed), and nanoda checks it.
A shard is as simple as that, so the coverage rule is as simple as it can be: the union of the shards' closures is every module of the tree.

The plan: the roots are the modules directly under the tree's umbrella that `Tengoku.All` imports (one per library) plus any module no library reaches;
roots are packed, in name order, into shards whose closures (the .olean bytes of the union) stay under the cap. Deterministic: the same graph gives the same plan.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path


def read_graph(path: Path) -> tuple[dict[str, list[str]], dict[str, str]]:
    imports: dict[str, list[str]] = {}
    olean: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) != 3:
            raise SystemExit(f"{path}: not a graph line: {line[:80]!r}")
        module, file, imps = parts
        if module in imports:
            raise SystemExit(f"{path}: module {module} listed twice")
        imports[module] = imps.split()
        olean[module] = file
    return imports, olean


def closure(imports: dict[str, list[str]], roots: list[str]) -> set[str]:
    """Every module reachable from `roots`, the roots included. A module the graph does not list is an error (a broken graph must fail, not shrink)."""
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        if m not in imports:
            raise SystemExit(f"the graph does not list module {m}")
        seen.add(m)
        stack.extend(imports[m])
    return seen


def size_of(olean: dict[str, str], modules: set[str], sizes: dict[str, int]) -> int:
    total = 0
    for m in modules:
        if m not in sizes:
            sizes[m] = os.path.getsize(olean[m])
        total += sizes[m]
    return total


def plan(imports: dict[str, list[str]], olean: dict[str, str], top: str, cap_bytes: int, sizes: dict[str, int] | None = None) -> dict:
    """Shards of roots. `top` is the umbrella module the tree is checked from (Tengoku.All): its direct imports are the roots, in name order."""
    if top not in imports:
        raise SystemExit(f"the graph does not list {top}")
    sizes = sizes if sizes is not None else {}
    roots = sorted(imports[top])
    everything = closure(imports, [top])
    reached: set[str] = set()
    for r in roots:
        reached |= closure(imports, [r])
    # modules no root reaches (only `top` itself, or a module top imports that is not a root): they are roots of their own
    orphans = sorted(everything - reached - {top})
    roots = roots + orphans
    shards: list[dict] = []
    current: list[str] = []
    current_mods: set[str] = set()
    for r in roots:
        with_r = current_mods | closure(imports, [r])
        if current and size_of(olean, with_r, sizes) > cap_bytes:
            shards.append({"roots": current, "bytes": size_of(olean, current_mods, sizes)})
            current, current_mods = [], set()
            with_r = closure(imports, [r])
        current.append(r)
        current_mods = with_r
    if current:
        shards.append({"roots": current, "bytes": size_of(olean, current_mods, sizes)})
    for i, s in enumerate(shards):
        s["id"] = i
    return {"top": top, "cap_bytes": cap_bytes, "modules": len(everything), "shards": shards}


def cover(whole: dict[str, list[str]], shard_graphs: list[dict[str, list[str]]], top: str) -> list[str]:
    """The problems with the shards, as a list of messages: empty when the union of the shards' modules is every module of the tree except `top` itself
    (`top` declares nothing: it is the umbrella). The shards' graphs are the ones each shard job computed from its own roots."""
    problems: list[str] = []
    union: set[str] = set()
    for g in shard_graphs:
        union |= set(g)
    want = set(whole) - {top}
    missing = sorted(want - union)
    extra = sorted(union - set(whole))
    if missing:
        problems.append(f"{len(missing)} modules are in no shard, e.g. {missing[:3]}")
    if extra:
        problems.append(f"{len(extra)} modules are in a shard and not in the tree, e.g. {extra[:3]}")
    return problems


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("graph", type=Path)
    p.add_argument("--top", default="Tengoku.All")
    p.add_argument("--cap-bytes", type=int, required=True)
    p.add_argument("--out", type=Path)
    c = sub.add_parser("cover")
    c.add_argument("graph", type=Path)
    c.add_argument("shard_graphs", type=Path, nargs="+")
    c.add_argument("--top", default="Tengoku.All")
    a = ap.parse_args(argv[1:])
    imports, olean = read_graph(a.graph)
    if a.cmd == "plan":
        out = plan(imports, olean, a.top, a.cap_bytes)
        text = json.dumps(out, indent=1)
        if a.out:
            a.out.write_text(text + "\n", encoding="utf-8")
        print(f"{out['modules']} modules, {len(out['shards'])} shards, bytes per shard: {[s['bytes'] for s in out['shards']]}")
        return 0
    problems = cover(imports, [read_graph(g)[0] for g in a.shard_graphs], a.top)
    for m in problems:
        print("COVERAGE:", m)
    print("coverage ok" if not problems else "coverage FAILED")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
