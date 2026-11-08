#!/usr/bin/env python3
"""tawatur.py — the independence test of the tawatur PROPOSAL (docs/tawatur.md). Nothing in the tree or the gates uses it; tawatur is not a status the tree has.

  tawatur.py report [--k 3] [--floor 5] [--ignore NAME ...] [--ignore-prefix P ...] [--all] < CLOSURES.jsonl

The closures come on standard input (no file name is taken from the command line), one proof per line: {"id": isnad id of the statement, "name": the theorem, "lib": where it comes from, "closure": [every constant the proof term
reaches, transitively], "statement_closure": [the constants of the statement, optional], "modules": {constant: the module that defines it, optional}}. The statements with at least two proofs are grouped by id; in each group a proof
counts only if it has a SUBSTANCE of at least `floor` constants outside the ignored set X, two proofs are INDEPENDENT when they come from different libraries and their
constants outside X are disjoint, and a statement is TAWATUR when at least `k` of its proofs are pairwise independent (the largest such set: Bron-Kerbosch on the
independence graph; a group is small). X is the forced layer (Lean's core, the three axioms, the statement's own constants) plus what `--ignore`/`--ignore-prefix` add: the
pinned foundation list is the open design question, not code.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from itertools import combinations

# the forced layer: what every proof shares by construction (the kernel's axioms and Lean's own library). Namespaces end in a dot, so that `Equiv.foo` or `Orderiso` of Mathlib
# are not taken for `Eq` and `Or`; the logical constants are exact names (and their namespaces: `Eq.mpr`, `And.intro`)
FORCED_PREFIXES = (
    "Lean.",
    "Init.",
    "Std.",
    "Classical.",
    "Quot.",
    "Eq.",
    "HEq.",
    "True.",
    "False.",
    "And.",
    "Or.",
    "Iff.",
    "Not.",
    "Exists.",
)
FORCED_EXACT = frozenset({"propext", "Quot", "Eq", "HEq", "True", "False", "And", "Or", "Iff", "Not", "Exists"})


FORCED_MODULES = (
    "Init",
    "Std",
    "Lean",
)  # a constant DEFINED in one of these modules (or below) is Lean's core, whatever its name: `Nat.succ` is in Init.Prelude


def forced_module(module: str | None) -> bool:
    return bool(module) and any(module == root or module.startswith(root + ".") for root in FORCED_MODULES)


def ignored(name: str, prefixes: tuple[str, ...], exact: set[str], module: str | None = None) -> bool:
    """the constant is in X: a logical constant, Lean's core by where it is defined (`module`, when the input says) or by its name's namespace, or in what the caller ignores"""
    return name in FORCED_EXACT or name in exact or name.startswith(prefixes) or forced_module(module)


def read_proofs(stream) -> list[dict]:
    return [json.loads(ln) for ln in stream.read().splitlines() if ln.strip()]


def substance(proof: dict, group_statement: set[str], prefixes: tuple[str, ...], exact: set[str]) -> set[str]:
    """the constants of the proof outside X (the forced layer, the statement's own constants for the whole group, what the caller ignores)"""
    own = set(proof["closure"]) - group_statement
    modules = proof.get("modules", {})
    return {c for c in own if not ignored(c, prefixes, exact, modules.get(c))}


def independent(a: dict, b: dict) -> bool:
    """two proofs of one statement are independent: different libraries, no constant in common outside X"""
    return a["lib"] != b["lib"] and not (a["substance"] & b["substance"])


def largest_independent_set(proofs: list[dict]) -> list[dict]:
    """a largest set of pairwise independent proofs (Bron-Kerbosch on the independence graph; groups are small)"""
    n = len(proofs)
    adj = {i: {j for j in range(n) if j != i and independent(proofs[i], proofs[j])} for i in range(n)}
    best: list[int] = []

    def grow(r: list[int], p: set[int], x: set[int]) -> None:
        nonlocal best
        if not p and not x:
            if len(r) > len(best):
                best = r
            return
        for v in sorted(p):
            grow([*r, v], p & adj[v], x & adj[v])
            p = p - {v}
            x = x | {v}

    grow([], set(range(n)), set())
    return [proofs[i] for i in sorted(best)]


def analyse(
    proofs: list[dict],
    k: int = 3,
    floor: int = 5,
    prefixes: tuple[str, ...] = FORCED_PREFIXES,
    exact: set[str] | None = None,
) -> list[dict]:
    """one report row per statement with at least two proofs: its proofs, which count, the largest independent set, and whether the statement is tawatur"""
    exact = exact or set()
    groups: dict[str, list[dict]] = defaultdict(list)
    for p in proofs:
        groups[p["id"]].append(p)
    rows = []
    for ident, members in sorted(groups.items()):
        if len(members) < 2:
            continue
        stmt = {c for m in members for c in m.get("statement_closure", [])}
        counted = []
        for m in members:
            sub = substance(m, stmt, prefixes, exact)
            counted.append({**m, "substance": sub})
        solid = [m for m in counted if len(m["substance"]) >= floor]
        best = largest_independent_set(solid) if solid else []
        rows.append(
            {
                "id": ident,
                "proofs": [m["name"] for m in members],
                "libs": sorted({m["lib"] for m in members}),
                "substantial": [m["name"] for m in solid],
                "shared": {f"{a['name']} | {b['name']}": len(a["substance"] & b["substance"]) for a, b in combinations(solid, 2)},
                "independent": [m["name"] for m in best],
                "tawatur": len(best) >= k,
            }
        )
    return rows


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("report")
    r.add_argument("--k", type=int, default=3, help="independent proofs a statement needs (the proposal says 3 or 4)")
    r.add_argument("--floor", type=int, default=5, help="constants outside X a proof needs to count")
    r.add_argument("--ignore", action="append", default=[], help="a constant name to add to X")
    r.add_argument("--ignore-prefix", action="append", default=[], help="a name prefix to add to X")
    r.add_argument("--all", action="store_true", help="every statement with two or more proofs, not only the tawatur ones")
    a = ap.parse_args(argv)
    rows = analyse(read_proofs(sys.stdin), a.k, a.floor, (*FORCED_PREFIXES, *a.ignore_prefix), set(a.ignore))
    shown = rows if a.all else [row for row in rows if row["tawatur"]]
    for row in shown:
        print(json.dumps(row, ensure_ascii=False))
    print(
        f"{len(rows)} statements with two or more proofs; {sum(row['tawatur'] for row in rows)} tawatur (k={a.k}, floor={a.floor})",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
