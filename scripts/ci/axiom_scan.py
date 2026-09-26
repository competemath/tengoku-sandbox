#!/usr/bin/env python3
"""axiom_scan.py <export.ndjson> [--records DIR] [--permitted OUT] — the axioms every declaration of a
lean4export file rests on, computed from the exported terms alone.

A second opinion next to the queue's `collectAxioms` check: no Lean code runs here. lean4export writes all
of a declaration's dependencies before any of its own terms (`dumpDeps` runs first), so one pass in file
order knows a constant's axioms before any term that mentions it. The only earlier mentions are an
inductive block's mentions of itself; those terms are re-read once the block's axioms are known.

Fails when
  - the export declares an axiom outside Lean's prelude (propext, Classical.choice, Quot.sound, sorryAx,
    Lean.ofReduceBool, Lean.ofReduceNat, Lean.trustCompiler),
  - any declaration rests on sorryAx,
  - a trusted record (data/trusted, tombstones applied) rests on anything but propext, Classical.choice
    and Quot.sound, or is not in the export at all,
  - the file breaks the order above (a constant mentioned and never declared).
--permitted writes the declared axioms as a JSON list, for nanoda's `permitted_axioms`.
"""

from __future__ import annotations

import argparse
import json
import sys
from array import array
from pathlib import Path

try:
    import orjson

    loads = orjson.loads
except ImportError:  # 3-4x slower, same result
    loads = json.loads

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PRELUDE = STANDARD | {"sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
DECLS = ("axiom", "def", "thm", "opaque", "quot", "inductive")


class Sets:
    """Sets of axioms, interned: every term carries a small id, unions are cached."""

    def __init__(self) -> None:
        self.sets: list[frozenset[int]] = [frozenset()]
        self.ids: dict[frozenset[int], int] = {frozenset(): 0}
        self.cache: dict[tuple[int, int], int] = {}

    def of(self, s: frozenset[int]) -> int:
        i = self.ids.get(s)
        if i is None:
            i = self.ids[s] = len(self.sets)
            self.sets.append(s)
        return i

    def union(self, a: int, b: int) -> int:
        if a == b or b == 0:
            return a
        if a == 0:
            return b
        k = (a, b) if a < b else (b, a)
        r = self.cache.get(k)
        if r is None:
            r = self.cache[k] = self.of(self.sets[a] | self.sets[b])
        return r


class Scan:
    def __init__(self) -> None:
        self.S = Sets()
        self.E = array("I")  # term index -> axiom-set id
        self.name_pre = array("I", [0])
        self.name_part: list[str] = [""]
        self.decl: dict[int, int] = {}  # declared name index -> axiom-set id
        self.axioms: list[int] = []  # axiom name indices, in file order (bit = position)
        self.early: set[int] = set()  # names mentioned before their declaration line
        self.buffer: list[tuple[int, dict]] = []  # terms since the first early mention, for the re-read
        self.lines = 0

    def name(self, i: int) -> str:
        parts = []
        while i:
            parts.append(self.name_part[i])
            i = self.name_pre[i]
        return ".".join(reversed(parts))

    def term(self, o: dict) -> int:
        U, E = self.S.union, self.E
        if "app" in o:
            v = o["app"]
            return U(E[v["fn"]], E[v["arg"]])
        if "const" in o:
            n = o["const"]["name"]
            m = self.decl.get(n)
            if m is None:
                self.early.add(n)
                return 0
            return m
        for k in ("forallE", "lam"):
            if k in o:
                v = o[k]
                return U(E[v["type"]], E[v["body"]])
        if "letE" in o:
            v = o["letE"]
            return U(U(E[v["type"]], E[v["value"]]), E[v["body"]])
        if "mdata" in o:
            return E[o["mdata"]["expr"]]
        if "proj" in o:
            v = o["proj"]
            return U(E[v["struct"]], self.decl.get(v["typeName"], 0))
        return 0  # bvar, sort, natVal, strVal

    def declaration(self, o: dict) -> None:
        U, E = self.S.union, self.E
        if "inductive" in o:
            v = o["inductive"]
            members = v["types"] + v["ctors"] + v["recs"]
            names = [x["name"] for x in members]
            m = 0
            for x in members:
                m = U(m, E[x["type"]])
            for r in v["recs"]:
                for rule in r["rules"]:
                    m = U(m, E[rule["rhs"]])
        else:
            kind = next(k for k in DECLS if k in o)
            v = o[kind]
            names = [v["name"]]
            m = E[v["type"]]
            if "value" in v:
                m = U(m, E[v["value"]])
            if kind == "axiom":
                self.axioms.append(v["name"])
                m = U(m, self.S.of(frozenset([len(self.axioms) - 1])))
        for n in names:
            self.decl[n] = m
        mine = self.early.intersection(names)
        if mine:
            self.early -= mine
            if m:  # the early mentions were read as resting on nothing: re-read them and every term above them
                for i, t in self.buffer:
                    E[i] = self.term(t)
        if not self.early:
            self.buffer.clear()

    def run(self, path: Path) -> None:
        with open(path, "rb") as f:
            for line in f:
                self.lines += 1
                o = loads(line)
                i = o.get("ie")
                if i is not None:
                    if i != len(self.E):
                        raise SystemExit(f"axiom-scan: term {i} out of order at line {self.lines}")
                    self.E.append(self.term(o))
                    if self.early:
                        self.buffer.append((i, o))
                elif "in" in o:
                    if o["in"] != len(self.name_part):
                        raise SystemExit(f"axiom-scan: name {o['in']} out of order at line {self.lines}")
                    v = o.get("str") or o["num"]
                    self.name_pre.append(v["pre"])
                    self.name_part.append(v["str"] if "str" in v else str(v["i"]))
                elif "il" in o:
                    pass
                elif "meta" in o:
                    fmt = o["meta"]["format"]["version"]
                    if not fmt.startswith("3."):
                        raise SystemExit(f"axiom-scan: export format {fmt}, this reads 3.x")
                elif any(k in o for k in DECLS):
                    self.declaration(o)
                else:
                    raise SystemExit(f"axiom-scan: unknown line {self.lines}: {line[:120]!r}")

    def rests_on(self, n: int) -> list[str]:
        return sorted(self.name(self.axioms[b]) for b in self.S.sets[self.decl[n]])


def trusted_records(d: Path) -> list[str]:
    names: dict[str, None] = {}
    gone: set[str] = set()
    for f in sorted(d.rglob("*.jsonl")):
        for line in f.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                if "tombstone" in r:
                    gone.add(r["tombstone"])
                elif "name" in r:
                    names[r["name"]] = None
    return [n for n in names if n not in gone]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("export", type=Path)
    ap.add_argument("--records", type=Path, help="data/trusted: every record must rest only on the standard axioms")
    ap.add_argument("--permitted", type=Path, help="write the declared axioms here (a JSON list)")
    a = ap.parse_args()

    s = Scan()
    s.run(a.export)
    bad: list[str] = []
    if s.early:
        bad.append(f"mentioned and never declared: {sorted(s.name(n) for n in s.early)[:10]}")
    declared = [s.name(n) for n in s.axioms]
    print(f"axiom-scan: {s.lines} lines, {len(s.E)} terms, {len(s.decl)} constants, axioms declared: {declared}")
    for x in declared:
        if x not in PRELUDE:
            bad.append(f"the export declares the axiom {x}")

    by_name = {s.name(n): n for n in s.decl}
    resting: dict[str, list[str]] = {x: [] for x in declared if x not in STANDARD}
    own = set(s.axioms)
    for sid, ax in enumerate(s.S.sets):
        hit = [x for x in (s.name(s.axioms[b]) for b in ax) if x in resting]
        if hit:
            users = [s.name(n) for n, m in s.decl.items() if m == sid and n not in own]  # not the axioms themselves
            for x in hit:
                resting[x] += users
    for x, users in resting.items():
        shown = sorted(users, key=lambda u: (u.count("._") > 0, u))[:25]  # user-facing names first
        print(f"  {x}: {len(users)} constants rest on it{': ' + ', '.join(shown) if shown else ''}{' …' if len(users) > 25 else ''}")
    if resting.get("sorryAx"):
        bad.append(f"{len(resting['sorryAx'])} constants rest on sorryAx")

    if a.records:
        records = trusted_records(a.records)
        by_last: dict[str, list[str]] = {}
        for k in by_name:
            by_last.setdefault(k.rsplit(".", 1)[-1], []).append(k)
        missing, extra = [], []
        for r in records:
            n = by_name.get(r)
            if n is None:  # declared inside a namespace: the record's name is the end of the constant's
                hits = [k for k in by_last.get(r.rsplit(".", 1)[-1], []) if k.endswith("." + r)]
                n = by_name[hits[0]] if len(hits) == 1 else None
            if n is None:
                missing.append(r)
                continue
            beyond = [x for x in s.rests_on(n) if x not in STANDARD]
            if beyond:
                extra.append(f"{r} rests on {beyond}")
        print(f"axiom-scan: {len(records)} trusted records, {len(records) - len(missing) - len(extra)} rest only on the standard axioms")
        if missing:
            bad.append(f"{len(missing)} trusted records are not in the export: {missing[:10]}")
        bad += extra[:50]

    if a.permitted:
        a.permitted.write_text(json.dumps(declared))
    for b in bad:
        print(f"::error::axiom-scan: {b}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
