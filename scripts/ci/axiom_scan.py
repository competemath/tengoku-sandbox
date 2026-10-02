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
    and Quot.sound, or belongs to a library the tree compiles (Tengoku/<Library>.lean exists) and is not in
    the export. Records of libraries without modules (the Mathlib index files, a library not yet compiled)
    are counted, by library, when the export does not hold them,
  - the file breaks the order above (a constant mentioned and never declared).
--permitted writes the declared axioms as a JSON list, for nanoda's `permitted_axioms`; --report writes the whole
verdict as JSON (the axiom report a release carries).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
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
# term kinds that join the axioms of two sub-terms: kind -> the keys of the two
_BINARY = {"app": ("fn", "arg"), "forallE": ("type", "body"), "lam": ("type", "body")}


class AxiomSets:
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
        self.S = AxiomSets()
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
        for kind, (first, second) in _BINARY.items():
            if kind in o:
                v = o[kind]
                return U(E[v[first]], E[v[second]])
        if "const" in o:
            return self.constant(o["const"]["name"])
        if "letE" in o:
            v = o["letE"]
            return U(U(E[v["type"]], E[v["value"]]), E[v["body"]])
        if "mdata" in o:
            return E[o["mdata"]["expr"]]
        if "proj" in o:
            v = o["proj"]
            return U(E[v["struct"]], self.decl.get(v["typeName"], 0))
        return 0  # bvar, sort, natVal, strVal

    def constant(self, n: int) -> int:
        """The axiom set of a constant; one mentioned before its declaration reads as resting on nothing for now."""
        m = self.decl.get(n)
        if m is None:
            self.early.add(n)
            return 0
        return m

    def inductive_block(self, v: dict) -> tuple[list[int], int]:
        """The names of an inductive block's types, constructors and recursors, and the axioms the block rests on."""
        U, E = self.S.union, self.E
        members = v["types"] + v["ctors"] + v["recs"]
        m = 0
        for x in members:
            m = U(m, E[x["type"]])
        for r in v["recs"]:
            for rule in r["rules"]:
                m = U(m, E[rule["rhs"]])
        return [x["name"] for x in members], m

    def single_declaration(self, o: dict) -> tuple[list[int], int]:
        """The name of an axiom, definition, theorem, opaque constant or quotient, and the axioms it rests on."""
        U, E = self.S.union, self.E
        kind = next(k for k in DECLS if k in o)
        v = o[kind]
        m = E[v["type"]]
        if "value" in v:
            m = U(m, E[v["value"]])
        if kind == "axiom":
            self.axioms.append(v["name"])
            m = U(m, self.S.of(frozenset([len(self.axioms) - 1])))
        return [v["name"]], m

    def declaration(self, o: dict) -> None:
        names, m = self.inductive_block(o["inductive"]) if "inductive" in o else self.single_declaration(o)
        for n in names:
            self.decl[n] = m
        mine = self.early.intersection(names)
        if mine:
            self.early -= mine
            if m:  # the early mentions were read as resting on nothing: re-read them and every term above them
                for i, t in self.buffer:
                    self.E[i] = self.term(t)
        if not self.early:
            self.buffer.clear()

    def add_term(self, i: int, o: dict) -> None:
        if i != len(self.E):
            raise SystemExit(f"axiom-scan: term {i} out of order at line {self.lines}")
        self.E.append(self.term(o))
        if self.early:
            self.buffer.append((i, o))

    def add_name(self, o: dict) -> None:
        if o["in"] != len(self.name_part):
            raise SystemExit(f"axiom-scan: name {o['in']} out of order at line {self.lines}")
        v = o.get("str") or o["num"]
        self.name_pre.append(v["pre"])
        self.name_part.append(v["str"] if "str" in v else str(v["i"]))

    def check_format(self, o: dict) -> None:
        fmt = o["meta"]["format"]["version"]
        if not fmt.startswith("3."):
            raise SystemExit(f"axiom-scan: export format {fmt}, this reads 3.x")

    def read(self, line: bytes) -> None:
        o = loads(line)
        i = o.get("ie")
        if i is not None:
            self.add_term(i, o)
        elif "in" in o:
            self.add_name(o)
        elif "il" in o:
            return  # a universe level: it carries no axiom
        elif "meta" in o:
            self.check_format(o)
        elif any(k in o for k in DECLS):
            self.declaration(o)
        else:
            raise SystemExit(f"axiom-scan: unknown line {self.lines}: {line[:120]!r}")

    def run(self, path: Path) -> None:
        with open(path, "rb") as f:
            for line in f:
                self.lines += 1
                self.read(line)

    def rests_on(self, n: int) -> list[str]:
        return sorted(self.name(self.axioms[b]) for b in self.S.sets[self.decl[n]])


def pascal(s: str) -> str:
    """equational-theories -> EquationalTheories, as scripts/ci/_git.py names a library's modules."""
    return "".join(w[:1].upper() + w[1:] for w in s.replace("_", "-").split("-") if w)


def trusted_records(d: Path) -> dict[str, set[str]]:
    """record name -> its libraries (data/trusted/<library>.jsonl or data/trusted/<library>/<file>.jsonl)."""
    names: dict[str, set[str]] = {}
    gone: set[str] = set()
    for f in sorted(d.rglob("*.jsonl")):
        lib = f.parent.name if f.parent != d else f.stem
        for line in f.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                if "tombstone" in r:
                    gone.add(r["tombstone"])
                elif "name" in r:
                    names.setdefault(r["name"], set()).add(lib)
    return {n: libs for n, libs in names.items() if n not in gone}


def checked_path(arg: Path) -> Path:
    """A path given on the command line, resolved; it must lie in the working directory or the temporary directory
    (where CI keeps the export), so an argument cannot point the scan or its output anywhere else."""
    p = arg.resolve()
    roots = [Path.cwd(), Path(tempfile.gettempdir())] + ([Path(os.environ["RUNNER_TEMP"])] if os.environ.get("RUNNER_TEMP") else [])
    if not any(p.is_relative_to(r.resolve()) for r in roots):
        raise SystemExit(f"axiom-scan: {arg} is outside the working directory and the temporary directory")
    return p


def resting_users(s: Scan, declared: list[str]) -> dict[str, list[str]]:
    """For each declared axiom outside the standard three: the constants that rest on it (the axioms themselves excluded)."""
    resting: dict[str, list[str]] = {x: [] for x in declared if x not in STANDARD}
    own = set(s.axioms)
    for sid, ax in enumerate(s.S.sets):
        hit = [x for x in (s.name(s.axioms[b]) for b in ax) if x in resting]
        if hit:
            users = [s.name(n) for n, m in s.decl.items() if m == sid and n not in own]
            for x in hit:
                resting[x] += users
    return resting


def print_resting(resting: dict[str, list[str]]) -> None:
    for x, users in resting.items():
        shown = sorted(users, key=lambda u: (u.count("._") > 0, u))[:25]  # user-facing names first
        print(f"  {x}: {len(users)} constants rest on it{': ' + ', '.join(shown) if shown else ''}{' …' if len(users) > 25 else ''}")


def constant_of(record: str, by_name: dict[str, int], by_last: dict[str, list[str]]) -> int | None:
    """The constant a record names: by its full name, else (declared inside a namespace) the one constant that ends in it."""
    n = by_name.get(record)
    if n is not None:
        return n
    hits = [k for k in by_last.get(record.rsplit(".", 1)[-1], []) if k.endswith("." + record)]
    return by_name[hits[0]] if len(hits) == 1 else None


def audit_records(s: Scan, records_dir: Path, by_name: dict[str, int]) -> tuple[dict, list[str]]:
    """Every trusted record must be in the export and rest only on the standard axioms. Returns the report and the failures."""
    records = trusted_records(records_dir)
    by_last: dict[str, list[str]] = {}
    for k in by_name:
        by_last.setdefault(k.rsplit(".", 1)[-1], []).append(k)
    tree = records_dir.resolve().parents[1] / "Tengoku"  # data/trusted -> <checkout>/Tengoku
    missing: list[str] = []
    extra: list[str] = []
    absent: dict[str, int] = {}
    for r, libs in records.items():
        n = constant_of(r, by_name, by_last)
        if n is None:
            if any((tree / f"{pascal(lib)}.lean").exists() for lib in libs):  # a compiled library claims it
                missing.append(r)
            else:
                lib = min(libs)
                absent[lib] = absent.get(lib, 0) + 1
            continue
        beyond = [x for x in s.rests_on(n) if x not in STANDARD]
        if beyond:
            extra.append(f"{r} rests on {beyond}")
    held = len(records) - len(missing) - sum(absent.values())
    print(f"axiom-scan: {len(records)} trusted records, {held} in the export, {held - len(extra)} of them rest only on the standard axioms")
    if absent:
        print(
            "  not in the export, from libraries the tree does not compile: "
            + ", ".join(f"{k} {v}" for k, v in sorted(absent.items(), key=lambda x: -x[1]))
        )
    bad = [f"{len(missing)} trusted records of compiled libraries are not in the export: {missing[:10]}"] if missing else []
    bad += extra[:50]
    report = {
        "total": len(records),
        "in_export": held,
        "resting_only_on_standard_axioms": held - len(extra),
        "resting_on_more": extra,
        "missing_from_compiled_libraries": missing,
        "not_in_export_libraries_not_compiled": dict(sorted(absent.items())),
    }
    return report, bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("export", type=Path)
    ap.add_argument("--records", type=Path, help="data/trusted: every record must rest only on the standard axioms")
    ap.add_argument("--permitted", type=Path, help="write the declared axioms here (a JSON list)")
    ap.add_argument("--report", type=Path, help="write the verdict here as JSON")
    a = ap.parse_args()
    export, records_dir = checked_path(a.export), a.records and checked_path(a.records)
    permitted, report_path = a.permitted and checked_path(a.permitted), a.report and checked_path(a.report)

    s = Scan()
    s.run(export)
    bad: list[str] = []
    if s.early:
        bad.append(f"mentioned and never declared: {sorted(s.name(n) for n in s.early)[:10]}")
    declared = [s.name(n) for n in s.axioms]
    print(f"axiom-scan: {s.lines} lines, {len(s.E)} terms, {len(s.decl)} constants, axioms declared: {declared}")
    bad += [f"the export declares the axiom {x}" for x in declared if x not in PRELUDE]

    resting = resting_users(s, declared)
    print_resting(resting)
    if resting.get("sorryAx"):
        bad.append(f"{len(resting['sorryAx'])} constants rest on sorryAx")

    report: dict = {
        "export": {"lines": s.lines, "terms": len(s.E), "constants": len(s.decl)},
        "axioms_declared": declared,
        "standard_axioms": sorted(STANDARD),
        "resting_on_other_axioms": {x: sorted(users) for x, users in resting.items()},
    }
    if records_dir:
        report["trusted_records"], record_failures = audit_records(s, records_dir, {s.name(n): n for n in s.decl})
        bad += record_failures

    if permitted:
        permitted.write_text(json.dumps(declared))
    if report_path:
        report["failures"] = bad
        report["passed"] = not bad
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    for b in bad:
        print(f"::error::axiom-scan: {b}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
