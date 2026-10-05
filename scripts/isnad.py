#!/usr/bin/env python3
"""isnad.py — the identity of a theorem (docs/isnad.md).

The Lean program `tengoku-isnad` (TengokuIsnad.lean) writes the canonical form of each theorem's elaborated statement; this hashes it (sha256,
here, so the hashing is auditable and does not depend on Lean's `String.hash`) and names it. Everything here is a pure function of those lines
except `id`, `verify` and `selftest`, which run the Lean program.

  isnad.py explain <id | tag line>              decode an id or a tag into words (offline)
  isnad.py id --module M [--name N ...]         the id lines of a module's theorems (needs a built tree: lake build tengoku-isnad)
  isnad.py verify '<tag line>' --module M --name N      recompute and compare id, shape and vocab of one theorem
  isnad.py selftest                             the golden ids of the Lean core theorems (any Lean install gives the same bytes)
  isnad.py laws [--emit]                        the laws of the recipe (renaming changes nothing, a different statement does) on real
                                                elaborated statements, with plain Lean: no Mathlib, no tree; --emit prints the Lean script

The id of a theorem: <kind>.<hyps>h<vars>v.s<log2 nodes>.<sha256(canonical)[:12]>. A tag line (the last line of a docstring):
@isnad1 id=<id> from=<seed|translated|novel> src=<0|-|hex12> shape=<8hex> vocab=<8hex>
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION = "1"
EXE = ".lake/build/bin/tengoku-isnad"
GOLDEN = ROOT / "tools" / "isnad" / "golden.tsv"
LAWS = ROOT / "tools" / "isnad" / "laws_body.lean"
LEAN_SOURCE = ROOT / "TengokuIsnad.lean"
FROM = ("seed", "translated", "novel")
KINDS = {
    "eq": "an equation (=)",
    "le": "an inequality (≤ or ≥)",
    "lt": "a strict inequality (< or >)",
    "ne": "a disequality (≠)",
    "iff": "an equivalence (↔)",
    "ex": "an existence (∃)",
    "and": "a conjunction (∧)",
    "or": "a disjunction (∨)",
    "not": "a negation (¬)",
    "var": "a bound variable (a statement about a proposition given as a variable)",
    "sort": "a type, not a proposition",
    "other": "something else",
}
ID_RE = re.compile(r"(?P<kind>[a-z0-9]{1,8})\.(?P<hyps>\d+)h(?P<vars>\d+)v\.s(?P<size>\d+)\.(?P<sig>[0-9a-f]{12})")
TAG_RE = re.compile(r"@isnad(?P<version>\d+) (?P<fields>(?:[a-z]+=\S+ ?)+)")
FIELDS = ("id", "from", "src", "shape", "vocab")
HEX = re.compile(r"[0-9a-f]+")


def sha(text: str, n: int) -> str:
    """The first n hex digits of the sha256 of the text (UTF-8)."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:n]


def size_class(nodes: int) -> int:
    """floor(log2 nodes): `s4` is 16 to 31 expression nodes."""
    return max(nodes, 1).bit_length() - 1


class Record:
    """One line of `tengoku-isnad`: a theorem with its canonical strings."""

    FIELDS = ("name", "module", "kind", "hyps", "vars", "nodes", "canonical", "shape", "vocab")

    def __init__(self, line: str):
        parts = line.rstrip("\n").split("\t")
        if len(parts) != 10 or parts[0] != f"isnad{VERSION}":
            raise ValueError(f"not an isnad{VERSION} record: {line[:80]!r}")
        self.name, self.module, self.kind = parts[1], parts[2], parts[3]
        self.hyps, self.vars, self.nodes = int(parts[4]), int(parts[5]), int(parts[6])
        self.canonical, self.shape_canonical, self.vocabulary = parts[7], parts[8], parts[9]

    @property
    def id(self) -> str:
        return f"{self.kind}.{self.hyps}h{self.vars}v.s{size_class(self.nodes)}.{sha(self.canonical, 12)}"

    @property
    def shape(self) -> str:
        return sha(self.shape_canonical, 8)

    @property
    def vocab(self) -> str:
        return sha(self.vocabulary, 8)


def parse_tag(line: str) -> dict[str, str]:
    """The fields of a tag line, with `version`. Raises ValueError for anything that is not exactly one well-formed tag."""
    m = TAG_RE.fullmatch(line.strip())
    if not m:
        raise ValueError(f"not an isnad tag: {line.strip()[:80]!r}")
    if m.group("version") != VERSION:
        raise ValueError(
            f"isnad format {m.group('version')} is not implemented here (this tool is format {VERSION}): its recipe is not known"
        )
    out = {"version": m.group("version")}
    for pair in m.group("fields").split():
        k, _, v = pair.partition("=")
        if k in out:
            raise ValueError(f"field {k} twice")
        out[k] = v
    missing = [f for f in FIELDS if f not in out]
    if missing or set(out) - set(FIELDS) - {"version"}:
        raise ValueError(
            f"a tag has exactly the fields {', '.join(FIELDS)} (missing {missing}, extra {sorted(set(out) - set(FIELDS) - {'version'})})"
        )
    if not ID_RE.fullmatch(out["id"]):
        raise ValueError(f"malformed id {out['id']!r}")
    if out["from"] not in FROM:
        raise ValueError(f"from= is one of {', '.join(FROM)}")
    if out["src"] not in ("0", "-") and not (len(out["src"]) == 12 and HEX.fullmatch(out["src"])):
        raise ValueError("src= is 0, - or 12 hex digits")
    for f in ("shape", "vocab"):
        if not (len(out[f]) == 8 and HEX.fullmatch(out[f])):
            raise ValueError(f"{f}= is 8 hex digits")
    # from= and src= are one claim: only a translation has a source side (`-`: not available, or its 12-digit sig); seed and novel content has none
    if (out["from"] == "translated") == (out["src"] == "0"):
        raise ValueError("from=translated needs src=- or a 12-digit source id; from=seed and from=novel need src=0")
    return out


def format_tag(rec: Record, origin: str, src: str | None = None) -> str:
    """The tag line of a theorem. `src` defaults by origin: `0` for seed and novel content, `-` (source side not available) for a translation."""
    if origin not in FROM:
        raise ValueError(f"from= is one of {', '.join(FROM)}")
    line = f"@isnad{VERSION} id={rec.id} from={origin} src={src if src is not None else ('-' if origin == 'translated' else '0')} shape={rec.shape} vocab={rec.vocab}"
    parse_tag(line)  # never write a tag that the reader would refuse
    return line


def explain_id(ident: str) -> str:
    m = ID_RE.fullmatch(ident)
    if not m:
        raise ValueError(f"not an isnad id: {ident!r}")
    size = int(m.group("size"))
    kind = m.group("kind")
    what = KINDS.get(kind, f"a statement whose conclusion is `{kind}…` (the last part of the head constant, shortened)")
    h, v = int(m.group("hyps")), int(m.group("vars"))
    return (
        f"concludes {what}; {h} hypothes{'is' if h == 1 else 'es'} and {v} variable{'' if v == 1 else 's'} "
        f"(typeclass binders are not counted); the statement has {2**size} to {2 ** (size + 1) - 1} expression nodes; "
        f"identity {m.group('sig')} = the first 12 hex digits of the sha256 of its canonical elaborated form"
    )


def explain_tag(line: str) -> str:
    t = parse_tag(line)
    src = {"0": "not a translation", "-": "a translation whose source side is not available"}.get(
        t["src"],
        f"a translation; the source statement's identity is {t['src']}"
        + (" (the same as this one: the statement was kept exactly)" if t["src"] == t["id"].rsplit(".", 1)[1] else ""),
    )
    origin = {
        "seed": "seeded upstream code (Tengoku/Seed)",
        "translated": "a verified translation of another library",
        "novel": "new content written for Tengoku",
    }[t["from"]]
    return (
        f"isnad format {t['version']}. This theorem {explain_id(t['id'])}.\n"
        f"  from={t['from']}: {origin}\n  src={t['src']}: {src}\n"
        f"  shape={t['shape']}: the pattern with every constant replaced by its order of first appearance; the same shape is the same statement over different objects\n"
        f"  vocab={t['vocab']}: the set of constants mentioned, without the logical connectives; the same vocab is the same objects arranged differently"
    )


def run_exe(args: list[str], exe: str | None = None, cwd: Path = ROOT) -> list[Record]:
    cmd = ["lake", "env", exe or EXE, *args]
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    if r.returncode not in (0, 1) or (r.returncode == 1 and not r.stdout):
        sys.exit(f"{' '.join(cmd)}: {r.stderr.strip()[-400:] or r.stdout.strip()[-400:]}\n(build it first: lake build tengoku-isnad)")
    return [Record(ln) for ln in r.stdout.splitlines() if ln.strip()]


def golden() -> list[tuple[str, str, str, str]]:
    """(import module, theorem, expected id, expected shape+vocab) rows of tools/isnad/golden.tsv."""
    rows = []
    for ln in GOLDEN.read_text().splitlines():
        if ln.strip() and not ln.startswith("#"):
            mod, name, ident, sv = ln.split("\t")
            rows.append((mod, name, ident, sv))
    return rows


def selftest(exe: str | None = None) -> int:
    bad = 0
    rows = golden()
    for mod, name, ident, sv in rows:
        recs = run_exe(["--import", mod, "--module", mod, "--name", name], exe)
        got = next((r for r in recs if r.name == name), None)
        want = f"{ident} {sv}"
        have = f"{got.id} {got.shape}.{got.vocab}" if got else "missing"
        if have != want:
            bad += 1
            print(f"FAIL {name}: expected {want}, got {have}")
    print(
        f"isnad selftest: {len(rows) - bad}/{len(rows)} golden ids reproduced"
        + ("" if not bad else " — the recipe or the toolchain changed")
    )
    return 1 if bad else 0


def laws_script() -> str:
    """The Lean script of the laws: the canonicaliser's own code (the CANON block of TengokuIsnad.lean, one source of truth) and the laws."""
    src = LEAN_SOURCE.read_text(encoding="utf-8")
    block = src[src.index("-- BEGIN CANON") : src.index("-- END CANON")]
    return "import Lean\nopen Lean\n\nnamespace Isnad\n" + block + "end Isnad\n\n" + LAWS.read_text(encoding="utf-8")


def run_laws() -> int:
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "IsnadLaws.lean"
        f.write_text(laws_script(), encoding="utf-8")
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, capture_output=True, text=True, check=False)
        print((r.stdout + r.stderr).strip())
        return 0 if r.returncode == 0 and "isnad laws:" in r.stdout + r.stderr else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    e = sub.add_parser("explain")
    e.add_argument("what")
    for name in ("id", "verify"):
        s = sub.add_parser(name)
        if name == "verify":
            s.add_argument("tag")
        s.add_argument("--module", action="append", required=True)
        s.add_argument("--name", action="append", default=[])
        s.add_argument("--exe")
    t = sub.add_parser("selftest")
    t.add_argument("--exe")
    lw = sub.add_parser("laws")
    lw.add_argument("--emit", action="store_true")
    a = ap.parse_args(argv)
    if a.cmd == "explain":
        print(explain_tag(a.what) if a.what.lstrip().startswith("@isnad") else explain_id(a.what))
        return 0
    if a.cmd == "selftest":
        return selftest(a.exe)
    if a.cmd == "laws":
        if a.emit:
            print(laws_script())
            return 0
        return run_laws()
    args = [x for m in a.module for x in ("--module", m)] + [x for n in a.name for x in ("--name", n)]
    recs = run_exe(args, a.exe)
    if a.cmd == "id":
        for r in recs:
            print(f"{r.name}\t{r.id}\tshape={r.shape}\tvocab={r.vocab}")
        return 0
    tag = parse_tag(a.tag)
    if len(recs) != 1:
        print(f"verify needs exactly one theorem (--name), got {len(recs)}")
        return 2
    r = recs[0]
    diffs = [f"{k}: tag {tag[k]}, recomputed {v}" for k, v in (("id", r.id), ("shape", r.shape), ("vocab", r.vocab)) if tag[k] != v]
    print("\n".join(diffs) if diffs else f"{r.name}: the tag matches the compiled statement")
    return 1 if diffs else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
