#!/usr/bin/env python3
"""isnad.py — the identity of a theorem (docs/isnad.md).

The Lean program `tengoku-isnad` (TengokuIsnad.lean) writes the canonical form of each theorem's elaborated statement; this hashes it (sha256,
here, so the hashing is auditable and does not depend on Lean's `String.hash`) and names it. Everything here is a pure function of those lines
except `id`, `verify` and `selftest`, which run the Lean program.

  isnad.py explain <id | tag line>              decode an id or a tag into words (offline)
  isnad.py id --module M [--name N ...]         the id lines of a module's theorems (needs a built tree: lake build tengoku-isnad)
  isnad.py verify '<tag line>' --module M --name N      recompute and compare id, shape and vocab of one theorem
  isnad.py tag --module M [--write]             write each theorem's tag into its source file (a dry run without --write; docs/isnad.md, "The tagger")
  isnad.py strip PATH... [--write]              take the tags out again
  isnad.py check-tags --module M...             every taggable theorem of these modules carries exactly the tag the build computes, and no other tag is there (the merge queue, for a tag PR)
  isnad.py tagtest                              the tagger on a real compile: tag, tag again, strip; every identity unchanged (CI)
  isnad.py selftest                             the golden ids of the Lean core theorems (any Lean install gives the same bytes)
  isnad.py laws [--emit]                        the laws of the recipe (renaming changes nothing, a different statement does) on real
                                                elaborated statements, with plain Lean: no Mathlib, no tree; --emit prints the Lean script

The id of a theorem: <kind>.<hyps>h<vars>v.s<log2 nodes>.<sha256(canonical)[:12]>. A tag line (the last line of a docstring):
@isnad1 id=<id> from=<seed|translated|novel> src=<0|-|hex12> shape=<8hex> vocab=<8hex>
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION = "1"
EXE = ".lake/build/bin/tengoku-isnad"
TAG_PREFIX = "@isnad"  # a tag line starts with it, followed by the format version
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


def split_tag(line: str) -> dict[str, str]:
    """The `key=value` fields of a tag line and its `version`: the line is split on single spaces, not matched by a pattern (a pattern with nested repetition
    backtracks exponentially on a crafted line: sixty characters in a docstring would hang the tool). Anything that is not exactly one line of printable
    ASCII, one space between tokens, `@isnad<digits>` first and distinct known `key=value` pairs after it is refused."""
    text = line.strip()
    if not text.isascii() or not text.isprintable():
        raise ValueError(f"not an isnad tag: {text[:80]!r}")
    head, *pairs = text.split(" ")
    if not (head.startswith(TAG_PREFIX) and head[len(TAG_PREFIX) :].isdigit()) or "" in pairs:
        raise ValueError(f"not an isnad tag: {text[:80]!r}")
    version = head[len(TAG_PREFIX) :]
    if version != VERSION:
        raise ValueError(f"isnad format {version} is not implemented here (this tool is format {VERSION}): its recipe is not known")
    out = {"version": version}
    for pair in pairs:
        key, eq, value = pair.partition("=")
        if not eq or not value or key not in FIELDS:
            raise ValueError(f"a tag has exactly the fields {', '.join(FIELDS)}, as key=value: {pair[:40]!r}")
        if key in out:
            raise ValueError(f"field {key} twice")
        out[key] = value
    missing = [f for f in FIELDS if f not in out]
    if missing:
        raise ValueError(f"a tag has exactly the fields {', '.join(FIELDS)} (missing {missing})")
    return out


def check_values(out: dict[str, str]) -> None:
    """The values of a split tag: the id's shape, `from`, `src`, and the two 8-digit hashes, and `from` with `src` as one claim."""
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


def parse_tag(line: str) -> dict[str, str]:
    """The fields of a tag line, with `version`. Raises ValueError for anything that is not exactly one well-formed tag."""
    out = split_tag(line)
    check_values(out)
    return out


def format_tag(rec: Record, origin: str, src: str | None = None) -> str:
    """The tag line of a theorem. `src` defaults by origin: `0` for seed and novel content, `-` (source side not available) for a translation."""
    if origin not in FROM:
        raise ValueError(f"from= is one of {', '.join(FROM)}")
    if src is None:
        src = "-" if origin == "translated" else "0"
    line = f"{TAG_PREFIX}{VERSION} id={rec.id} from={origin} src={src} shape={rec.shape} vocab={rec.vocab}"
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


def run_exe_lines(args: list[str], exe: str | None = None, cwd: Path = ROOT, extra_path: Path | None = None) -> list[str]:
    """The output lines of `tengoku-isnad`; `extra_path` is a directory of compiled modules that its imports may name (added to the tree's LEAN_PATH)."""
    cmd = ["lake", "env", exe or EXE, *args]
    if extra_path is not None:
        cmd = [
            "lake",
            "env",
            "sh",
            "-c",
            'LEAN_PATH="$1:$LEAN_PATH"; export LEAN_PATH; shift; exec "$@"',
            "sh",
            str(extra_path),
            exe or EXE,
            *args,
        ]
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    if r.returncode not in (0, 1) or (r.returncode == 1 and not r.stdout):
        sys.exit(f"{' '.join(cmd)}: {r.stderr.strip()[-400:] or r.stdout.strip()[-400:]}\n(build it first: lake build tengoku-isnad)")
    return [ln for ln in r.stdout.splitlines() if ln.strip()]


def run_exe(args: list[str], exe: str | None = None, cwd: Path = ROOT, extra_path: Path | None = None) -> list[Record]:
    return [Record(ln) for ln in run_exe_lines(args, exe, cwd, extra_path)]


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
    """The laws, with plain Lean: the script goes in through stdin, so there is no file and no path to name."""
    r = subprocess.run(["lake", "env", "lean", "--stdin"], input=laws_script(), cwd=ROOT, capture_output=True, text=True, check=False)
    print((r.stdout + r.stderr).strip())
    return 0 if r.returncode == 0 and "isnad laws:" in r.stdout + r.stderr else 1


RANGE_TAG = "isnad1-range"
Range = tuple[int, int, int, int]


def parse_range_line(line: str) -> tuple[str, str, Range, Range]:
    """`isnad1-range <name> <module> <l:c> <l:c> <l:c> <l:c>` (`tengoku-isnad --ranges`) as (name, module, command range, name range)."""
    parts = line.rstrip("\n").split("\t")
    if len(parts) != 7 or parts[0] != RANGE_TAG:
        raise ValueError(f"not an {RANGE_TAG} line: {line[:80]!r}")

    def pos(a: str, b: str) -> Range:
        (l1, c1), (l2, c2) = a.split(":"), b.split(":")
        return int(l1), int(c1), int(l2), int(c2)

    return parts[1], parts[2], pos(parts[3], parts[4]), pos(parts[5], parts[6])


def origin_of(module: str) -> str:
    """Where a module's theorems come from: the seed (Mathlib, Batteries, …), CompeteMath's own (Native), or a translation (every library under Tengoku/)."""
    for prefix, origin in (("Tengoku.Seed", "seed"), ("Tengoku.Native", "novel")):
        if module == prefix or module.startswith(prefix + "."):
            return origin
    return "translated"


def module_file(module: str, root: Path = ROOT) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def _tagger():
    """scripts/isnad_tag.py (imported on use: the identity commands do not need it)."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import isnad_tag

    return isnad_tag


def read_source(path: Path) -> str:
    return path.read_bytes().decode("utf-8")  # bytes: a CRLF file must stay visible as one, not be turned into LF by a text read


def plan_tags(recs: list[Record], ranges: list[str], origin: str | None = None, src: str | None = None):
    """Per module, the items to tag (record joined to range by module and name), and (name, reason) for what cannot be: a name two theorems share, a record Lean gave no range."""
    tg = _tagger()
    where: dict[tuple[str, str], list[tuple[Range, Range]]] = {}
    for ln in ranges:
        name, module, rng, sel = parse_range_line(ln)
        where.setdefault((module, name), []).append((rng, sel))
    seen: dict[tuple[str, str], int] = {}
    for r in recs:
        seen[(r.module, r.name)] = seen.get((r.module, r.name), 0) + 1
    plan: dict[str, list] = {}
    skipped: list[tuple[str, str]] = []
    for r in recs:
        key = (r.module, r.name)
        if seen[key] > 1 or len(where.get(key, [])) > 1:
            skipped.append((r.name, "the same name for two theorems of the module"))
        elif key not in where:
            skipped.append((r.name, "Lean recorded no position for it"))
        else:
            rng, sel = where[key][0]
            plan.setdefault(r.module, []).append(tg.Item(r.name, rng, sel, format_tag(r, origin or origin_of(r.module), src)))
    return plan, skipped


def tag_files(plan: dict[str, list], root: Path, write: bool) -> tuple[dict[str, int], list[tuple[str, str]]]:
    """Tag each module's file; a result that is not equivalent to what was there is never written. Returns the counts and the (name or file, reason) skipped."""
    tg = _tagger()
    total = {"added": 0, "replaced": 0, "same": 0, "created": 0}
    skipped: list[tuple[str, str]] = []
    for module, items in sorted(plan.items()):
        path = module_file(module, root)
        if not path.is_file():
            skipped += [(it.name, f"{path} does not exist") for it in items]
            continue
        old = read_source(path)
        new, counts, why = tg.tag_text(old, items)
        skipped += why
        if not tg.equivalent(old, new):
            skipped.append((str(path), "tagging would change more than tags: left alone"))
            continue
        for k, v in counts.items():
            total[k] += v
        if write and new != old:
            path.write_bytes(new.encode("utf-8"))
    return total, skipped


def strip_files(paths: list[Path], write: bool) -> int:
    """Take the tags out of these files (a directory: its *.lean files); returns how many files had any."""
    tg = _tagger()
    files = [f for p in paths for f in (sorted(p.rglob("*.lean")) if p.is_dir() else [p])]
    changed = 0
    for f in files:
        old = read_source(f)
        new = tg.strip_text(old)
        if new != old:
            changed += 1
            if write:
                f.write_bytes(new.encode("utf-8"))
    return changed


TAGGER_DIR = ROOT / "tools" / "isnad" / "tagger"
FIXTURE_MODULE = "IsnadFixture"
# the fixture's theorems the tagger must leave alone, each for a reason of its own: `ext` makes two theorems nobody wrote, a structure's fields are theorems whose
# range is only their name (one of them behind `protected`, one with a docstring of its own)
FIXTURE_NOT_TAGGED = {"Fx.Pt.ext", "Fx.Pt.ext_iff", "Fx.Cancel.left_zero", "Fx.Cancel.right_zero", "Fx.Cancel.both"}
FIXTURE_NO_RANGE = {"Fx.Pt.mk.inj"}  # a theorem `structure` generates and Lean gives no position


def compile_fixture(d: Path) -> None:
    """Compile `d/IsnadFixture.lean` to an olean next to it (the module name comes from the path under --root), with the tree's toolchain."""
    r = subprocess.run(
        ["lake", "env", "lean", f"--root={d}", "-o", str(d / f"{FIXTURE_MODULE}.olean"), str(d / f"{FIXTURE_MODULE}.lean")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if r.returncode != 0:
        sys.exit(f"the fixture does not compile:\n{(r.stdout + r.stderr)[-800:]}")


def fixture_facts(d: Path, exe: str | None) -> tuple[list[Record], list[str]]:
    args = ["--import", FIXTURE_MODULE, "--module", FIXTURE_MODULE]
    return run_exe(args, exe, extra_path=d), run_exe_lines(["--ranges", *args], exe, extra_path=d)


def identities(recs: list[Record]) -> dict[str, tuple[str, str, str]]:
    return {r.name: (r.id, r.shape, r.vocab) for r in recs}


def tagtest(exe: str | None = None) -> int:
    """The tagger on a real compile (CI, job isnad): Lean's ranges for the fixture are the ones the repository pins; tagging, tagging again and stripping each
    leave every theorem's identity as it was (the statements are compiled again after each step); the second tag is a no-op; the stripped file is equivalent to the
    original. Anything else is a bug in the tagger or in the ranges, and the first one found is reported."""
    tg = _tagger()
    original = read_source(TAGGER_DIR / "Fixture.lean")
    pinned = json.loads((TAGGER_DIR / "ranges.json").read_text(encoding="utf-8"))
    problems: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        d = Path(tmp)
        path = d / f"{FIXTURE_MODULE}.lean"
        path.write_bytes(original.encode("utf-8"))
        compile_fixture(d)
        recs, ranges = fixture_facts(d, exe)
        fresh = {name: [list(r), list(s)] for name, _, r, s in map(parse_range_line, ranges)}
        if fresh != {n: [v["range"], v["sel"]] for n, v in pinned.items()}:
            problems.append("Lean's ranges for the fixture are not the ones in tools/isnad/tagger/ranges.json")
        before = identities(recs)

        plan, skipped = plan_tags(recs, ranges, "seed")
        counts, more = tag_files(plan, d, write=True)
        tagged = read_source(path)
        wanted = len(pinned) - len(FIXTURE_NOT_TAGGED)
        if {n for n, _ in skipped + more} != FIXTURE_NOT_TAGGED | FIXTURE_NO_RANGE or counts["added"] + counts["replaced"] + counts[
            "created"
        ] != wanted:
            problems.append(f"tagging did not tag exactly the {wanted} theorems it should: {counts}, skipped {skipped + more}")
        if tagged.count(TAG_PREFIX + VERSION + " id=") != wanted or not tg.equivalent(original, tagged):
            problems.append("the tagged file is not the original plus tags")
        compile_fixture(d)
        recs2, ranges2 = fixture_facts(d, exe)
        if identities(recs2) != before:
            problems.append("tagging changed the identity of a theorem")
        tag_of = {r.name: format_tag(r, "seed") for r in recs2}
        if any(tag_of[n] not in tagged for n in before if n not in FIXTURE_NOT_TAGGED | FIXTURE_NO_RANGE):
            problems.append("a tag in the file is not the one recomputed from the compiled statement")

        plan2, _ = plan_tags(recs2, ranges2, "seed")
        counts2, _ = tag_files(plan2, d, write=True)
        if read_source(path) != tagged or counts2["same"] != wanted:
            problems.append(f"tagging a tagged file is not a no-op: {counts2}")

        strip_files([d], write=True)
        stripped = read_source(path)
        if "@isnad" in stripped or not tg.equivalent(original, stripped):
            problems.append("the stripped file is not the original")
        compile_fixture(d)
        if identities(fixture_facts(d, exe)[0]) != before:
            problems.append("stripping changed the identity of a theorem")
    for msg in problems:
        print(f"FAIL {msg}")
    print(
        f"isnad tagtest: {wanted} theorems tagged, tagged again, stripped"
        + (" — all as expected" if not problems else f" — {len(problems)} problem(s)")
    )
    return 1 if problems else 0


def cmd_tag(a: argparse.Namespace) -> int:
    mods = [x for m in a.module for x in ("--module", m)] + [x for n in a.name for x in ("--name", n)]
    plan, skipped = plan_tags(run_exe(mods, a.exe), run_exe_lines(["--ranges", *mods], a.exe), a.origin, a.src)
    counts, more = tag_files(plan, Path(a.root), a.write)
    for name, why in skipped + more:
        print(f"skipped {name}: {why}")
    print(
        f"isnad tag: {counts['added']} added, {counts['replaced']} replaced, {counts['same']} already right, {counts['created']} docstrings created; {len(skipped + more)} skipped"
    )
    print("" if a.write else "dry run: nothing written (add --write)")
    return 0


def tag_lines_of(text: str) -> int:
    """How many tag lines the docstrings of this source hold."""
    tg = _tagger()
    return sum(1 for kind, a, b in tg.scan(text) if kind == "doc" for ln in text[a + 3 : b - 2].split("\n") if tg.TAG_LINE.match(ln))


def check_tags(recs: list[Record], ranges: list[str], modules: list[str], root: Path) -> tuple[list[str], str]:
    """A tag PR's modules, as built: tagging them again must change nothing (every taggable theorem has exactly the tag the build computes: none missing, none
    stale, no docstring to create) and no tag may be there that belongs to no theorem. Returns (problems, a summary line)."""
    plan, skipped = plan_tags(recs, ranges)
    counts, more = tag_files(plan, root, write=False)
    present = 0
    for m in modules:
        path = module_file(m, root)
        present += tag_lines_of(read_source(path)) if path.is_file() else 0
    problems = [
        f"{counts[k]} theorem(s) {why}"
        for k, why in (
            ("added", "have no tag"),
            ("replaced", "have a tag that is not the one the build computes"),
            ("created", "have no docstring to carry one"),
        )
        if counts[k]
    ]
    # what the tagger leaves alone by rule (a structure's field, a generated twin: `tag_text` says why) is not a problem; a module that is missing, or a result that would
    # change more than tags, is
    refused = [(name, why) for name, why in more if why.endswith("does not exist") or why.startswith("tagging would change more than tags")]
    problems += [f"{name}: {why}" for name, why in refused]
    if present != counts["same"]:
        problems.append(
            f"{present} tag line(s) in the docstrings but {counts['same']} theorem(s) carry the right one: a tag belongs to no theorem, or is on a theorem twice"
        )
    by_rule = len(skipped) + len(more) - len(refused)
    return problems, f"{counts['same']} tags right, {by_rule} theorems skipped by rule, {len(recs)} theorems in {len(modules)} modules"


def cmd_check_tags(a: argparse.Namespace) -> int:
    mods = [x for m in a.module for x in ("--module", m)]
    problems, summary = check_tags(run_exe(mods, a.exe), run_exe_lines(["--ranges", *mods], a.exe), a.module, Path(a.root))
    if problems:
        print("isnad check-tags: " + "; ".join(problems[:10]) + (f"; and {len(problems) - 10} more" if len(problems) > 10 else ""))
        return 1
    print(f"isnad check-tags ok: {summary}")
    return 0


def cmd_strip(a: argparse.Namespace) -> int:
    n = strip_files([Path(p) for p in a.paths], a.write)
    print(f"isnad strip: tags in {n} file(s)" + ("" if a.write else " (dry run: nothing written; add --write)"))
    return 0


def cmd_id(recs: list[Record]) -> int:
    for r in recs:
        print(f"{r.name}\t{r.id}\tshape={r.shape}\tvocab={r.vocab}")
    return 0


def cmd_verify(tag_line: str, recs: list[Record]) -> int:
    tag = parse_tag(tag_line)
    if len(recs) != 1:
        print(f"verify needs exactly one theorem (--name), got {len(recs)}")
        return 2
    r = recs[0]
    diffs = [f"{k}: tag {tag[k]}, recomputed {v}" for k, v in (("id", r.id), ("shape", r.shape), ("vocab", r.vocab)) if tag[k] != v]
    print("\n".join(diffs) if diffs else f"{r.name}: the tag matches the compiled statement")
    return 1 if diffs else 0


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("explain").add_argument("what")
    for name in ("id", "verify"):
        s = sub.add_parser(name)
        if name == "verify":
            s.add_argument("tag")
        s.add_argument("--module", action="append", required=True)
        s.add_argument("--name", action="append", default=[])
        s.add_argument("--exe")
    s = sub.add_parser("tag")
    s.add_argument("--module", action="append", required=True)
    s.add_argument("--name", action="append", default=[])
    s.add_argument(
        "--origin", choices=FROM, help="default: by where the module lives (Tengoku.Seed -> seed, Tengoku.Native -> novel, else translated)"
    )
    s.add_argument("--src", help="default: 0 for seed and novel, - for translated")
    s.add_argument("--root", default=str(ROOT))
    s.add_argument("--write", action="store_true")
    s.add_argument("--exe")
    s = sub.add_parser("check-tags")
    s.add_argument("--module", action="append", required=True)
    s.add_argument("--root", default=str(ROOT))
    s.add_argument("--exe")
    s = sub.add_parser("strip")
    s.add_argument("paths", nargs="+")
    s.add_argument("--write", action="store_true")
    sub.add_parser("tagtest").add_argument("--exe")
    sub.add_parser("selftest").add_argument("--exe")
    sub.add_parser("laws").add_argument("--emit", action="store_true")
    return ap


def main(argv: list[str]) -> int:
    a = build_parser().parse_args(argv)
    if a.cmd == "explain":
        print(explain_tag(a.what) if a.what.lstrip().startswith(TAG_PREFIX) else explain_id(a.what))
        return 0
    if a.cmd == "tag":
        return cmd_tag(a)
    if a.cmd == "strip":
        return cmd_strip(a)
    if a.cmd == "check-tags":
        return cmd_check_tags(a)
    if a.cmd == "tagtest":
        return tagtest(a.exe)
    if a.cmd == "selftest":
        return selftest(a.exe)
    if a.cmd == "laws":
        if a.emit:
            print(laws_script())
            return 0
        return run_laws()
    recs = run_exe([x for m in a.module for x in ("--module", m)] + [x for n in a.name for x in ("--name", n)], a.exe)
    return cmd_id(recs) if a.cmd == "id" else cmd_verify(a.tag, recs)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
