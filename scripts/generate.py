#!/usr/bin/env python3
"""Turn verified records into tree modules.

    python3 scripts/generate.py --corpus <path to equational_theories checkout> [--libraries equational-theories]

For each non-seed library with `source_path` records (data/staging + data/trusted):

  Tengoku/<Library>/Deps/<Module>.lean   the corpus modules the records' contexts
                                         pasted (verbatim source, imports mapped),
                                         and Deps/Equations.lean regenerated from
                                         every `equation N := law` in the corpus —
                                         all under `namespace <Library>`
  Tengoku/<Library>/<source path>.lean   one module per original source file:
                                         the file's own earlier declarations (from
                                         the records' `context`, after the prelude)
                                         + every verified theorem of that file
  Tengoku/<Library>.lean                 imports all of the above

Everything from a corpus lives under its own namespace (`EquationalTheories.*`),
so a corpus type that shares a name with a seeded one (`FreeMagma`) can coexist.
Records are the source of truth for theorems; the corpus checkout is only read
for definition modules, exactly as the translation harness reads it.
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from seed import IMPORT_RE, PACKAGES, module_map  # noqa: E402

# Only TRUSTED records become modules of the tree. A staging record (both
# gates passed, module not yet proven to build) is promoted by
# scripts/promote.py, which builds its module before moving it here; nothing
# staging or tentative is ever importable through Tengoku.All.
DATA_TIERS = ("trusted",)
FILE_MARKER_RE = re.compile(r"^-- \[Emissary\] (\S+), everything before line \d+[^\n]*\n", re.M)
PRELUDE_MODULE_RE = re.compile(r"^-- \[Emissary prelude\] (\S+) — verbatim", re.M)
EQUATION_LINE_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*equation\s+(\d+)\s*:=\s*(.+?)\s*$", re.M)
UNSAFE_MODULE_RE = re.compile(
    r"^\s*(?:scoped\s+)?(initialize|builtin_initialize|register_simp_attr|register_option|register_label_attr|register_tag_attr|register_parametric_attr)\b",
    re.M,
)


# Namespacing a corpus module (`namespace EquationalTheories … end`) keeps its
# own names (Magma, EquationN, FreeMagma) from clashing with seeded ones — but
# a corpus file also EXTENDS outside namespaces (`def Lean.MVarId.congrWith`,
# `theorem Eq.comm'`), and inside the wrapper those would silently become
# `EquationalTheories.Lean.MVarId.congrWith`, breaking every `m.congrWith`.
# A dotted declaration whose head is an outside namespace gets `_root_.`;
# a module that opens an outside namespace block is left unwrapped.
TOOLCHAIN_ROOTS = set(
    """
Lean Init Std Eq Ne HEq Nat Int List Array String Char Option Prod Sum Fin Function Sigma PSigma Subtype Quot Quotient
Decidable Bool Iff And Or Not Exists True False Unit PUnit IO Task Id StateT ReaderT ExceptT Except Monad Functor
Applicative HashMap HashSet RBMap ByteArray Float UInt8 UInt16 UInt32 UInt64 USize Empty PEmpty Classical WellFounded Acc
Setoid Equivalence Inhabited Nonempty Subsingleton DecidableEq BEq Hashable Ord LT LE Add Mul Sub Div Neg HAdd HMul HSub HDiv
Membership Singleton Insert EmptyCollection Union Inter SDiff HasSubset Coe CoeFun CoeSort Zero One Dvd Mod Pow HPow Append
GetElem Bind Pure Seq SeqLeft SeqRight ToString Repr Format Syntax Name Expr Level MVarId FVarId Meta Elab Tactic Term Command
""".split()
)


def seed_heads(out: Path) -> set[str]:
    """First segments of every declaration/namespace in the seeded tree."""
    heads = set(TOOLCHAIN_ROOTS)
    rx = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*(?:namespace|def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([A-Za-z_][\w']*)",
        re.M,
    )
    for f in (out / "Tengoku").rglob("*.lean"):
        if "EquationalTheories" in f.parts or "CompeteMath" in f.parts:
            continue
        try:
            heads.update(rx.findall(f.read_text(encoding="utf-8", errors="ignore")))
        except OSError:
            pass
    return heads


DECL_HEAD_RE = re.compile(
    r"^(\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*(?:def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+)([A-Za-z_][\w']*)\.",
    re.M,
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w']*)", re.M)


def rootify(body: str, external: set[str]) -> str:
    """`def Lean.MVarId.congrWith` at the top level of a file extends an outside
    namespace and must stay there (`_root_.`) once the file is wrapped. The
    same spelling INSIDE the file's own `namespace Asterix` block names
    `Asterix.Denumerable.notMemFinset`, and its callers rely on that — so the
    rewrite applies only at namespace depth zero."""
    out, stack = [], []
    for line in body.splitlines():
        m = re.match(r"^(?:noncomputable\s+)?(namespace|section)\b", line)
        if m:
            stack.append(m.group(1))
        elif re.match(r"^end\b", line) and stack:
            stack.pop()
        if "namespace" not in stack:
            line = DECL_HEAD_RE.sub(lambda mm: f"{mm.group(1)}{'_root_.' if mm.group(2) in external else ''}{mm.group(2)}.", line)
        out.append(line)
    return "\n".join(out)


def opens_external_namespace(body: str, external: set[str]) -> bool:
    return any(h in external for h in NAMESPACE_RE.findall(body))


def wrap(body: str, lib_ns: str, external: set[str]) -> str:
    if opens_external_namespace(body, external):
        # Its declarations extend an outside namespace and must land there; the
        # library's own names (Magma, EquationN, the Deps) are reached by opening it.
        return f"-- left unwrapped: this module opens an outside namespace block\nopen {lib_ns}\n\n{body.strip()}\n"
    return f"namespace {lib_ns}\n\n{rootify(body, external).strip()}\n\nend {lib_ns}\n"


def unclosed_scopes(text: str) -> list[str]:
    """`end` lines closing every namespace/section `text` opens and never
    closes, innermost first. A file prefix ends before the file's own
    `end <ns>`, so the wrapper must close what it left open."""
    stack: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^(?:noncomputable\s+)?(namespace|section)\b[ \t]*([\w.«»]*)", line)
        if m:
            stack.append(m.group(2))
            continue
        m = re.match(r"^end\b[ \t]*([\w.«»]*)", line)
        if m and stack:
            stack.pop()
    return [f"end {n}".rstrip() for n in reversed(stack)]


def strip_trailing_ends(proof: str) -> str:
    """A record's proof runs from its `:=` to the end of the script, so an
    agent-written script leaves `end <Namespace>` (closing what the context
    opened) at its tail. The module shares one prefix, so those must go."""
    lines = proof.rstrip().splitlines()
    while lines and (not lines[-1].strip() or re.match(r"^end\b", lines[-1])):
        lines.pop()
    return "\n".join(lines)


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def strip_corpus_attrs(text: str) -> str:
    def attrs(m):
        kept = [s.strip() for s in m.group(1).split(",") if s.strip() and not s.strip().startswith("equational_result")]
        return f"@[{', '.join(kept)}]" if kept else ""

    return re.sub(r"@\[([^\]]*)\]", attrs, text)


def map_imports(
    text: str, corpus_prefix: str, lib_ns: str, deps_available: set[str], corpus: Path | None = None, _seen: set[str] | None = None
) -> str:
    """Seed imports -> Tengoku.*; corpus imports -> this library's Deps modules.
    A corpus module the tree does not reproduce is replaced by what IT imported
    (recursively), so a module keeps the seed-library surface its file had —
    the standalone script compiled with the whole tree in scope; the module
    must not silently lose `Mathlib.ModelTheory` because it arrived through a
    corpus import."""
    roots = [(v[1], v[2]) for v in PACKAGES.values()]
    seen = _seen if _seen is not None else set()

    def sub(m):
        mod = m.group(2)
        if mod == corpus_prefix or mod.startswith(corpus_prefix + "."):
            leaf = mod.split(".")[-1]
            if leaf in deps_available:
                return f"{m.group(1)}Tengoku.{lib_ns}.Deps.{leaf}{m.group(3)}"
            if corpus is not None and mod not in seen:
                seen.add(mod)
                f = corpus / Path(*mod.split(".")).with_suffix(".lean")
                if f.exists():
                    inner = map_imports(f.read_text(encoding="utf-8"), corpus_prefix, lib_ns, deps_available, corpus, seen)
                    return "\n".join(l.strip() for l in inner.splitlines() if re.match(r"\s*(public |private |meta )*import ", l))
            return ""  # a corpus module we don't reproduce and cannot read: nothing to import
        for root_mod, mapped in roots:
            new = module_map(root_mod, mapped, mod)
            if new:
                return f"{m.group(1)}{new}{m.group(3)}"
        return m.group(0)

    return IMPORT_RE.sub(sub, text)


DECL_NAME_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*(?:def|theorem|lemma|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([A-Za-z_][\w'.]*)",
    re.M,
)
IMPORT_LINE_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s")


NOTATION_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:scoped\s+|local\s+)?(?:infixl?|infixr|prefix|postfix|notation)\b[^\"]*\"([^\"]+)\"")


def deps_declared(deps_dir: Path) -> tuple[set[str], set[str]]:
    """Names and (whitespace-normalised) lines every Deps module already
    provides. A notation counts by its token: `" ◇ "` declared by Deps/Magma
    is the same notation however a script spells the declaration, and a
    second copy makes every `x ◇ y` ambiguous."""
    names, lines = set(), set()
    for f in deps_dir.glob("*.lean"):
        text = f.read_text(encoding="utf-8")
        names.update(n.removeprefix("_root_.") for n in DECL_NAME_RE.findall(text))
        for l in text.splitlines():
            if l.strip() and not l.lstrip().startswith("--"):
                lines.add(" ".join(l.split()))
                m = NOTATION_RE.match(l)
                if m:
                    names.add("notation:" + m.group(1).strip())
    return names, lines


def top_level_chunks(text: str) -> list[list[str]]:
    """Split a file prefix at column-0 lines; attribute/doc-comment lead-ins and
    the inside of block comments stay with the declaration they belong to."""
    out: list[list[str]] = []
    cur: list[str] = []
    depth = 0

    def lead_in_only(lines: list[str]) -> bool:
        # attributes, doc comments, and `set_option … in` / `omit … in` /
        # `open … in` modifiers all belong to the declaration that follows
        return all(
            not l.strip() or l.startswith(("@[", "/--", "/-", "--")) or l.strip().endswith("-/") or l.rstrip().endswith(" in")
            for l in lines
        )

    for line in text.splitlines():
        if line and not line[0].isspace() and depth == 0 and cur and not lead_in_only(cur):
            out.append(cur)
            cur = []
        cur.append(line)
        depth += line.count("/-") - line.count("-/")
    if cur:
        out.append(cur)
    return out


def dedupe_prefix(prefix: str, deps_names: set[str], deps_lines: set[str]) -> str:
    """A context written by an agent (no prelude marker) is a self-contained
    script: `import Mathlib`, its own `class Magma`, `abbrev EquationN`, the
    `◇` notation. Inside the tree those come from the library's Deps modules,
    so imports go and any top-level declaration Deps already provides is
    dropped — an `import` after line 1 or a second `class Magma` in the same
    namespace fails the build. Universe declarations are per-file and kept."""
    kept = []
    for chunk in top_level_chunks(prefix):
        body = "\n".join(chunk)
        code = [l for l in chunk if l.strip() and not l.lstrip().startswith(("--", "/-", "@[")) and not l.strip().endswith("-/")]
        if not code:
            continue
        if any(IMPORT_LINE_RE.match(l) for l in code):
            continue
        if code[0].startswith("universe"):
            kept.append(body)
            continue
        m = DECL_NAME_RE.search(body)
        if m and m.group(1).removeprefix("_root_.") in deps_names:
            continue
        n = NOTATION_RE.match(code[0])
        if n and ("notation:" + n.group(1).strip()) in deps_names:
            continue
        kept.append(body)
    return "\n".join(kept)


def regenerate_equations(corpus: Path, corpus_prefix: str) -> list[str]:
    out = []
    for f in sorted((corpus / corpus_prefix / "Equations").glob("*.lean")):
        for m in EQUATION_LINE_RE.finditer(f.read_text(encoding="utf-8")):
            law = m.group(2)
            vars_ = []
            for t in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", law):
                if t.group(0) not in vars_:
                    vars_.append(t.group(0))
            out.append(f"abbrev Equation{m.group(1)} (G : Type uEq) [Magma G] : Prop := ∀ {' '.join(vars_)} : G, {law}")
    return out


def data_files(out: Path, tier: str, library: str) -> list[Path]:
    """data/<tier>/<library>.jsonl plus data/<tier>/<library>/*.jsonl — contributors add one file per PR so appends never conflict."""
    flat = out / "data" / tier / f"{library}.jsonl"
    nested = sorted((out / "data" / tier / library).glob("*.jsonl")) if (out / "data" / tier / library).is_dir() else []
    return ([flat] if flat.exists() else []) + nested


def tombstoned_names(out: Path, library: str) -> list[str]:
    """Names retracted by tombstone lines in the library's trusted files."""
    names = []
    for p in data_files(out, "trusted", library):
        for line in p.read_text(encoding="utf-8").splitlines():
            if line.strip():
                r = json.loads(line)
                if "tombstone" in r:
                    names.append(str(r["tombstone"]))
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="checkout of the corpus (dir containing e.g. equational_theories/)")
    ap.add_argument("--libraries", nargs="*", default=["equational-theories"])
    ap.add_argument("--out", default=".")
    ap.add_argument("--only", default=None, help="regenerate just this source_path's module (Deps and the aggregator are still refreshed)")
    ap.add_argument(
        "--candidate",
        default=None,
        help="generate this source_path's module from its trusted AND staging records into a `_candidate_` sibling file (the real module and aggregator are untouched); promote.py builds it before trusting the records",
    )
    ap.add_argument(
        "--candidate-names",
        default="",
        help="with --candidate: only these staging records (comma-separated names) join the trusted ones; the merge queue passes the group's own records so an older broken staging record of the same file cannot fail someone else's PR",
    )
    args = ap.parse_args()
    if args.candidate:
        args.only = args.candidate
    out = Path(args.out).resolve()
    corpus = Path(args.corpus).expanduser().resolve()

    for library in args.libraries:
        lib_ns = pascal(library)
        corpus_prefix = library.replace("-", "_")  # equational-theories -> equational_theories
        records = []
        # A tombstone line {"tombstone": "<name>", ...} in a trusted file retracts every record of that name
        # (history stays in the file). The campaign found the schema accepted tombstones that changed nothing.
        retracted = set(tombstoned_names(out, library))
        for tier in DATA_TIERS:
            for p in data_files(out, tier, library):
                for line in p.read_text(encoding="utf-8").splitlines():
                    if line.strip():
                        r = json.loads(line)
                        if "tombstone" in r or r.get("name") in retracted:
                            continue
                        if r.get("source_path") and r.get("context") is not None:
                            records.append(r)
        if args.candidate:
            only_names = set(args.candidate_names.split(",")) if args.candidate_names else None
            for p in data_files(out, "staging", library):
                for line in p.read_text(encoding="utf-8").splitlines():
                    if line.strip():
                        r = json.loads(line)
                        if "tombstone" in r or r.get("name") in retracted:
                            continue
                        if r.get("source_path") == args.candidate and r.get("context") is not None:
                            if only_names is None or r.get("name") in only_names:
                                records.append(r)
        if not records:
            print(f"{library}: no trusted records with source_path/context — modules on disk are removed, Deps kept")

        lib_dir = out / "Tengoku" / lib_ns
        deps_dir = lib_dir / "Deps"
        deps_dir.mkdir(parents=True, exist_ok=True)
        external = seed_heads(out)

        # ---- Deps: the corpus modules any context pasted verbatim, plus all equations
        pasted = set()
        for r in records:
            pasted.update(PRELUDE_MODULE_RE.findall(r["context"]))
        deps_available = {m.split(".")[-1] for m in pasted}
        for mod in sorted(pasted):
            src = corpus / Path(*mod.split(".")).with_suffix(".lean")
            text = src.read_text(encoding="utf-8")
            if UNSAFE_MODULE_RE.search(text):
                print(f"  skip {mod}: needs load-time initialisation")
                continue
            body = strip_corpus_attrs(map_imports(text, corpus_prefix, lib_ns, deps_available, corpus))
            imports = "\n".join(l for l in body.splitlines() if re.match(r"\s*(public |private |meta )*import ", l))
            rest = "\n".join(l for l in body.splitlines() if not re.match(r"\s*(public |private |meta )*import ", l))
            leaf = mod.split(".")[-1]
            (deps_dir / f"{leaf}.lean").write_text(
                f"-- {lib_ns}/Deps/{leaf}: verbatim from {mod} (imports mapped, corpus bookkeeping attributes stripped)\n"
                f"{imports}\nimport Tengoku.Init\n\nset_option linter.all false\n\n{wrap(rest, lib_ns, external)}",
                encoding="utf-8",
            )
        eqs = regenerate_equations(corpus, corpus_prefix)
        if eqs and (deps_dir / "Magma.lean").exists():  # the abbrevs need Magma; without it the file would not build
            (deps_dir / "Equations.lean").write_text(
                f"-- {lib_ns}/Deps/Equations: every `equation N := law` of the corpus, in the exact shape its `equation` command produces\n"
                f"import Tengoku.{lib_ns}.Deps.Magma\n\nset_option linter.all false\n\n"
                + wrap("universe uEq\n\n" + "\n".join(eqs), lib_ns, external),
                encoding="utf-8",
            )
        deps_mods = sorted(p.stem for p in deps_dir.glob("*.lean"))
        (lib_dir / "Deps.lean").write_text("\n".join(f"import Tengoku.{lib_ns}.Deps.{m}" for m in deps_mods) + "\n", encoding="utf-8")
        deps_names, deps_lines = deps_declared(deps_dir)

        # ---- One module per original source file
        by_file: dict[str, list[dict]] = {}
        for r in records:
            by_file.setdefault(r["source_path"], []).append(r)
        warnings = 0
        for source_path, recs in sorted(by_file.items()):
            if args.only and source_path != args.only:
                continue
            rel = Path(source_path)
            if rel.parts and rel.parts[0] == corpus_prefix:
                rel = Path(*rel.parts[1:])
            mod_path = lib_dir / rel
            mod_name = f"Tengoku.{lib_ns}." + ".".join(rel.with_suffix("").parts)
            if args.candidate:
                mod_path = mod_path.with_name("_candidate_" + mod_path.name)
                head, leaf = mod_name.rsplit(".", 1)
                mod_name = f"{head}._candidate_{leaf}"

            def line_of(r):
                m = re.search(r"#L(\d+)", r.get("source_url") or "")
                return int(m.group(1)) if m else 0

            recs.sort(key=line_of)

            # The file's own declarations: everything after the prelude marker in
            # a record's context (a marker-bearing record is preferred: its prefix
            # is the original file's, not an agent's self-contained rewrite).
            # Contexts that differ (an agent's fix) are noted; the build decides.
            def own_prefix(r):
                mm = FILE_MARKER_RE.search(r["context"])
                text = r["context"][mm.end() :] if mm else r["context"]
                text = "\n".join(l for l in text.splitlines() if not l.startswith("set_option linter.all false"))
                return dedupe_prefix(text, deps_names, deps_lines)

            # Walk the records in file order; before each theorem emit whatever
            # its context declares that the module does not have yet (a
            # definition sitting between two theorems is in the later one's
            # context, not the earlier one's), then the theorem itself. A
            # declaration is identified by its name, a structural line
            # (namespace/section/end/open/variable/…) by its text.
            emitted: set[str] = set()
            parts: list[str] = []

            def emit(text: str) -> None:
                text = text.strip()
                if not text:
                    return
                if text.rstrip().endswith(" in"):  # a modifier for the next declaration: never deduplicated
                    parts.append(text)
                    return
                m = DECL_NAME_RE.search(text)
                key = ("name:" + m.group(1).removeprefix("_root_.")) if m else ("text:" + " ".join(text.split()))
                if key in emitted:
                    return
                emitted.add(key)
                parts.append(text)

            for r in recs:
                for chunk in top_level_chunks(own_prefix(r)):
                    emit("\n".join(chunk))
                emit(f"{strip_corpus_attrs(r['statement'])}\n{strip_trailing_ends(r['proof'])}")
            body = "\n\n".join(parts)
            # Import what the ORIGINAL file imported, mapped into the tree —
            # not the whole tree: builds stay proportional to the file, and a
            # module is testable against a partial build.
            orig = corpus / source_path
            orig_imports = []
            if orig.exists():
                mapped = map_imports(orig.read_text(encoding="utf-8"), corpus_prefix, lib_ns, deps_available, corpus)
                orig_imports = [l.strip() for l in mapped.splitlines() if re.match(r"\s*(public |private |meta )*import ", l)]
                orig_imports = [re.sub(r"^(public |private |meta )+", "", l) for l in orig_imports]
            # The Deps this file's records pasted (plus Magma/Equations, which
            # every equation abbrev needs) — not the Deps aggregator, so a corpus
            # module first pasted by some OTHER file does not rebuild this one.
            needed = {m.split(".")[-1] for r in recs for m in PRELUDE_MODULE_RE.findall(r["context"])} & deps_available
            needed |= {d for d in ("Magma", "Equations") if d in deps_mods}
            dep_imports = [f"import Tengoku.{lib_ns}.Deps.{d}" for d in sorted(needed)]
            # A mechanical record is the original text, which compiled with its
            # file's own imports. An agent-written one (no prelude marker) was
            # verified with the whole tree in scope and may lean on any seeded
            # lemma, so such a file imports the seeded root as well.
            if any(not FILE_MARKER_RE.search(r["context"]) for r in recs):
                orig_imports = ["import Tengoku"] + orig_imports
            imports = "\n".join(dict.fromkeys(orig_imports + dep_imports))
            closers = unclosed_scopes(body)
            if closers:
                body += "\n\n" + "\n".join(closers)
            mod_path.parent.mkdir(parents=True, exist_ok=True)
            mod_path.write_text(
                f"-- {mod_name}: verified translations of {source_path} ({len(recs)} theorem{'s' if len(recs) != 1 else ''})\n"
                f"{imports}\n\nset_option linter.all false\n\n{wrap(body, lib_ns, external - deps_names)}",
                encoding="utf-8",
            )

        # A module on disk that no trusted record backs any more is removed —
        # a file whose records went back to staging must not stay importable.
        def mod_path_of(source_path: str) -> Path:
            rel = Path(source_path)
            if rel.parts and rel.parts[0] == corpus_prefix:
                rel = Path(*rel.parts[1:])
            return lib_dir / rel

        backed = {mod_path_of(sp) for sp in by_file}
        stale = (
            []
            if args.candidate
            else [mod_path_of(args.only)]
            if args.only
            else [
                p
                for p in lib_dir.rglob("*.lean")
                if "Deps" not in p.relative_to(lib_dir).parts and p.name != "Deps.lean" and not p.name.startswith("_candidate_")
            ]
        )
        for p in stale:
            if p not in backed and p.exists():
                p.unlink()
                print(f"  removed {p.relative_to(out)}: no trusted record backs it")
        # The aggregator lists every file module on disk (not just this run's),
        # so a `--only` regeneration keeps the whole library importable.
        modules = sorted(
            f"Tengoku.{lib_ns}." + ".".join(p.relative_to(lib_dir).with_suffix("").parts)
            for p in lib_dir.rglob("*.lean")
            if "Deps" not in p.relative_to(lib_dir).parts and p.name != "Deps.lean" and not p.name.startswith("_candidate_")
        )
        (out / "Tengoku" / f"{lib_ns}.lean").write_text(
            f"import Tengoku.{lib_ns}.Deps\n" + "\n".join(f"import {m}" for m in modules) + "\n", encoding="utf-8"
        )
        print(
            f"{library}: {len(records)} records -> {len(modules)} file modules on disk, {len(deps_mods)} Deps modules ({len(eqs)} equations); {warnings} context notes"
        )

    # Tengoku/All.lean: everything, for tools that index or import "the whole
    # tree" (loogle, the verifier's injected import). A legacy-style file can
    # import both the module-system root and the legacy translation modules;
    # the root itself cannot.
    libs = sorted(
        p.stem
        for p in (out / "Tengoku").glob("*.lean")
        if p.stem not in {"All", "Init", "Tactic", "Std", "Widgets"}
        and (out / "Tengoku" / p.stem).is_dir()
        and (out / "Tengoku" / p.stem / "Deps.lean").exists()
    )
    (out / "Tengoku" / "All.lean").write_text(
        "-- Everything in the tree: the seeded root plus every library of verified additions.\nimport Tengoku\n"
        + "\n".join(f"import Tengoku.{l}" for l in libs)
        + "\n",
        encoding="utf-8",
    )
    print(f"Tengoku/All.lean: root + {', '.join(libs) or 'no additions yet'}")


if __name__ == "__main__":
    main()
