#!/usr/bin/env python3
"""lint_banked.py <base> <head> | --text FILE — banked Lean must not run code.
Records paste `context` and `proof` verbatim into modules; modules are compiled
by CI and imported by every Leak service, where `initialize` runs. A staging or
trusted record (the tiers the tree compiles) must pass the allow-list
(scripts/ci/allowlist.py): only known-inert commands, attributes and options.
Tentative records (never compiled) and module lines keep the list of known
dangers below. Existing records are not re-judged: only lines a PR adds."""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
from pathlib import Path

from _git import added_lines, blob, changed_files, fail, load_schema, match, pascal, removed_lines, run
from allowlist import unscoped_matches, unscoped_violations, violations
from lean_lex import code_only
from restructure_check import is_restructure

IMPORT_START = r"^\s*import\b"
# three rules, because three readings of TENGOKU_INTAKE_LINT allow them differently (docs/bundle-lint.md): notation commands in `proposed` and `wide`, the macro
# family in `wide`, the elaborator commands in no mode
NOTATION = "notation declarations"
MACRO = "syntax/macro declarations"
ELAB = "elab declarations"
NOTATION_COMMANDS = ["notation3?", "infixl?", "infixr", "prefix", "postfix"]
MACRO_COMMANDS = ["macro", "macro_rules", "syntax", "declare_syntax_cat"]
ELAB_COMMANDS = ["elab", "elab_rules"]


def declaration_rule(commands: list[str]) -> re.Pattern:
    return re.compile(r"^\s*(@\[[^\]]*\]\s*)*(scoped\s+|local\s+)?(" + "|".join(commands) + r")\b", re.M)


FORBIDDEN = [
    (re.compile(IMPORT_START, re.M), "import (the generator supplies imports)"),
    (re.compile(r"#eval\b"), "#eval"),
    (re.compile(r"#print\s+axioms"), "#print axioms (CI runs its own)"),
    (re.compile(r"\brun_cmd\b"), "run_cmd"),
    (re.compile(r"\brun_tac\b"), "run_tac"),
    (re.compile(r"\brun_elab\b"), "run_elab"),
    (re.compile(r"^\s*(builtin_)?initialize\b", re.M), "initialize (runs on import in every Leak service)"),
    (
        re.compile(r"@\[\s*(init|builtin_init|extern|implemented_by|export|never_extract)\b"),
        "@[init]/@[extern]/@[implemented_by]/@[export]",
    ),
    (re.compile(r"^\s*(unsafe|partial)\s+(def|theorem|abbrev|instance|opaque)", re.M), "unsafe/partial definitions"),
    (declaration_rule(NOTATION_COMMANDS), NOTATION),
    (declaration_rule(MACRO_COMMANDS), MACRO),
    (declaration_rule(ELAB_COMMANDS), ELAB),
    (re.compile(r"\bnative_decide\b"), "native_decide (trusts the compiler)"),
    (re.compile(r"^\s*opaque\b", re.M), "opaque"),
    (re.compile(r"^\s*axiom\b", re.M), "axiom"),
    (re.compile(r"\bIO\.(Process|FS)\b|\bSystem\.(FilePath|Platform)\b"), "IO.Process / IO.FS"),
]
SET_OPTION = re.compile(r"set_option\s+([A-Za-z_][\w.]*)")

# A PR of the scope-fix class (scripts/ci/classify.py: existing modules of intake libraries, modified in place, from the factory's account; scripts/ci/scope_fix_check.py
# judges every line of it) makes a library's global notation `scoped` or `local`: the line of the command is edited, so the PR "adds" a notation command, and an importer
# gets a `local` copy of a command that was made local. Neither is a new declaration: the text is the one the tree already has, in a narrower scope. 2026-10-17: tengoku#601
# was ejected from the queue by "notation declarations" on 64 such modules. Only in a diff of that shape, only for a line the SAME module had as code, and only for a copy of a
# command some module of the PR makes local (Gitar on tengoku#603: a comment line removed in one PR must not come back as code in the next).
# The same holds for a REGENERATION of a generated library (scripts/generate.py scopes the notation of the modules it writes, scripts/scope_notation.py): the modules of a library the
# generator rebuilds from its corpus (schemas/sources.json `corpora`), modified in place, with the same lines narrowed and nothing else.
COMMAND_WORDS = "prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab"
COMMAND = re.compile(
    rf"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*(?:(?:local|scoped)[ \t]+)?(?P<kw>{COMMAND_WORDS})(?![\w'.])"
)
NARROWED = re.compile(rf"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*)(?P<mod>local|scoped)[ \t]+(?P<cmd>(?:{COMMAND_WORDS})(?![\w'.]).*)$")


def code_end(text: str) -> int:
    """the column where the code of this line ends: before a `--` comment that is not inside a string literal"""
    inside, i = False, 0
    while i < len(text):
        c = text[i]
        if inside:
            if c == "\\":
                i += 2
                continue
            inside = c != '"'
        elif c == '"':
            inside = True
        elif text.startswith("--", i):
            return len(text[:i].rstrip())
        i += 1
    return len(text.rstrip())


def narrowable_libraries(base: str) -> set[str]:
    """the libraries whose modules a narrowing may edit in place: an intake bundle at the base (the scope-fix class) or a library the generator rebuilds from a corpus (a regeneration)"""
    intake = {
        pascal(m.group(1))
        for p in run("ls-tree", "-r", "--name-only", base, "data/intake", check=False).split(
            "\n"
        )  # a base that is no revision (the fuzzers') has no intake libraries: no exemption
        if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
    }
    return intake | {pascal(lib) for lib in load_schema("sources.json").get("corpora", {})}


def scope_fix_shape(base: str, files: list[tuple[str, str]]) -> bool:
    """the diff is what classify.py calls a scope-fix PR, or a regeneration of the same kind: existing modules `Tengoku/<Library>/….lean` of a library that arrived as an intake bundle
    or that the generator rebuilds from its corpus, modified in place, nothing else"""
    libraries = narrowable_libraries(base)
    return bool(files) and all(
        st == "M" and (m := re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", p)) and m.group(1) in libraries for st, p in files
    )


class Narrowing:
    """The added lines of a scope-fix diff that declare nothing new: a line that is a line the same module had (as code, not inside a comment or a string) with `scoped` or `local`
    put in front of its command, or `local <command>` for a command that some module of the PR makes local (what an importer declares again)."""

    def __init__(self, base: str, head: str, files: list[tuple[str, str]]):
        self.removed: dict[str, set[str]] = {}
        self.local: set[str] = set()
        if not scope_fix_shape(base, files):
            return
        for _, p in files:
            self.removed[p] = self.removed_code(base, head, p)
        for p, lines in self.removed.items():
            for _, text in added_lines(base, head, p):
                m = NARROWED.match(text)
                if m and m.group("mod") == "local" and self.old(text, m) in lines:
                    self.local.add(text[m.start("cmd") : code_end(text)].strip())

    @staticmethod
    def removed_code(base: str, head: str, p: str) -> set[str]:
        raw = blob(base, p)
        if raw is None:
            return set()
        text = raw.decode("utf-8", "replace")
        code = code_only(text).split("\n")
        if len(code) != len(text.split("\n")):  # the lexer keeps every line break; if it ever did not, nothing is trusted
            return set()
        return {t.strip() for no, t in removed_lines(base, head, p) if no - 1 < len(code) and COMMAND.match(code[no - 1])}

    @staticmethod
    def old(line: str, m: re.Match) -> str:
        return (line[: m.start("mod")] + line[m.start("cmd") :]).strip()

    def hides(self, p: str, line: str) -> bool:
        m = NARROWED.match(line)
        if not m or p not in self.removed:
            return False
        if self.old(line, m) in self.removed[p]:
            return True
        return m.group("mod") == "local" and not m.group("pre").strip() and line[m.start("cmd") : code_end(line)].strip() in self.local


def intake_modules(base: str, head: str) -> tuple[str, ...]:
    """The module paths of an intake bundle in this diff, when the repository's intake lint is `proposed` or `wide` (variable TENGOKU_INTAKE_LINT):
    notation commands are allowed there, as in scripts/ci/intake_check.py (the allow-list lint of the bundle). Nowhere else."""
    if os.environ.get("TENGOKU_INTAKE_LINT") not in ("proposed", "wide"):
        return ()
    libs = {m.group(1) for _, p in changed_files(base, head) if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}
    return tuple(x for lib in libs for x in (f"Tengoku/{pascal(lib)}/", f"Tengoku/{pascal(lib)}.lean"))


def in_intake(p: str, intake: tuple[str, ...]) -> bool:
    """Is `p` one of the bundle's own modules: its root file exactly, or a file under its directory (never a sibling that merely starts the same)."""
    return p in intake or any(x.endswith("/") and p.startswith(x) for x in intake)


def check_text(
    label: str, text: str, allowed: set[str], notation_ok: bool = False, macro_ok: bool = False, module: bool = False
) -> list[str]:
    out = []
    for re_, why in FORBIDDEN:
        if (why == NOTATION and notation_ok) or (why == MACRO and macro_ok):
            continue
        if re_.search(text):
            out.append(f"{label}: {why}")
    for opt in SET_OPTION.findall(text):
        if opt not in allowed:
            out.append(f"{label}: set_option {opt} is not on the allowlist")
    return out


RECORD_FILES = [
    "data/tentative/*.jsonl",
    "data/staging/*.jsonl",
    "data/trusted/*.jsonl",
    "data/tentative/*/*.jsonl",
    "data/staging/*/*.jsonl",
]


def lint_record_file(base: str, head: str, p: str, allowed: set[str]) -> list[str]:
    """The lines a PR adds to a records file, judged by the allow-list (compiled tiers) or the list of known dangers."""
    errors = []
    for no, text in added_lines(base, head, p):
        try:
            r = json.loads(text)
        except Exception:
            continue
        if not isinstance(r, dict) or "tombstone" in r:  # not an object: validate_records.py refuses it
            continue
        body = "\n".join(str(r.get(k, "")) for k in ("context", "statement", "proof"))
        label = f"{p}:{no} ({r.get('name')})"
        if p.startswith(("data/staging/", "data/trusted/")):  # compiled: only what is known to be inert
            errors += [f"{label}: {v}" for v in violations(body, allowed)]
        else:
            errors += check_text(label, body, allowed)
    return errors


def lint_module(
    base: str,
    head: str,
    p: str,
    allowed: set[str],
    notation_ok: bool,
    added: bool = False,
    macro_ok: bool = False,
    narrowing: Narrowing | None = None,
) -> list[str]:
    """The lines a PR adds to a module. `import` lines in a module are the generator's own (a promotion regenerates them); records may not contain one.
    A module the PR adds is read whole and without its comments and string literals (lean_lex.code_only): the words this list refuses are
    refused where they run, not where a docstring mentions them (`#print axioms` in a doc comment is prose). A module the PR changes is read whole
    the same way, and only the lines it adds are judged: a line alone cannot tell code from the middle of a comment, the whole file can."""
    raw = blob(head, p) if added else None
    if added and raw is None:  # fail closed: the line-by-line path below cannot see a block comment that an `import X -/` line closes
        return [f"{p}: could not read the module at {head}"]
    if raw is not None:
        # comments and strings first, THEN the import lines: a line `import X -/` inside a block comment closes it, and dropping it first would
        # turn the rest of the file into comment text (a `#eval` after it would go unread)
        code = code_only(raw.decode("utf-8", "replace"))
        body = "\n".join(ln for ln in code.split("\n") if not re.match(IMPORT_START, ln))
        # no module of the tree declares a GLOBAL notation or macro command, in any mode (the rules above read the start of a line; Lean needs no line break between commands)
        return list(
            dict.fromkeys(
                check_text(p, body, allowed, notation_ok=notation_ok, macro_ok=macro_ok)
                + [f"{p}: {v}" for v in unscoped_violations(body, macro=True)]
            )
        )
    added_here = [
        (no, t) for no, t in added_lines(base, head, p) if not (narrowing and narrowing.hides(p, t))
    ]  # the narrowed ones declare nothing the tree does not have
    raw_head = blob(head, p)
    if raw_head is not None:
        # The module is read whole and lexed like an added one, and only the lines the PR adds are judged, as code: an isnad tag moves the `-/` of a docstring to its own line, which makes the
        # docstring's last line an added line, and prose that starts with `prefix` or `notation` was refused as a notation command (isnad tag PR #438, 2026-10-11: "prefix length](hyp:Z,p,k) …").
        head_text = raw_head.decode("utf-8", "replace")
        code = code_only(head_text).split("\n")
        if len(code) == len(
            head_text.split("\n")
        ):  # the lexer keeps every line break; if it ever did not, the lines would not line up and the old reading stands
            text = "\n".join(code[no - 1] for no, _ in added_here if no - 1 < len(code) and not re.match(IMPORT_START, code[no - 1]))
            out = check_text(p, text, allowed, notation_ok=notation_ok, macro_ok=macro_ok)
            # a global command is judged against the module as it stands, and counted when it is on an added line: the `scoped` in front of it is the module's own line before it, never
            # an added line that happens to come before it in the diff (Gitar on tengoku#615: a lone `scoped` line added far above made a later `notation` look scoped)
            added_nos = {no for no, _ in added_here}
            return list(dict.fromkeys(out + [f"{p}: {v}" for no, v in unscoped_matches(head_text, macro=True) if no in added_nos]))
    text = "\n".join(t for _, t in added_here if not re.match(IMPORT_START, t))
    return list(
        dict.fromkeys(
            check_text(p, text, allowed, notation_ok=notation_ok, macro_ok=macro_ok)
            + [f"{p}: {v}" for v in unscoped_violations(text, macro=True, same_line=True)]
        )
    )


def checked_path(arg: str) -> Path:
    """A file given on the command line: it must lie in the working directory or the temporary directory."""
    p = Path(arg).resolve()
    if not any(p.is_relative_to(root.resolve()) for root in (Path.cwd(), Path(tempfile.gettempdir()))):
        fail(f"{arg} is outside the working directory and the temporary directory")
    return p


def main() -> None:
    allowed = set(load_schema("allowed-options.json")["allowed"])
    errors = []
    if sys.argv[1] == "--text":
        errors = check_text(sys.argv[2], checked_path(sys.argv[2]).read_text(), allowed)
    else:
        base, head = sys.argv[1], sys.argv[2]
        intake = intake_modules(base, head)
        moved_seed = is_restructure(
            base, head
        )  # the seed's move is recomputed by restructure_check.py; it is upstream code, never banked content
        files = changed_files(base, head)
        narrowing = Narrowing(base, head, files)
        for st, p in files:
            if moved_seed and p.startswith("Tengoku/Seed/"):
                continue
            if match(p, RECORD_FILES):
                errors += lint_record_file(base, head, p, allowed)
            elif p.endswith(".lean") and p.startswith(
                "Tengoku/"
            ):  # modules only; root tool programs (TengokuExtract/TengokuAxioms) run in CI, not in the library
                own = in_intake(p, intake)
                errors += lint_module(
                    base,
                    head,
                    p,
                    allowed,
                    notation_ok=own,
                    added=st == "A",
                    macro_ok=own and os.environ.get("TENGOKU_INTAKE_LINT") == "wide",
                    narrowing=narrowing,
                )
    if errors:
        fail("banked content lint:\n  " + "\n  ".join(errors[:20]))
    print("content lint OK")


main()
