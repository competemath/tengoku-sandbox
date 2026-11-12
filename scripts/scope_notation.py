#!/usr/bin/env python3
"""scope_notation.py — a generated library must not leak notation, macros, elaborators or syntax into everybody else's files.

A GLOBAL `notation`, `infix`, `macro`, `elab` or `syntax` command of one library is a second reading of a symbol, or a reserved word, in every file of the tree that imports it
(2026-10-17: lean-pool's `prefix:80 "-"` made `-(3 * x)` "Ambiguous term" on a real number on Leak IV; equational-theories' `elab "resolve"` still makes `resolve` unusable as a name).
The generator (scripts/generate.py) calls `scope_library` on the modules it has written: every such command becomes `scoped` inside a namespace and `local` at the root, and a
`open scoped N` goes after the `end` that leaves N when code after it still uses the command. A command that cannot be scoped without changing what a module of the library
means (it is used outside the namespace, or after the scope ended in another file) is NOT left global quietly: `scope_library` reports it and the generator stops.

The same rules, for bundles that arrive from the factory, are in emissary's scripts/bump/scope_rewrite.py; the tests here pin the shared behaviour.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

NOTATION_KW = re.compile(
    r"^(?P<pre>[ \t]*(?:(?:open|set_option|variable|omit|include)\b[^\n]*?[ \t]in[ \t]+)*"  # `open Nat in notation …` on one line: `open Nat in scoped notation …` is the same command
    r"(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*)(?P<mod>(?:local|scoped)[ \t]+)?"
    r"(?P<kw>prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab)(?![\w'.])"
)
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")  # a character literal: `'"'` does not open a string
NAMESPACE = re.compile(r"^\s*(?:(?:public|noncomputable)\s+)*namespace\s+(\S+)\s*$")
OPENER = re.compile(r"^\s*(?:namespace\s+\S+|(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*section\b.*|mutual\s*)$")
CLOSER = re.compile(r"^\s*end\b")
STRING_ATOM = re.compile(r'"((?:[^"\\]|\\.)*)"')
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(\S+)")


def mask(text: str, keep_strings: bool = False) -> str:
    """the text with every comment (line, nested block, doc) blanked to spaces, and with `keep_strings=False` every string literal, character literal and escaped name too: same length and
    columns, so a word found in the mask is code. With `keep_strings`, the literals stay (a notation is used inside strings of `macro_rules` quotations too, and a use is a use)."""
    out, i, n = [], 0, len(text)

    def blank(seg: str) -> str:
        return seg if keep_strings else "".join("\n" if ch == "\n" else " " for ch in seg)

    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif c == '"' or c == "«":
            close = '"' if c == '"' else "»"
            j = i + 1
            while j < n and text[j] != close:
                j += 2 if (c == '"' and text[j] == "\\") else 1
            j = min(j + 1, n)
            out.append(blank(text[i:j]))
            i = j
        elif c == "'" and not (i and (text[i - 1].isalnum() or text[i - 1] in "_'!?.")) and (m := CHAR.match(text, i)):
            out.append(blank(m.group()))  # `'"'` is a character, not the start of a string that would blank the rest of the file
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


def code_end(text: str) -> int:
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


def namespaces(code: list[str]) -> tuple[list[str], list[int]]:
    """per line (0-based), the namespace in effect BEFORE the line and the number of blocks (namespace / section / mutual) open before it"""
    stack: list[str] = []  # the namespace each open block adds ('' for a section)
    ns_before, depth_before = [], []
    for ln in code:
        ns_before.append(".".join(c for c in stack if c))
        depth_before.append(len(stack))
        if m := NAMESPACE.match(ln):
            stack.append(m.group(1))
        elif OPENER.match(ln):
            stack.append("")
        elif CLOSER.match(ln) and stack:
            stack.pop()
    return ns_before, depth_before


def inside(ns_here: str, ns: str) -> bool:
    return ns_here == ns or ns_here.startswith(ns + ".")


def first_atom(lines: list[str]) -> str:
    """the first string atom of a command (up to its first `=>`): the token that makes its syntax recognised"""
    atoms = [a.strip() for a in STRING_ATOM.findall(" ".join(lines).split("=>")[0]) if a.strip()]
    return atoms[0] if atoms else ""


def command_lines(text: list[str], i: int) -> list[str]:
    j = i + 1
    while j < min(len(text), i + 12) and text[j].strip() and text[j][:1] in " \t" and "=>" not in text[j - 1]:
        j += 1
    return text[i:j]


def uses(code: list[str], atom: str) -> list[int]:
    """lines (0-based) of the masked code that use `atom`: a word as a whole word, a symbol as it stands.
    The code is masked (strings blanked), so the atom is looked for in the raw line with comments only removed."""
    if not atom:
        return []
    if re.fullmatch(r"[^\W\d][\w']*", atom):
        pat = re.compile(rf"(?<![\w'.!?]){re.escape(atom)}(?![\w'!?])")
    else:
        pat = re.compile(re.escape(atom))
    return [k for k, ln in enumerate(code) if pat.search(ln)]


def code_without_comments(text: str) -> list[str]:
    """like mask, but string literals stay: a notation is used inside `‹ … ›`-less terms and in strings of `macro_rules` quotations alike, and a use is a use"""
    return mask(text, keep_strings=True).split("\n")


class Found:
    """one global command: where, what scope it can get, and what makes that unsafe"""

    def __init__(self, path: Path, line: int, kw_col: int, ns: str, atom: str, scope_end: int | None):
        self.path, self.line, self.kw_col, self.ns, self.atom, self.scope_end = path, line, kw_col, ns, atom, scope_end
        self.problem = ""

    @property
    def mode(self) -> str:
        return "scoped" if self.ns else "local"

    def label(self, root: Path) -> str:
        return f"{self.path.relative_to(root)}:{self.line + 1} {self.mode} `{self.atom}`"


def find_commands(path: Path, text: str) -> tuple[list[Found], list[str], list[str], list[int]]:
    raw = text.split("\n")
    code = mask(text).split("\n")
    plain = code_without_comments(text)
    ns_before, depth_before = namespaces(code)
    found = []
    for i, ln in enumerate(code):
        m = NOTATION_KW.match(ln)
        if not m or m.group("mod"):
            continue
        ns = ns_before[i]
        # where the scope ends: the first later line that is outside the namespace (scoped) / outside the innermost block (local, i.e. root level)
        end = None
        for k in range(i + 1, len(code)):
            if (ns and not inside(ns_before[k], ns)) or (not ns and depth_before[k] < depth_before[i]):
                end = k
                break
        found.append(Found(path, i, m.start("kw"), ns, first_atom(command_lines(raw, i)), end))
    return found, raw, code, plain, ns_before


def scope_library(lib_dir: Path, lib_ns: str, external: set[str] = frozenset(), write: bool = True) -> dict:
    """Make every global notation / macro / elab / syntax command of the `.lean` modules under `lib_dir` scoped (in a namespace) or local (at the root).

    Returns {"scoped": [labels], "reopened": [labels], "unscopable": [(label, why)]}. A command whose scope would end before a use (in its own file after the `end`,
    or in a module that imports its module without being inside the namespace) is left global and listed under "unscopable": the caller stops on it.
    `external` are the heads of namespaces the seeded tree (Mathlib, core) owns: an `open scoped` of one would also switch its scoped entries on, so it is not written."""
    root = lib_dir.parent.parent  # <out>/Tengoku/<Lib> -> <out>
    files = sorted(lib_dir.rglob("*.lean"))
    info: dict[Path, tuple] = {}
    mod_of: dict[str, Path] = {}
    for f in files:
        text = f.read_text(encoding="utf-8")
        info[f] = find_commands(f, text)
        mod_of[f"Tengoku.{lib_ns}." + ".".join(f.relative_to(lib_dir).with_suffix("").parts)] = f
    imports: dict[Path, set[Path]] = {f: set() for f in files}
    for f, (_, raw, *_rest) in info.items():
        for ln in raw:
            if (m := IMPORT.match(ln)) and m.group(1) in mod_of:
                imports[f].add(mod_of[m.group(1)])

    rev: dict[Path, set[Path]] = {f: set() for f in files}  # f -> the modules that import f directly
    for g, deps in imports.items():
        for f in deps:
            rev[f].add(g)

    def importers_of(f: Path) -> set[Path]:
        """every module of the library that imports `f`, directly or not"""
        seen: set[Path] = set()
        stack = [f]
        while stack:
            for g in rev[stack.pop()]:
                if g not in seen:
                    seen.add(g)
                    stack.append(g)
        return seen

    report: dict = {"scoped": [], "reopened": [], "unscopable": []}
    edits: dict[Path, list[tuple[int, int, str]]] = {}  # file -> (line, column, text to insert)
    after: dict[Path, dict[int, list[str]]] = {}  # file -> line after which a line is inserted -> lines
    for f, (cmds, raw, code, plain, ns_before) in info.items():
        for c in cmds:
            why = ""
            if not c.atom:
                why = "no string atom to look for"
            if not why and c.scope_end is not None:
                # its own file, after the scope ended: a use there needs the command again
                later = [k for k in uses(plain, c.atom) if k >= c.scope_end and not (c.ns and inside(ns_before[k], c.ns))]
                if later and not c.ns:
                    why = f"used after its block ends (line {later[0] + 1}) at the root"
                elif later:
                    head = c.ns.split(".")[0]
                    if head in external:
                        why = f"used after its namespace `{c.ns}` ends (line {later[0] + 1}), and `open scoped {c.ns}` would switch on entries of the seeded tree"
                    else:
                        after.setdefault(f, {}).setdefault(c.scope_end - 1, [])
                        line = f"open scoped {c.ns}"
                        if line not in after[f][c.scope_end - 1]:
                            after[f][c.scope_end - 1].append(line)
                        report["reopened"].append(c.label(root))
            if not why:
                for g in sorted(importers_of(f)):
                    _, raw_g, _, plain_g, ns_g = info[g]
                    bad = [k for k in uses(plain_g, c.atom) if not (c.ns and inside(ns_g[k], c.ns))]
                    if not bad:
                        continue
                    if not c.ns:
                        why = f"used in {g.relative_to(lib_dir)} line {bad[0] + 1}, and a root-level command cannot be switched on in another file"
                    elif c.ns.split(".")[0] in external:
                        why = f"used in {g.relative_to(lib_dir)} line {bad[0] + 1}, outside `{c.ns}`, and `open scoped {c.ns}` would switch on entries of the seeded tree"
                    else:
                        # the importer opens the namespace's scoped entries right after its imports
                        last_import = max((k for k, ln in enumerate(raw_g) if IMPORT.match(ln)), default=-1)
                        line = f"open scoped {c.ns}"
                        slot = after.setdefault(g, {}).setdefault(last_import, [])
                        if line not in slot and not any(raw_g[k].strip() == line for k in range(len(raw_g))):
                            slot.append(line)
                        report["reopened"].append(f"{g.relative_to(root)} (imports {f.relative_to(lib_dir)}): open scoped {c.ns}")
            if why:
                c.problem = why
                report["unscopable"].append((c.label(root), why))
            else:
                edits.setdefault(f, []).append((c.line, c.kw_col, c.mode + " "))
                report["scoped"].append(c.label(root))
    new_text: dict[Path, str] = {}
    for f in files:
        lines = info[f][1][:]
        for line, col, word in edits.get(f, []):
            lines[line] = lines[line][:col] + word + lines[line][col:]
        for k, extra in sorted(after.get(f, {}).items(), reverse=True):
            lines[k + 1 : k + 1] = extra
        new_text[f] = "\n".join(lines)
    # Whatever this pass did not read is checked the way the gate checks it (scripts/ci/allowlist.py `unscoped_violations`: every occurrence of the keyword, not the start of a line):
    # a command in the middle of a line, or one that no reading above found, is global still, and the generator stops on it instead of writing it
    reported = {
        c.path for cmds, *_ in info.values() for c in cmds if c.problem
    }  # those commands are left global on purpose and already named
    for f, why in residual({f: t for f, t in new_text.items() if f not in reported}):
        report["unscopable"].append((f"{f.relative_to(root)}", why))
    if write:
        for f in files:  # the paths the walk of `lib_dir` found, never a key of what was read
            if f in edits or f in after:
                with open(f, "w", encoding="utf-8") as out_file:
                    out_file.write(new_text[f])
    return report


def residual(texts: dict[Path, str]) -> list[tuple[Path, str]]:
    """(module, why) for every module of `texts` that still has a notation, macro, syntax or elab command that is neither `scoped` nor `local`"""
    sys.path.insert(0, str(Path(__file__).resolve().parent / "ci"))
    import allowlist

    return [
        (f, "a global command is left that this pass does not read: " + v)
        for f, text in texts.items()
        for v in allowlist.unscoped_violations(text, macro=True)
    ]
