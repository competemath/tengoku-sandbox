#!/usr/bin/env python3
"""scope_fix_check.py <base> <head> — the checks of a SCOPE-FIX PR.

A merged library cannot be edited (its modules are derived files), yet a library can register, for the whole tree, an instance or a simp lemma
that mentions nothing of its own types (`attribute [instance] Matrix.linftyOpNormedAddCommGroup`: the norm of every matrix in the tree becomes the
L-infinity operator norm; the merge queue's leak report lists them). A scope-fix PR makes such a registration `local` to the module that makes
it and gives the library's own importers the same registrations, local to each: inside the library nothing changes, outside it nothing leaks.

Only that one transformation is accepted, and it is checked line by line, not trusted:
  - every changed file is an existing module `Tengoku/<Library>/….lean` of a library that arrived as an intake bundle (data/intake/<library>/ at
    the base), modified in place; nothing else is touched (no manifest, no All.lean, no other path);
  - a line may change in exactly one way: the word `local ` inserted, in code, before `instance` or `simp` (`local instance`, `@[local simp]`,
    `attribute [local instance]`); the same number of lines before and after, in the same order;
  - lines may be added in exactly one form: `attribute [local instance] N …`, `attribute [local instance P] N …` (a priority), `attribute [local simp] N …`,
    blank lines, and the one note comment `-- Tengoku: … (generated)`; each N is a name the library itself registers (an instance it declares or
    names in an `attribute [instance]`, a simp lemma it declares or names in `attribute [simp]`) or an automatically named instance (`inst…`).
A library can also register NOTATION for the whole tree: a global `prefix:80 "-" => complement` (lean-pool, `LO.Modal.Formula`) is a second reading of every `-(3 * x)`
on a real number ("Ambiguous term"), and a global `notation "v" => …` makes `v` a reserved word in every file. The same PR may make such a command `scoped` (in a namespace)
or `local` (in the root namespace) and give the library's importers the activation:
  - a line may change by the word `scoped ` or `local ` inserted, in code, right before `prefix`, `infix`, `infixl`, `infixr`, `postfix`, `notation`, `notation3`, `syntax`,
    `macro` or `elab` that starts the command (after attributes and modifiers only); `scoped` needs a namespace around the command;
  - lines may be added: `open scoped N …` where each N is the namespace of a command made `scoped` in the same PR, `local <command>` where the command is one made `local` in the
    same PR (the same text), and the note comment `-- Tengoku: … notation(s) of this module made … (generated)`.
Nothing is declared, removed, reordered or renamed, so no theorem, statement, import or axiom changes; the merge queue builds the library.
"""

from __future__ import annotations

import difflib
import re
import sys

from _git import blob, changed_files, fail, pascal, run

NAME = r"[\w.'«»!?]+"
ATTR_LINE = re.compile(rf"attribute \[local (?:instance(?: \d+)?|simp)\]( {NAME})+")
NOTE = re.compile(r"-- Tengoku: \d+ registration\(s\) of this module made local so they do not change other libraries \(generated\)")
KEYWORD = re.compile(r"(?:instance|simp)(?![\w'.])")
INSTANCE_DECL = re.compile(
    rf"^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|public)[ \t]+)*instance\s+(?:\(priority\s*:=[^)]*\)\s*)?({NAME})",
    re.M,
)  # a global instance declaration at the start of a line (not `local instance`, not the word inside an attribute list)
SIMP_DECL = re.compile(
    rf"@\[[^\]]*(?<![\w.\-])(?<!local )(?<!scoped )simp\b[^\]]*\]\s*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev)\s+({NAME})"
)
ATTRIBUTE_CMD = re.compile(
    rf"attribute\s*\[([^\]]*)\]((?:[ \t]+{NAME})+(?:[ \t]*\n[ \t]+{NAME}(?:[ \t]+{NAME})*)*)"
)  # continuation lines are indented
IN_CODE = re.compile(r"--[^\n]*|/-|\"(?:\\.|[^\"\\])*\"")  # a line comment, the start of a block comment, a string literal


def _block_end(text: str, i: int) -> int:
    """the index just past the `-/` that closes the (nested) block comment opened at i; the end of the text if it never closes"""
    depth, j = 1, i + 2
    while j < len(text) and depth:
        if text.startswith("/-", j):
            depth, j = depth + 1, j + 2
        elif text.startswith("-/", j):
            depth, j = depth - 1, j + 2
        else:
            j += 1
    return j


def mask(text: str) -> str:
    """the text with comments and string literals blanked to spaces: same length, same columns (a word found in it is code)"""
    out, i = list(text), 0
    while m := IN_CODE.search(text, i):
        j = _block_end(text, m.start()) if m.group() == "/-" else m.end()
        for k in range(m.start(), j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def local_insertion(old: str, new: str, new_code: str | None = None) -> bool:
    """new is old with `local ` inserted once, in code, before `instance` or `simp`. `new_code`: the line of the masked WHOLE file (a block comment or a string
    may open on an earlier line); without it, the line is masked on its own"""
    k = next((i for i, (a, b) in enumerate(zip(old, new)) if a != b), min(len(old), len(new)))
    if not (new[k : k + 6] == "local " and new[k + 6 :] == old[k:]):
        return False
    code = mask(new) if new_code is None else new_code
    return code[k : k + 6] == "local " and bool(KEYWORD.match(new, k + 6))


def last(name: str) -> str:
    return name.rsplit(".", 1)[-1]


NOTE_NOTATION = re.compile(
    r"-- Tengoku: \d+ notation\(s\) of this module made (?:scoped|local|scoped or local) so they do not change other libraries \(generated\)"
)
OPEN_SCOPED = re.compile(rf"open scoped( {NAME})+")
NOTATION_KEYWORD = re.compile(r"(?:prefix|infixl|infixr|infix|postfix|notation3|notation|syntax|macro|elab)(?![\w'.])")
BEFORE_KEYWORD = re.compile(r"[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable)[ \t]+)*")
NAMESPACE = re.compile(r"^\s*(?:(?:public|noncomputable)\s+)*namespace\s+(\S+)\s*$")
OPENER = re.compile(r"^\s*(?:namespace\s+\S+|(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*section\b.*|mutual\s*)$")
CLOSER = re.compile(r"^\s*end\b")


def notation_insertion(old: str, new: str, new_code: str | None = None) -> str | None:
    """ "scoped" or "local" when new is old with that word inserted once, in code, right before the keyword of a notation / syntax / macro / elab command that starts the line
    (after attributes and modifiers only); None otherwise. `new_code`: the line of the masked WHOLE file (a block comment or a string may open on an earlier line)"""
    k = next((i for i, (a, b) in enumerate(zip(old, new)) if a != b), min(len(old), len(new)))
    code = mask(new) if new_code is None else new_code
    for word in ("scoped ", "local "):
        if new[k : k + len(word)] == word and new[k + len(word) :] == old[k:] and code[k : k + len(word)] == word:
            if NOTATION_KEYWORD.match(new, k + len(word)) and BEFORE_KEYWORD.fullmatch(code[:k]):
                return word.strip()
    return None


def namespace_at(code_lines: list[str], i: int) -> str:
    """the namespace line `i` (0-based) is in, from the `namespace` blocks that enclose it (sections add nothing); `code_lines` are masked"""
    blocks: list[list[str]] = []
    for ln in code_lines[:i]:
        if m := NAMESPACE.match(ln):
            blocks.append(m.group(1).split("."))
        elif OPENER.match(ln):
            blocks.append([])
        elif CLOSER.match(ln) and blocks:
            blocks.pop()
    return ".".join(c for blk in blocks for c in blk)


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


def allowed_edit(old: str, new: str, new_code: str | None = None) -> bool:
    return new == old or local_insertion(old, new, new_code) or notation_insertion(old, new, new_code) is not None


def pair_up(
    o: list[str], n: list[str], i1: int, i2: int, j1: int, j2: int, new_code: list[str] | None = None
) -> tuple[list[tuple[int, int]], list[int], bool]:
    """A replace block that does not have as many new lines as old ones (an edited line next to an added one, e.g. the last line of a file and the note after it): every old
    line must meet, in order, a new line that is the same or an allowed edit of it; the new lines in between and after are additions. (pairs, additions, every old line met)"""
    pairs, added, b = [], [], j1
    for a in range(i1, i2):
        while b < j2 and not allowed_edit(o[a], n[b], new_code[b] if new_code else None):
            added.append(b)
            b += 1
        if b == j2:
            return pairs, added, False
        pairs.append((a, b))
        b += 1
    return pairs, added + list(range(b, j2)), True


GREP_NAMESPACES = r"(^[[:space:]]*(public[[:space:]]+|noncomputable[[:space:]]+)*(namespace|section)([[:space:]]|$))|(^[[:space:]]*end([[:space:]]|$))|(scoped)"
SCOPED_USE = re.compile(
    r"(?:^|[\s@\[,])scoped(?:\[(?P<ns>[\w.«»']+)\])?[ \t]+(?:instance|notation3?|infix[lr]?|prefix|postfix|macro|syntax|elab|attribute|simp|irreducible_def|def|abbrev|theorem|lemma)\b"
    r"|@\[[^\]]*\bscoped\b"
)


def scoped_namespaces(rev: str, pathspec: str) -> set[str]:
    """The namespaces in which the modules under `pathspec` at `rev` declare something `scoped` (`scoped instance`, `scoped notation`, `@[scoped simp]`, `scoped[N] …`), read from
    the lines of one `git grep` (a docstring that happens to say 'scoped notation' only makes the set larger)."""
    out: set[str] = set()
    blocks: list[list[str]] = []
    current = None
    for line in run("grep", "-n", "-I", "-E", GREP_NAMESPACES, rev, "--", pathspec, check=False).splitlines():
        m = re.match(r"^[^:]*:(?P<path>[^:]+):(?P<n>\d+):(?P<text>.*)$", line)
        if not m:
            continue
        if m.group("path") != current:
            current, blocks = m.group("path"), []
        text = m.group("text")
        if nm := NAMESPACE.match(text):
            blocks.append(nm.group(1).split("."))
        elif OPENER.match(text):
            blocks.append([])
        elif CLOSER.match(text):
            if blocks:
                blocks.pop()
        elif use := SCOPED_USE.search(text):
            out.add(use.group("ns") or ".".join(c for blk in blocks for c in blk))
    return out


def namespace_errors(notes: Notes, libraries: set[str]) -> list[str]:
    """`open scoped N` turns on EVERY scoped entry of N: a namespace of core or Mathlib with scoped entries (`Real`: `π`, `Classical`: instances) would change how the
    library's statements elaborate, and so would a library's own scoped entries that the importer did not have. Both are refused."""
    if not notes.opened:
        return []
    seed = scoped_namespaces(base, "Tengoku/Seed")
    own: set[str] = set()
    for lib in sorted(libraries):
        own |= scoped_namespaces(base, f"Tengoku/{lib}")
    return [
        f"`{ns}`: core or Mathlib declare scoped entries in this namespace, `open scoped {ns}` would turn them on"
        for ns in sorted(notes.opened & seed)
    ] + [
        f"`{ns}`: the library already has scoped entries in this namespace, `open scoped {ns}` would turn them on in the modules that import it"
        for ns in sorted((notes.opened & own) - seed)
    ]


class Notes:
    """what a PR makes of notation: the namespaces of the commands it made `scoped`, the text of the commands it made `local`"""

    def __init__(self) -> None:
        self.ns: set[str] = set()
        self.cmds: set[str] = set()
        self.opened: set[str] = set()  # the namespaces an accepted `open scoped N` line names


def collect_notes(old: str, new: str, notes: Notes) -> list[str]:
    """add the notation edits of one file to `notes`; the errors are the `scoped` ones that have no namespace around them"""
    o, n = old.split("\n"), new.split("\n")
    code, new_code = mask(old).split("\n"), mask(new).split("\n")
    errors = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, o, n, autojunk=False).get_opcodes():
        if tag != "replace":
            continue
        pairs = list(zip(range(i1, i2), range(j1, j2))) if i2 - i1 == j2 - j1 else pair_up(o, n, i1, i2, j1, j2, new_code)[0]
        for a, b in pairs:
            mode = notation_insertion(o[a], n[b], new_code[b])
            if mode == "scoped":
                ns = namespace_at(code, a)
                if ns:
                    notes.ns.add(ns)
                else:
                    errors.append(
                        f"line {b + 1}: `scoped` needs a namespace around the command (it is in the root namespace: make it `local`)"
                    )
            elif mode == "local":
                k = n[b].index("local ") + len("local ")
                notes.cmds.add(n[b][k : code_end(n[b])])
    return errors


def registered(ns: str) -> dict[str, set[str]]:
    """last components of the names the library registers for the whole tree, by kind (`instance`, `simp`), read (approximately) from its modules
    at the base"""
    out: dict[str, set[str]] = {"instance": set(), "simp": set()}
    for p in run("ls-tree", "-r", "--name-only", base, f"Tengoku/{ns}").split("\n"):
        b = blob(base, p) if p.endswith(".lean") else None
        if b is not None:
            for kind, names in registrations(mask(b.decode("utf-8", "replace"))).items():
                out[kind] |= names
    return out


GLOBAL_ATTR = re.compile(r"(instance|simp)(?![\w'.])")  # an attribute that starts with the kind: not `local …`, `scoped …` or `-simp`


def registrations(text: str) -> dict[str, set[str]]:
    """the (last components of the) names a GLOBAL instance or simp registration of this masked module text mentions, by kind: a `local` or
    `scoped` registration or a removal (`-simp`) is not one, and in a mixed list each attribute counts on its own"""
    out = {
        "instance": {last(m.group(1)) for m in INSTANCE_DECL.finditer(text)},
        "simp": {last(m.group(1)) for m in SIMP_DECL.finditer(text)},
    }
    for m in ATTRIBUTE_CMD.finditer(text):
        kinds = {g.group(1) for a in m.group(1).split(",") if (g := GLOBAL_ATTR.match(a.strip()))}
        for kind in kinds:
            out[kind] |= {last(n) for n in m.group(2).split()}
    return out


def added_line_errors(path: str, lineno: int, line: str, known: dict[str, set[str]], notes: Notes | None = None) -> list[str]:
    notes = notes or Notes()
    if not line or NOTE.fullmatch(line) or NOTE_NOTATION.fullmatch(line):
        return []
    if OPEN_SCOPED.fullmatch(line):
        notes.opened.update(ns for ns in line.split()[2:] if ns in notes.ns)
        return [
            f"{path}:{lineno}: `{ns}` is not a namespace this PR made a `scoped` notation for"
            for ns in line.split()[2:]
            if ns not in notes.ns
        ]
    if line.startswith("local ") and line[len("local ") :] in notes.cmds:
        return []
    if not ATTR_LINE.fullmatch(line):
        return [
            f"{path}:{lineno}: an added line must be `attribute [local instance|simp] names`, `open scoped N` or `local <command>` for a notation this PR made scoped or local, "
            f"a blank line or the note, not `{line[:80]}`"
        ]
    kind = "simp" if line.startswith("attribute [local simp]") else "instance"
    return [
        f"{path}:{lineno}: `{name}` is not {'an instance' if kind == 'instance' else 'a simp lemma'} this library registers (the line may only repeat its own registrations)"
        for name in line.split("]", 1)[1].split()
        if last(name) not in known[kind] and not (kind == "instance" and re.match(r"inst[A-Z_]", last(name)))
    ]


def opcode_errors(
    path: str,
    o: list[str],
    n: list[str],
    op: tuple,
    known: dict[str, set[str]],
    notes: Notes | None = None,
    new_code: list[str] | None = None,
) -> list[str]:
    """the problems with one edit of a file (an `equal` stretch has none)"""
    tag, i1, i2, j1, j2 = op
    if tag == "equal":
        return []
    if tag == "insert":
        return [e for k in range(j1, j2) for e in added_line_errors(path, k + 1, n[k], known, notes)]
    if tag == "replace" and i2 - i1 == j2 - j1:
        return [
            f"{path}:{b + 1}: a changed line may only gain `local ` before `instance`/`simp`, or `scoped `/`local ` before a notation command: `{o[a][:60]}` -> `{n[b][:60]}`"
            for a, b in zip(range(i1, i2), range(j1, j2))
            if not allowed_edit(o[a], n[b], new_code[b] if new_code else None)
        ]
    if tag == "replace":
        pairs, added, whole = pair_up(o, n, i1, i2, j1, j2, new_code)
        if whole:
            return [e for k in added for e in added_line_errors(path, k + 1, n[k], known, notes)]
    return [f"{path}:{j1 + 1}: lines were removed or replaced by a different number of lines ({tag}: {i2 - i1} -> {j2 - j1})"]


def check_file(path: str, old: str, new: str, known: dict[str, set[str]], notes: Notes | None = None) -> list[str]:
    o, n = old.split("\n"), new.split("\n")
    errors = []
    if notes is None:  # one file on its own: its own notation edits are the PR's
        notes = Notes()
        errors += [f"{path}:{e}" for e in collect_notes(old, new, notes)]
    ops = difflib.SequenceMatcher(None, o, n, autojunk=False).get_opcodes()
    new_code = mask(new).split("\n")
    return errors + [e for op in ops for e in opcode_errors(path, o, n, op, known, notes, new_code)]


def intake_namespaces() -> set[str]:
    """the libraries that arrived as intake bundles (data/intake/<library>/manifest.jsonl at the base), as module namespaces"""
    return {
        pascal(m.group(1))
        for p in run("ls-tree", "-r", "--name-only", base, "data/intake").split()
        if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
    }


def file_errors(st: str, p: str, intake: set[str], known_by_ns: dict[str, dict[str, set[str]]], notes: Notes | None = None) -> list[str]:
    m = re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", p)
    if st != "M" or not m or m.group(1) not in intake:
        return [f"{p}: a scope-fix PR only modifies existing modules of libraries that arrived as intake bundles (status {st})"]
    ob, nb = blob(base, p), blob(head, p)
    if ob is None or nb is None:
        return [f"{p}: not readable at {base if ob is None else head}"]
    try:
        if m.group(1) not in known_by_ns:  # the library is scanned once, not once per module
            known_by_ns[m.group(1)] = registered(m.group(1))
        return check_file(p, ob.decode("utf-8"), nb.decode("utf-8"), known_by_ns[m.group(1)], notes)
    except UnicodeDecodeError:
        return [f"{p}: not valid UTF-8"]


def main(argv: list[str]) -> None:
    global base, head
    base, head = argv[1], argv[2]
    files = changed_files(base, head)
    intake, known_by_ns = intake_namespaces(), {}
    notes, errors = Notes(), []
    # what the PR makes of notation, over all its files: an importer's `open scoped N` is judged against the declaring module's edit
    for st, p in files:
        ob, nb = blob(base, p), blob(head, p)
        if st == "M" and ob is not None and nb is not None:
            try:
                errors += [f"{p}:{e}" for e in collect_notes(ob.decode("utf-8"), nb.decode("utf-8"), notes)]
            except UnicodeDecodeError:
                pass  # file_errors reports it
    errors += [e for st, p in files for e in file_errors(st, p, intake, known_by_ns, notes)]
    errors += namespace_errors(notes, {m.group(1) for _, p in files if (m := re.match(r"Tengoku/([^/]+)/", p))})
    if not files:
        errors.append("an empty diff")
    if errors:
        fail("scope-fix PR: " + "; ".join(errors[:10]) + (f"; and {len(errors) - 10} more" if len(errors) > 10 else ""))
    libraries = {re.match(r"Tengoku/([^/]+)/", p).group(1) for _, p in files}
    print(f"scope-fix ok: {len(files)} modules of {len(libraries)} libraries, only `local` registrations and `scoped`/`local` notation")


base = head = ""
if __name__ == "__main__":
    main(sys.argv)
