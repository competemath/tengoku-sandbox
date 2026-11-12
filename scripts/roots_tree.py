#!/usr/bin/env python3
"""roots_tree.py — the declarations of the tree's libraries that sit in the root namespace get their library's namespace.

  roots_tree.py apply --tree CHECKOUT --roots DIR     # DIR/<Library>.txt: the `root: NAME` lines of tengoku-leakscan for that library (the root-inventory workflow's artifact)

The same transformation the factory applies to a bundle since emissary-archangel#179 (`scope_rewrite.py --qualify-roots`, whose code this file carries unchanged from `mask` to
`qualify_manifest`), applied to the libraries that arrived before it. For a library `L` with roots R:
  - a declaration named by a root of R, a `namespace r` block of a root r (with its `end`), and a dotted `r.x` declaration get `Tengoku.L.` in front;
  - an `open r` of a root namespace follows it;
  - a module that declares or still uses a root gets `namespace Tengoku.L end Tengoku.L open Tengoku.L` on its first body line (a bare use keeps resolving to the library's own name);
  - the manifest record (name and statement) of a renamed declaration follows.
Everything goes INSIDE existing lines (no line moves, so no position in a report or a docstring shifts), and each edited module ends with one generated comment. A root no module declares (the
name Lean gave an anonymous instance) is reported in `unresolved`: text cannot rename it.
The result is a function of the tree and the roots: running it twice changes nothing (an edited name no longer matches).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def mask(text: str) -> str:
    """the text with every comment (line, nested block, doc) and string literal blanked to spaces: same length and same columns, so a word
    found in the mask is code, and its position is the position in the text"""
    out, i, n = [], 0, len(text)
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
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append("".join("\n" if ch == "\n" else " " for ch in text[i:j]))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out)


class Lines:
    """a file as lines, with the mask of each; an edit goes into both so that later edits find their columns"""

    def __init__(self, text: str):
        self.text, self.code = text.split("\n"), mask(text).split("\n")
        self.edited: list[int] = []  # the line of every insertion, in order

    def insert(self, i: int, col: int, word: str) -> None:
        self.edited.append(i)
        self.text[i] = self.text[i][:col] + word + self.text[i][col:]
        self.code[i] = self.code[i][:col] + word + self.code[i][col:]


NAMESPACE = re.compile(
    r"^\s*(?:(?:public|noncomputable)\s+)*namespace\s+((?:«[^»]*»|[^\s«»])+)\s*$"
)  # a «quoted» component may hold a space

OPENER = re.compile(r"^\s*(?:namespace\s+(?:«[^»]*»|[^\s«»])+|(?:@\[expose\]\s+)?(?:(?:public|noncomputable)\s+)*section\b.*|mutual\s*)$")
CLOSER = re.compile(r"^\s*end\b")


def scope_info(code: list[str]) -> tuple[list[tuple[int, ...]], dict[int, int]]:
    """for every line the openers (`namespace`, `section`, `mutual`) that enclose it, and for every opener the line of its `end`"""
    stack: list[int] = []
    open_at, end_of = [], {}
    for i, ln in enumerate(code):
        open_at.append(tuple(stack))
        if OPENER.match(ln):
            stack.append(i)
        elif CLOSER.match(ln) and stack:
            end_of[stack.pop()] = i
    return open_at, end_of


HEADER_LINE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*(?:import\s|module\s*$|prelude\s*$)")
SECTION = re.compile(r"^\s*(?:@\[expose\]\s*)?(?:(?:public|noncomputable)\s+)*section\b")


def body_start(lines: list[str]) -> int:
    """the index of the first line after the header: blank lines, comments (line and block), `module`/`prelude` and imports are the header; a
    `section` line that opens the body is part of it (the inserted commands go inside it)"""
    depth = 0
    for i, ln in enumerate(lines):
        s = ln.strip()
        if depth:
            depth = max(depth + s.count("/-") - s.count("-/"), 0)
            continue
        if not s or s.startswith("--"):
            continue
        if s.startswith("/-"):
            depth = max(s.count("/-") - s.count("-/"), 0)
            continue
        if HEADER_LINE.match(ln):
            continue
        return i + 1 if SECTION.match(ln) else i
    return len(lines)


QUOTED = r"«[^»]*»"
NAME_TOKEN = rf"(?:{QUOTED}|[^\s:({{\[⦃«»])+"
PLAIN = r"[^\W\d][\w'!?]*"  # a plain identifier component: a letter or `_`, then letters, digits, `_`, `'`, `!`, `?` (Unicode letters and subscripts included)
SIMPLE_NAME = re.compile(rf"(?:{QUOTED}|{PLAIN})(?:\.(?:{QUOTED}|{PLAIN}))*")
ROOT_LINE = re.compile(rf"(?m)^[ \t]*root:\s+((?:{QUOTED}|[^\s«»])+)[ \t]*$")  # leading blanks: `;` may be followed by a space


def head_of(name: str) -> str:
    """the first component of a dotted name, the quotes of a «quoted» one kept: `«a.b».c` -> `«a.b»`, `Foo.bar` -> `Foo`"""
    m = re.match(rf"{QUOTED}|[^.«»]+", name)
    return m.group(0) if m else name


ROOT_DECL = re.compile(
    r"^(?P<pre>[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|public|noncomputable|nonrec|partial|unsafe)[ \t]+)*)"
    r"(?:(?:local|scoped)[ \t]+)?(?:theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom|instance)\s+"
    rf"(?:\(priority\s*:=[^)]*\)\s*)?(?P<name>{NAME_TOKEN})"
)
NAMESPACE_NAME = re.compile(rf"^(?P<pre>\s*(?:(?:public|noncomputable)\s+)*namespace\s+)(?P<name>(?:{QUOTED}|[^\s«»])+)\s*$")
END_NAME = re.compile(rf"^(?P<pre>\s*end\s+)(?P<name>(?:{QUOTED}|[^\s«»])+)\s*$")
OPEN_MARK = "namespace {ns} end {ns} open {ns} "
OPEN_HEADS = (  # `open scoped …` first; when that leaves no valid ending, `scoped` is an argument (the order a backtracking match would try)
    re.compile(r"^(?P<pre>\s*(?:@\[[^\]]*\]\s*)?open\s+scoped\s+)"),
    re.compile(r"^(?P<pre>\s*(?:@\[[^\]]*\]\s*)?open\s+)"),
)
OPEN_TAIL = (  # where the arguments of an `open` end: before `hiding`/`renaming`, before a trailing `in`, before a `(`, or at the end of the line
    re.compile(r"\s+(?:hiding|renaming)\b"),
    re.compile(r"\s+in\s*$"),
    re.compile(r"\s*\("),
    re.compile(r"\s*$"),
)


def open_args(code: str) -> tuple[int, str] | None:
    """(column, text) of the arguments of an `open` line, or None: the shortest arguments (no parenthesis in them) after which the line ends as an `open` line may end. The same as the
    regular expression with a lazy `[^()]*?` and an alternation of those endings (the factory's, emissary-archangel scope_rewrite.py OPEN_LINE) finds on every well-formed `open` line,
    without its backtracking (each candidate end is tried once); they differ only on lines that are no Lean (`open scoped  hiding)`), where the old one backtracked into the blanks."""
    for head_re in OPEN_HEADS:
        head = head_re.match(code)
        if not head:
            continue
        rest = code[head.end() :]
        for end in range(len(rest) + 1):
            if end and rest[end - 1] in "()":
                break  # the arguments cannot contain a parenthesis
            tail = rest[end:]
            if any(t.match(tail) for t in OPEN_TAIL):
                return head.end(), rest[:end]
    return None


def parse_roots(text: str) -> set[str]:
    """the `root: NAME` lines of a leak scan report (a declaration of the library whose name has one component)"""
    return {m.group(1) for m in ROOT_LINE.finditer(text.replace(";", "\n"))}


def _uses_roots(f: Lines, roots: set[str]) -> bool:
    """a bare use of a root name is left in the code (an edited token is preceded by `.`, so it no longer matches)"""
    if not roots:
        return False
    pat = re.compile(r"(?<![\w.'«])(?:" + "|".join(re.escape(r) for r in sorted(roots, key=len, reverse=True)) + r")(?![\w'»])")
    return any(pat.search(c) for c in f.code)


def qualify_roots_in_file(f: Lines, roots: set[str], ns: str, mark_open: bool = True) -> dict:
    """The edits of one module: a declaration whose name is a root of the library, a `namespace R` block of a root R (with its `end`), and a dotted `R.x` declaration get `<ns>.`
    in front; the first body line gets `namespace NS end NS open NS` when the module declares or still uses a root. All of it goes INSIDE existing lines (no line moves)."""
    done: dict = {
        "declared": [],
        "namespaces": 0,
        "dotted": 0,
        "opened": False,
        "heads": set(),
    }
    open_at, end_of = scope_info(f.code)
    for i, code in enumerate(f.code):
        if any(NAMESPACE.match(f.code[o]) for o in open_at[i]):
            continue  # inside a namespace a declaration is `N.x`, not a root; the block itself is handled at its own `namespace` line
        if m := NAMESPACE_NAME.match(code):
            head = head_of(m.group("name"))
            if head in roots:
                f.insert(i, m.start("name"), ns + ".")
                done["heads"].add(head)
                done["namespaces"] += 1
                end = end_of.get(i)
                if end is not None and (e := END_NAME.match(f.code[end])) and e.group("name") == m.group("name"):
                    f.insert(end, e.start("name"), ns + ".")
            continue
        m = ROOT_DECL.match(code)
        if not m:
            continue
        name = m.group("name")
        if head_of(name) in roots:
            f.insert(i, m.start("name"), ns + ".")
            done["heads"].add(head_of(name))
            if len(re.findall(rf"{QUOTED}|[^.«»]+", name)) > 1:  # a dot inside «quotes» is part of one component
                done["dotted"] += 1
            else:
                done["declared"].append(name)
    for i, code in enumerate(
        f.code
    ):  # `open R` of a root namespace R: the namespace moved, so the `open` follows (right to left: an insertion shifts the columns after it)
        found = open_args(code) if "namespace" not in code else None
        if found:
            column, args = found
            for t in reversed(list(re.finditer(rf"(?:{QUOTED}|[^\s«»])+", args))):
                tok = t.group(0)
                if head_of(tok) in roots and not tok.startswith(ns):
                    f.insert(i, column + t.start(), ns + ".")
                    done["opens"] = done.get("opens", 0) + 1
    touched = bool(done["declared"] or done["namespaces"] or done["dotted"] or done.get("opens"))
    first = body_start(f.text)
    mark = OPEN_MARK.format(ns=ns)
    if mark_open and (touched or _uses_roots(f, roots)) and first < len(f.text) and mark not in f.text[first]:
        f.insert(first, 0, mark)
        done["opened"] = True
    return done


def qualify_manifest_text(text: str, roots: set[str], ns: str) -> tuple[str, int]:
    """The manifest lines (text) of a declaration whose name starts with a root that the module pass renamed (`roots` is that set: the declaration itself, a member of its namespace block, a dotted
    `R.x`) follow: the module now declares `<ns>.<name>`. A root no module pass renamed (an anonymous instance) leaves its record alone. Returns the new text and the count."""
    out, changed = [], 0
    for line in text.splitlines(keepends=True):
        rec = json.loads(line) if line.strip() else None
        if rec and head_of(rec.get("name", "")) in roots:
            f = Lines(rec["statement"])
            qualify_roots_in_file(f, roots, ns, mark_open=False)  # a record's statement is the declaration alone: no header, no `open`
            rec["statement"] = "\n".join(f.text)
            rec["name"] = f"{ns}.{rec['name']}"
            line = json.dumps(rec, ensure_ascii=False) + "\n"
            changed += 1
        out.append(line)
    return "".join(out), changed


def valid_namespace(ns: str) -> str:
    """a namespace name as it goes into generated Lean (`namespace NS end NS open NS`, a declaration prefix): dotted components, plain or «quoted», nothing else: no newline, no command"""
    if not SIMPLE_NAME.fullmatch(ns) or "\n" in ns or "\r" in ns:
        raise argparse.ArgumentTypeError(f"not a Lean namespace name: {ns!r}")
    return ns


LIBRARY = re.compile(r"[A-Za-z][A-Za-z0-9]*")  # `Tengoku/<Library>/`: a plain identifier, never a path
MODULE_PATH = r"Tengoku/{lib}/.+\.lean"
MANIFEST_PATH = re.compile(r"data/intake/[^/]+/manifest\.jsonl")
NOTE = "-- Tengoku: root names of this library moved to {ns} so they do not collide with other libraries (generated)\n"


def qualify_module_text(text: str, roots: set[str], ns: str) -> tuple[str | None, dict]:
    """qualify_roots_in_file on the text of one module: the new text (with the generated note) and the edits; None when nothing changed"""
    f = Lines(text)
    d = qualify_roots_in_file(f, roots, ns)
    if not f.edited:
        return None, d
    new = "\n".join(f.text)
    if not new.endswith("\n"):
        new += "\n"
    return new + NOTE.format(ns=ns), d


def manifest_namespace_text(text: str) -> str | None:
    """`Tengoku.<Library>` of an intake manifest: the first two components of the module of its first record"""
    for ln in text.splitlines():
        if ln.strip():
            parts = (json.loads(ln).get("module") or "").split(".")
            return ".".join(parts[:2]) if len(parts) > 2 and parts[0] == "Tengoku" else None
    return None


def qualify_files(files: dict[str, str], reports: dict[str, str]) -> tuple[dict[str, str], dict]:
    """The whole transformation on text, with no file system: `files` maps a repository path (`Tengoku/<Library>/….lean`, `data/intake/<key>/manifest.jsonl`) to its text, `reports` a library
    to its root report. Returns the files that change (path -> new text) and, per library, what was done."""
    changed: dict[str, str] = {}
    done: dict = {}
    manifests = sorted(p for p in files if MANIFEST_PATH.fullmatch(p))
    for lib in sorted(reports):
        roots = parse_roots(reports[lib]) if LIBRARY.fullmatch(lib) else set()
        modules = sorted(p for p in files if re.fullmatch(MODULE_PATH.format(lib=lib), p)) if roots else []
        if not modules:
            continue
        ns = f"Tengoku.{lib}"
        valid_namespace(ns)
        rep: dict = {"qualified": 0, "namespaces": 0, "dotted": 0, "modules_opened": 0, "unresolved": []}
        seen: set[str] = set()
        renamed: set[str] = set()
        for path in modules:
            new, d = qualify_module_text(files[path], roots, ns)
            if new is None:
                continue
            changed[path] = new
            rep["qualified"] += len(d["declared"])
            rep["namespaces"] += d["namespaces"]
            rep["dotted"] += d["dotted"]
            rep["modules_opened"] += 1 if d["opened"] else 0
            seen.update(d["declared"])
            renamed |= d["heads"]
        rep["unresolved"] = sorted(roots - seen)
        rep["renamed"] = sorted(renamed)  # the roots the module pass renamed: what the manifest follows
        for path in manifests:
            text = changed.get(path, files[path])
            if manifest_namespace_text(text) == ns:
                new, count = qualify_manifest_text(text, renamed, ns)
                rep["manifest_records"] = count
                if count:
                    changed[path] = new
        done[lib] = rep
    return changed, done


def apply(tree: Path, roots_dir: Path) -> dict:
    """qualify_files on a checkout: reads the reports of `roots_dir` and the files of their libraries under `tree`, writes the files that change"""
    reports = {rep.stem: rep.read_text(encoding="utf-8", errors="replace") for rep in sorted(roots_dir.glob("*.txt"))}
    files: dict[str, str] = {}
    for lib in reports:
        if LIBRARY.fullmatch(lib):
            for path in sorted((tree / "Tengoku" / lib).rglob("*.lean")):
                files[path.relative_to(tree).as_posix()] = path.read_text(encoding="utf-8")
    for path in sorted((tree / "data" / "intake").glob("*/manifest.jsonl")):
        files[path.relative_to(tree).as_posix()] = path.read_text(encoding="utf-8")
    changed, done = qualify_files(files, reports)
    for rel, text in changed.items():
        (tree / rel).write_text(text, encoding="utf-8")
    return done


def main(argv: list[str] | None = None) -> int:
    """`roots_tree.py apply`, run in a checkout: every report under `data/roots/<id>/<Library>.txt` of the working directory is applied, the ids in order (a report already applied
    changes nothing). No path is taken from the command line: the tree is the working directory."""
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("cmd", choices=["apply"])
    ap.parse_args(argv)
    tree = Path.cwd()
    report = {d.name: apply(tree, d) for d in sorted((tree / "data" / "roots").glob("*")) if d.is_dir()}
    print(json.dumps(report, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
