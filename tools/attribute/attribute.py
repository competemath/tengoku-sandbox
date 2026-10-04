#!/usr/bin/env python3
"""attribute.py <dir> --credit "Author: …" — put your credit on every declaration.

A project with three hundred theorems should not need three hundred hand-written
docstrings before it is submitted. This walks the `.lean` files under a directory
and gives every theorem, lemma, definition, instance, structure, inductive and
class the credit as the last line of its docstring, writing the docstring where
there is none. Running it twice changes nothing; another author's credit is never
overwritten; commented-out code is never touched. README.md next to this file
has the rest.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

KINDS = ["theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "class", "opaque"]
MODIFIERS = ["private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local", "public", "meta"]
KIND_RE = re.compile(r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*(?P<kind>" + "|".join(KINDS) + r")\b(?:\s+(?P<name>[^\s(:{\[⦃]+))?")
MOD_LINE_RE = re.compile(r"^\s*(?:(?:" + "|".join(MODIFIERS) + r")\s*)+$")
# A docstring that closes on the line it opens: `/-- doc -/ theorem …`, `/-- doc -/ @[simp]`.
DOC_LINE_RE = re.compile(r"^(?P<indent>[ \t]*)/--(?P<doc>.*?)-/(?P<rest>.*)$")
LINE_COMMENT_RE = re.compile(r"^\s*--")
# The marker the tree's checks key on (scripts/ci/credits.py, tools/lean_extract.py).
CREDIT_RE = re.compile(r"\bAuthors?:", re.I)


def attr_end(s: str, i: int) -> int | None:
    """`s[i:]` starts with `@[`; the index just past its `]`, or None if unclosed. Brackets
    nest (`@[simps (config := …)]`) and a string literal may hold any of them."""
    depth, j = 0, i + 1
    while j < len(s):
        c = s[j]
        if c == '"':
            j += 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
        elif c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return None


def skip_attrs(s: str, i: int = 0) -> int | None:
    """The index after the leading `@[…]` groups (and whitespace) of `s[i:]`; None if one is unclosed."""
    j = i
    while True:
        while j < len(s) and s[j].isspace():
            j += 1
        if not s.startswith("@[", j):
            return j
        j = attr_end(s, j)
        if j is None:
            return None


def is_attr_block(s: str) -> bool:
    return "@[" in s and skip_attrs(s) == len(s)


def decl_at(line: str) -> tuple[str, str, str] | None:
    """(indent, kind, label) when `line` starts a declaration: attributes and modifiers on
    the line, then the keyword. The label is the name, or the kind for an anonymous instance."""
    indent = line[: len(line) - len(line.lstrip())]
    j = skip_attrs(line, len(indent))
    if j is None:
        return None
    m = KIND_RE.match(line, j)
    if not m:
        return None
    return indent, m.group("kind"), (m.group("name") or "").rstrip(".") or m.group("kind")


def strip_comment(line: str) -> str:
    """The line without a trailing `-- …` comment; the `--` of a `/--` docstring opener is not one."""
    m = DOC_LINE_RE.match(line)
    if m:
        return line[: m.start("rest")] + re.sub(r"\s*--.*$", "", m.group("rest"))
    return re.sub(r"\s*(?<!/)--.*$", "", line)


def closing_at(line: str) -> int | None:
    """Index of the `-/` that ends the line's code: only whitespace or a `--` comment may follow it."""
    pos = line.rfind("-/")
    if pos >= 0 and re.fullmatch(r"\s*(--.*)?", line[pos + 2 :]):
        return pos
    return None


def closing_pos(line: str, depth: int) -> int | None:
    """Index of the `-/` on this line that closes the comment open at its start (depth > 0), or None."""
    for m in re.finditer(r"/-|-/", line):
        depth += 1 if m.group() == "/-" else -1
        if depth == 0:
            return m.start()
    return None


def opener_of(lines: list[str], d: int) -> int | None:
    """The line opening the block comment that closes on line d, by nesting depth."""
    k, depth = d, 0
    while k >= 0:
        depth += lines[k].count("-/") - lines[k].count("/-")
        if depth <= 0:
            return k
        k -= 1
    return None


def close_with_attrs(lines: list[str], d: int, h: int) -> int | None:
    """Index of a `-/` on line d followed by attributes that run to line h - 1 (`… -/ @[simp]`,
    `… -/ @[simp,` … `]`), or None."""
    line = strip_comment(lines[d])
    tail = [strip_comment(l) for l in lines[d + 1 : h] if l.strip() and not LINE_COMMENT_RE.match(l)]
    for m in re.finditer("-/", line):
        if is_attr_block("\n".join([line[m.end() :]] + tail)):
            return m.start()
    return None


def lead_in(lines: list[str], i: int) -> tuple[int, tuple[int, int, int] | None]:
    """(h, doc): h is the first line of the declaration's own lead-in above line i — attribute
    lines (one attribute may span several; blank and `--` lines may sit between) and modifier-only
    lines, never `open … in` or `set_option … in`, which a docstring goes below — and doc its
    docstring: above h, or on the line that opens the attributes (`/-- doc -/ @[simp,` … `]`)."""
    h = i
    while h > 0:
        found = None
        for k in range(h - 1, max(-1, h - 24), -1):
            line = lines[k]
            if not line.strip() or LINE_COMMENT_RE.match(line):
                continue
            if MOD_LINE_RE.match(strip_comment(line)):
                found = k
                break
            block = "\n".join(strip_comment(l) for l in lines[k:h] if l.strip() and not LINE_COMMENT_RE.match(l))
            if is_attr_block(block):
                found = k
                break
            pos = close_with_attrs(lines, k, h)
            if pos is not None:  # the comment closing on line k opens the attributes: the lead-in starts after it
                k0 = opener_of(lines, k)
                if k0 is not None and lines[k0].lstrip().startswith("/--"):
                    return k + 1, (k0, k, pos)
                return k + 1, (-1, k, pos)  # a plain `/- … -/`: the line is split so a docstring can go above the attributes
            if block.count("]") <= block.count("["):
                break  # not the tail of an attribute that opens further up
        if found is None:
            break
        h = found
    return h, docstring_above(lines, h)


def docstring_above(lines: list[str], h: int) -> tuple[int, int, int] | None:
    """(opening line, closing line, index of the closing `-/` in it) of the docstring directly
    above line h — blank and `--` lines may sit between — or None: a `/- … -/` or `/-! … -/` is not one."""
    d = h - 1
    while d >= 0 and (not lines[d].strip() or LINE_COMMENT_RE.match(lines[d])):
        d -= 1
    if d < 0:
        return None
    pos = closing_at(lines[d])
    if pos is not None:
        k = opener_of(lines, d)
        if k is None or not lines[k].lstrip().startswith("/--"):
            return None
        return k, d, pos
    pos = close_with_attrs(lines, d, h)  # `/-- doc -/ @[simp]`: the docstring's closing line carries the attributes
    if pos is not None:
        k = opener_of(lines, d)
        if k is not None and lines[k].lstrip().startswith("/--"):
            return k, d, pos
    return None


def attribute_file(path: Path, credit: str, kinds: set[str], dry_run: bool) -> dict | None:
    """Credit every declaration in one file; None when the file is not UTF-8."""
    try:
        text = path.read_bytes().decode("utf-8")
    except UnicodeDecodeError:
        return None
    crlf = "\r\n" in text
    if crlf:
        text = text.replace("\r\n", "\n")
    lines = text.split("\n")
    edits: list[tuple[str, int, object]] = []
    stats: dict = {"credited": 0, "already": 0, "other": []}

    def credit_docstring(indent: str, k: int, d: int, close_at: int, label: str, i: int) -> None:
        body = "\n".join(lines[k:d] + [lines[d][:close_at]])
        if credit in body:
            stats["already"] += 1
            return
        if CREDIT_RE.search(body):
            stats["other"].append(f"{path}:{i + 1} {label}")
            return
        stats["credited"] += 1
        head = lines[d][:close_at]
        if not head.strip():  # `-/` opens its line: the credit goes on the line above it
            edits.append(("insert", d, ([""] if lines[d - 1].strip() else []) + [f"{indent}{credit}"]))
        else:
            edits.append(("replace", d, f"{head.rstrip()}\n\n{indent}{credit} {lines[d][close_at:]}"))

    depth = 0
    for i, line in enumerate(lines):
        if depth == 0:
            dec = decl_at(line)
            if dec:
                indent, kind, label = dec
                if kind in kinds:
                    h, doc = lead_in(lines, i)
                    if doc is None:
                        stats["credited"] += 1
                        edits.append(("insert", h, [f"{indent}/-- {credit} -/"]))
                    elif doc[0] < 0:  # `/- … -/ @[simp,`: put the attributes on their own line, the docstring between
                        stats["credited"] += 1
                        _, d, pos = doc
                        edits.append(
                            (
                                "replace",
                                d,
                                f"{lines[d][: pos + 2].rstrip()}\n{indent}/-- {credit} -/\n{indent}{lines[d][pos + 2 :].lstrip()}",
                            )
                        )
                    else:
                        credit_docstring(indent, *doc, label, i)
            else:
                m = DOC_LINE_RE.match(line)
                if m:
                    dec = decl_at(m.group("rest"))
                    if dec and dec[1] in kinds:
                        credit_docstring(m.group("indent"), i, i, m.start("rest") - 2, dec[2], i)
        else:  # inside a comment: a docstring may close on the declaration's own line (`-/ theorem …`)
            pos = closing_pos(line, depth)
            dec = decl_at(line[pos + 2 :]) if pos is not None else None
            if dec and dec[1] in kinds:
                k = opener_of(lines, i)
                if k is not None and lines[k].lstrip().startswith("/--"):
                    credit_docstring(line[: len(line) - len(line.lstrip())], k, i, pos, dec[2], i)
        depth = max(0, depth + line.count("/-") - line.count("-/"))

    for op, idx, payload in sorted(edits, key=lambda e: -e[1]):
        if op == "insert":
            lines[idx:idx] = payload  # type: ignore[arg-type]
        else:
            lines[idx] = payload  # type: ignore[assignment]
    if edits and not dry_run:
        out = "\n".join(lines)
        path.write_text(out.replace("\n", "\r\n") if crlf else out, encoding="utf-8", newline="")
    return stats


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Write your credit into every declaration's docstring under a directory.")
    ap.add_argument("directory", type=Path, help="the Lean project (every .lean file under it, .lake/ skipped)")
    ap.add_argument(
        "--credit",
        required=True,
        help='one line starting with "Author:", e.g. "Author: Ada Lovelace (https://github.com/ada), with Claude"',
    )
    ap.add_argument(
        "--kinds", default=",".join(KINDS), help=f"declaration kinds to credit, comma-separated (default: all of {', '.join(KINDS)})"
    )
    ap.add_argument("--dry-run", action="store_true", help="report what would change; write nothing")
    a = ap.parse_args(argv)
    credit = " ".join(a.credit.split())
    if not CREDIT_RE.search(credit):
        ap.error("--credit must contain `Author:` (or `Authors:`): that is the marker the tree's checks key on")
    if "-/" in credit or "/-" in credit:
        ap.error("--credit cannot contain `-/` or `/-`: it goes inside a doc comment")
    kinds = {k.strip() for k in a.kinds.split(",") if k.strip()}
    if kinds - set(KINDS):
        ap.error(f"unknown kinds: {', '.join(sorted(kinds - set(KINDS)))}")
    files = sorted(p for p in a.directory.rglob("*.lean") if ".lake" not in p.parts)
    if not files:
        print(f"no .lean files under {a.directory}", file=sys.stderr)
        return 1
    credited = already = skipped = 0
    other: list[str] = []
    for f in files:
        st = attribute_file(f, credit, kinds, a.dry_run)
        if st is None:
            print(f"{f}: not UTF-8, skipped", file=sys.stderr)
            skipped += 1
            continue
        if st["credited"]:
            print(f"{f}: {st['credited']} {'would be ' if a.dry_run else ''}credited")
        credited += st["credited"]
        already += st["already"]
        other += st["other"]
    print(
        f"{'would credit' if a.dry_run else 'credited'} {credited} declarations in {len(files) - skipped} files; {already} already carried this credit"
    )
    if other:
        print(f"{len(other)} left alone, their docstring names another author:")
        for o in other:
            print(f"  {o}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
