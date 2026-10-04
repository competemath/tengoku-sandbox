"""Extract theorem/lemma declarations — statement AND proof — from Lean 4
source text.

This is a syntactic scanner, not a semantic one — it never elaborates the
file (that would require the project's full toolchain + dependencies built,
which is a multi-GB, multi-hour operation per library and not what this
needs). It finds `theorem`/`lemma` declarations, splits each into its
`statement` (keyword through the type, up to the top-level `:=`) and its
`proof` (everything after, up to the next top-level declaration or EOF).

Both halves are kept: a harvested declaration is a real, already-proven
result from its source library, staged in Tengoku's `tentative/` folder
until Leak's own services re-verify it and it can move to `trusted/`. This
is NOT a proof-stripping tool — see export vs. harvest usage in harvest.py.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

_DECL_KEYWORD_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"  # attributes, e.g. @[simp] (own line or same line)
    r"(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*"
    r"(theorem|lemma)\s+"
    r"(«[^»]*»|[^\s(:{\[⦃\]),]+)",  # the name: a Lean identifier — Greek letters, subscripts, `!`, `?`, or «quoted, with spaces»
    re.MULTILINE,
)
_NAMESPACE_RE = re.compile(r"^namespace\s+(\S+)", re.MULTILINE)
_END_RE = re.compile(r"^end\s+(\S+)", re.MULTILINE)

_OPEN = {"(": ")", "[": "]", "{": "}"}
_CLOSE = {v: k for k, v in _OPEN.items()}

# A line with no leading whitespace is, in Mathlib-style-linted Lean, always
# the start of a new top-level command (theorem/def/namespace/end/#check/...).
# Used to find where a proof body ends, without needing to know Lean's full
# grammar for every possible top-level keyword.
_TOP_LEVEL_LINE_RE = re.compile(r"^[^\s].*$", re.MULTILINE)

# `sorry` as a whole word anywhere in a proof means Lean did NOT actually
# check it — it's an admitted gap, not a proof. Many real-world libraries
# (this scanner's whole reason to exist) mix genuinely proven results with
# still-`sorry`'d placeholders for open/in-progress problems in the same
# file (e.g. a "catalog of competition problems" tracking what's done vs.
# not yet). A proof corpus that can't tell those apart isn't a proof corpus.
_SORRY_RE = re.compile(r"\bsorry\b")

# A `/-- … -/` directly above a declaration that carries an `Author:` line is the
# contributor's credit (README, *Contributors*): it travels with the statement
# into the record, and scripts/ci/credits.py refuses to let it go afterwards. Any
# other docstring belongs to the source library and stays at `source_url`.
_CREDIT_RE = re.compile(r"\bAuthors?:", re.I)


def _contains_sorry(proof: str) -> bool:
    return bool(_SORRY_RE.search(proof))


def _credit_docstring(source_lines: list[str], decl_line: int) -> str | None:
    """The `/-- … -/` ending directly above line `decl_line` (blank lines allowed),
    when it carries a credit; None otherwise."""
    d = decl_line - 1
    while d >= 0 and (
        not source_lines[d].strip()
        or source_lines[d].lstrip().startswith(("--", "@["))
        or source_lines[d].rstrip().endswith("]")  # the tail of a multi-line attribute
    ):
        d -= 1
    if d < 0 or not source_lines[d].rstrip().endswith("-/"):
        return None
    k, depth = d, 0
    while k >= 0:
        depth += source_lines[k].count("-/") - source_lines[k].count("/-")
        if depth <= 0:
            break
        k -= 1
    if k < 0 or not source_lines[k].lstrip().startswith("/--"):
        return None
    doc = "\n".join(source_lines[k : d + 1])
    return doc if _CREDIT_RE.search(doc) else None


@dataclass
class ExtractedDeclaration:
    name: str
    statement: str
    proof: str
    line: int


def _strip_block_comments(text: str) -> str:
    """Blank out `/- … -/` blocks (docstrings and module docs included, nesting respected),
    keeping every newline so line numbers survive: a `theorem` named in a module doc is prose."""
    out: list[str] = []
    depth, i, n = 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        else:
            out.append(text[i] if depth == 0 or text[i] == "\n" else " ")
            i += 1
    return "".join(out)


def _strip_line_comments(text: str) -> str:
    """Blank out `--` line comments so they can't hide a fake `:=`, confuse
    bracket depth, or look like a top-level line. Block comments (`/- ... -/`)
    are left alone — rare inside a signature/proof and handling nesting
    correctly isn't worth the complexity for this heuristic pass."""
    out_lines = []
    for line in text.split("\n"):
        idx = line.find("--")
        out_lines.append(line if idx == -1 else line[:idx])
    return "\n".join(out_lines)


def _find_statement_end(text: str, search_from: int) -> int | None:
    """Find the top-level `:=` that starts the proof, tracking bracket depth
    so one nested inside a default-argument value (e.g. `(n : Nat := 0)`)
    doesn't end the statement early. Returns None if unterminated."""
    depth = 0
    i = search_from
    while i < len(text):
        ch = text[i]
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return i
        elif depth == 0 and ch == "\n" and text[i:].lstrip().startswith(("theorem ", "lemma ")):
            # Next declaration started before `:=` was found — bail out
            # rather than swallow it into this one.
            return i
        i += 1
    return None


def _find_proof_end(text: str, proof_start: int) -> int:
    """Find where the proof body ends: the next line with no leading
    whitespace (a new top-level command), or EOF."""
    for match in _TOP_LEVEL_LINE_RE.finditer(text, proof_start + 1):
        return match.start()
    return len(text)


def extract_declarations(source: str) -> list[ExtractedDeclaration]:
    """Return every theorem/lemma declaration found in `source`, each split
    into its statement and its full proof."""
    text = _strip_line_comments(_strip_block_comments(source))
    source_lines = source.split("\n")  # same line numbering as `text`
    results: list[ExtractedDeclaration] = []
    # `namespace X … end X` nests; a declaration's full name carries the stack, as Lean's does
    # (two files' `theorem foo` in different namespaces are different theorems). `_root_.foo` is foo.
    scopes: list[tuple[int, str]] = [(m.start(), m.group(1)) for m in _NAMESPACE_RE.finditer(text)]
    ends: list[tuple[int, str]] = [(m.start(), m.group(1)) for m in _END_RE.finditer(text)]

    def namespace_at(pos: int) -> str:
        stack: list[str] = []
        events = sorted([(p, "ns", n) for p, n in scopes] + [(p, "end", n) for p, n in ends])
        for p, kind, n in events:
            if p >= pos:
                break
            if kind == "ns":
                stack.append(n)
            elif stack and stack[-1] == n:
                stack.pop()
        return ".".join(stack)

    for match in _DECL_KEYWORD_RE.finditer(text):
        name = match.group(2).rstrip(".")
        if name.startswith("_root_."):
            name = name[len("_root_.") :]
        else:
            ns = namespace_at(match.start())
            if ns:
                name = f"{ns}.{name}"
        start = match.start()
        line_no = text.count("\n", 0, match.start(1)) + 1  # the keyword's line, not a blank line above the attributes

        colon_eq = _find_statement_end(text, match.end())
        if colon_eq is None:
            continue  # unterminated — skip rather than guess

        statement = text[start:colon_eq].strip()
        doc = _credit_docstring(source_lines, line_no - 1)
        if doc:
            statement = f"{doc}\n{statement}"
        # Skip declarations that are just `theorem`/`lemma` inside a string
        # literal or doc example rather than real code (heuristic: a real
        # declaration's statement must contain a top-level `:` separating
        # the binders from the type).
        if ":" not in statement:
            continue

        proof_end = _find_proof_end(text, colon_eq)
        proof = text[colon_eq:proof_end].strip()

        if _contains_sorry(proof):
            continue  # admitted, not proven — not a real proof

        results.append(ExtractedDeclaration(name=name, statement=statement, proof=proof, line=line_no))

    return results
