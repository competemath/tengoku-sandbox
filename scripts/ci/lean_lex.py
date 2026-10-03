"""lean_lex.py — the one Lean lexer the gate's text checks share.

`code_only(text)` returns the source with every comment removed (line, nested block, doc) and the contents of every
string, raw string and character literal blanked, keeping line breaks. A check that reads its result never sees a
word inside a comment or a string, and a comment marker inside a string (or the other way round) cannot hide what
follows it: comments, strings and code are one state machine, each delimiter meaningful only in its own state.
"""

from __future__ import annotations

import re

_CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
_RAW_OPEN = re.compile(r'r(#*)"')
_IDENT = re.compile(r"[\w'!?.]")


def _blank(s: str) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in s)


def _past(text: str, k: int, closer: str) -> int:
    """The index just past the next `closer` found from `k`; the end of the text when there is none."""
    e = text.find(closer, k)
    return len(text) if e < 0 else e + len(closer)


def _block_comment_end(text: str, k: int) -> int:
    """The index just past the (nested) block comment whose `/-` is at `k`; the end when it never closes."""
    depth, k, n = 1, k + 2, len(text)
    while k < n and depth:
        if text.startswith("/-", k):
            depth, k = depth + 1, k + 2
        elif text.startswith("-/", k):
            depth, k = depth - 1, k + 2
        else:
            k += 1
    return k


def _line_comment_end(text: str, k: int) -> int:
    """The index of the line break that ends the comment at `k` (the end of the text when there is none)."""
    nl = text.find("\n", k)
    return len(text) if nl < 0 else nl


def _string_body_end(text: str, i: int) -> int:
    """For a plain string whose opening quote is at `i`: the index of its closing quote (at or past the end if unclosed)."""
    j, n = i + 1, len(text)
    while j < n and text[j] != '"':
        j += 2 if text[j] == "\\" else 1
    return j


def _after_ident(text: str, i: int) -> bool:
    return i > 0 and bool(_IDENT.match(text[i - 1]))


def _raw_open(text: str, i: int) -> re.Match[str] | None:
    """The opening `r#"` of a raw string at `i`, unless the `r` ends an identifier."""
    if text[i] != "r" or _after_ident(text, i):
        return None
    return _RAW_OPEN.match(text, i)


def _is_interpolated_quote(text: str, i: int) -> bool:
    """`s!"`, `m!"`, `f!"`: a quote after `!` after an identifier character opens an interpolated string."""
    return text[i] == '"' and i >= 2 and text[i - 1] == "!" and bool(_IDENT.match(text[i - 2]))


def _char_literal(text: str, i: int) -> re.Match[str] | None:
    """A character literal at `i`, unless the quote is an identifier's prime."""
    if text[i] != "'" or _after_ident(text, i):
        return None
    return _CHAR.match(text, i)


def _skip_opaque(text: str, k: int) -> int | None:
    """If a comment, escaped identifier, string or character literal starts at `k`, the index just past it; else None."""
    if text[k] == "«":  # an escaped identifier: opaque
        return _past(text, k + 1, "»")
    if text.startswith("/-", k):
        return _block_comment_end(text, k)
    if text.startswith("--", k):
        return _line_comment_end(text, k)
    if m := _raw_open(text, k):  # a raw string: a brace or quote inside it is text
        return _past(text, m.end(), '"' + m.group(1))
    if _is_interpolated_quote(text, k):
        return _interpolated(text, k)[1]
    if text[k] == '"':
        return _string_body_end(text, k) + 1
    if m := _char_literal(text, k):
        return m.end()
    return None


def _hole_end(text: str, j: int) -> int:
    """The index just past the `}` that closes the interpolation hole whose `{` is at `j`. Braces count only in code:
    strings (interpolated ones included), character literals and comments inside the hole are stepped over whole."""
    depth, k, n = 1, j + 1, len(text)
    while k < n and depth:
        skipped = _skip_opaque(text, k)
        if skipped is not None:
            k = skipped
        else:
            depth += {"{": 1, "}": -1}.get(text[k], 0)
            k += 1
    return k


def _interpolated(text: str, i: int) -> tuple[str, int]:
    """An interpolated string (`s!"…{e}…"`, `m!`, `f!`…) from its opening quote at `i`: the literal text blanked, each
    `{…}` hole kept as code (lexed in turn, so strings, character literals and comments inside a hole are handled).
    Returns the replacement and the index after the closing quote."""
    out, j, n = ['"'], i + 1, len(text)
    while j < n and text[j] != '"':
        if text[j] == "\\":
            out.append(_blank(text[j : j + 2]))
            j += 2
        elif text[j] == "{":
            k = _hole_end(text, j)
            closed = text[k - 1 : k] == "}"  # an unclosed hole runs to the end: keep its last character (found by scripts/ci/fuzz)
            out.append("{" + code_only(text[j + 1 : k - 1 if closed else k]) + "}")
            j = k
        else:
            out.append("\n" if text[j] == "\n" else " ")
            j += 1
    out.append('"')
    return "".join(out), j + 1


def _emit(text: str, i: int, out: list[str]) -> int:
    """Append what the token at `i` leaves in the code-only text to `out`; the index after the token."""
    c = text[i]
    if c == "«":  # an escaped identifier: its text is a name, whatever it contains (--, /-, braces, quotes)
        j = _past(text, i + 1, "»")
        out.append(text[i:j])
        return j
    if text.startswith("/-", i):  # a block comment leaves its line breaks, so line numbers stay put
        j = _block_comment_end(text, i)
        out.append("\n" * text.count("\n", i, j))
        return j
    if text.startswith("--", i):
        return _line_comment_end(text, i)
    if m := _raw_open(text, i):
        close = '"' + m.group(1)
        j = text.find(close, m.end())
        j = len(text) if j < 0 else j
        out.append(text[i : m.end()] + _blank(text[m.end() : j]) + close)  # delimiters kept: columns stay put
        return j + len(close)
    if _is_interpolated_quote(text, i):
        s, j = _interpolated(text, i)  # s!"…{e}…": the holes are code
        out.append(s)
        return j
    if c == '"':
        j = _string_body_end(text, i)
        out.append('"' + _blank(text[i + 1 : min(j, len(text))]) + '"')
        return j + 1
    if m := _char_literal(text, i):
        out.append("' '")
        return m.end()
    out.append(c)
    return i + 1


def code_only(text: str) -> str:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        i = _emit(text, i, out)
    return "".join(out)
