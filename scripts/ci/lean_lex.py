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


def _skip_block_comment(text: str, i: int) -> int:
    """The index just past the `-/` that closes the (nested) block comment opened by the `/-` at `i`; the end of the text if it never closes."""
    depth, k, n = 1, i + 2, len(text)
    while k < n and depth:
        if text.startswith("/-", k):
            depth, k = depth + 1, k + 2
        elif text.startswith("-/", k):
            depth, k = depth - 1, k + 2
        else:
            k += 1
    return k


def _skip_line_comment(text: str, i: int) -> int:
    """The index of the line break that ends the `--` comment at `i` (the break itself is not part of the comment)."""
    nl = text.find("\n", i)
    return len(text) if nl < 0 else nl


def _skip_escaped(text: str, i: int) -> int:
    """The index just past the `»` that closes the escaped identifier opened by the `«` at `i`."""
    e = text.find("»", i + 1)
    return len(text) if e < 0 else e + 1


def _string_close(text: str, i: int) -> int:
    """The index of the quote that closes the string literal opened at `i` (the end of the text if there is none); `\\` escapes the next character."""
    j, n = i + 1, len(text)
    while j < n and text[j] != '"':
        j += 2 if text[j] == "\\" else 1
    return j


def _raw_close(text: str, m: re.Match[str]) -> int:
    """The index where the closing delimiter of the raw string opened by `m` starts (the end of the text if there is none)."""
    e = text.find('"' + m.group(1), m.end())
    return len(text) if e < 0 else e


def _is_interpolated_quote(text: str, i: int) -> bool:
    """`s!"…"`, `m!"…"`, `f!"…"`: a quote right after `<identifier>!`."""
    return i >= 2 and text[i - 1] == "!" and bool(_IDENT.match(text[i - 2]))


def _classify(text: str, i: int) -> tuple[str, re.Match[str] | None]:
    """What starts at `i`: an escaped identifier, a block or line comment, a raw, interpolated or plain string, a character literal, or code.
    The order is the lexer's: each delimiter is meaningful only in code, and the first that matches wins. The match is returned for the
    kinds that carry one (a raw string's `#` count, a character literal's extent)."""
    c = text[i]
    if c == "«":
        return "escaped", None
    if text.startswith("/-", i):
        return "block", None
    if text.startswith("--", i):
        return "line", None
    after_ident = i > 0 and bool(_IDENT.match(text[i - 1]))
    if c == "r" and not after_ident and (m := _RAW_OPEN.match(text, i)):
        return "raw", m
    if c == '"':
        return ("interpolated" if _is_interpolated_quote(text, i) else "string"), None
    if c == "'" and not after_ident and (m := _CHAR.match(text, i)):
        return "char", m
    return "code", None


def _token_end(text: str, i: int, kind: str, m: re.Match[str] | None) -> int:
    """The index just past the token of `kind` that starts at `i` (anything but code)."""
    if kind == "escaped":
        return _skip_escaped(text, i)
    if kind == "block":
        return _skip_block_comment(text, i)
    if kind == "line":
        return _skip_line_comment(text, i)
    if kind == "raw":
        return min(len(text), _raw_close(text, m) + len('"' + m.group(1)))
    if kind == "interpolated":
        return _interpolated(text, i)[1]
    if kind == "string":
        return _string_close(text, i) + 1
    return m.end()


def _hole_end(text: str, j: int) -> int:
    """The index just past the `}` that closes the interpolation hole whose `{` is at `j`. Braces count only in code:
    strings (interpolated ones included), character literals and comments inside the hole are stepped over whole."""
    depth, k, n = 1, j + 1, len(text)
    while k < n and depth:
        kind, m = _classify(text, k)
        if kind == "code":
            depth += {"{": 1, "}": -1}.get(text[k], 0)
            k += 1
        else:
            k = _token_end(text, k, kind, m)
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


def _emit(text: str, i: int, kind: str, m: re.Match[str] | None, out: list[str]) -> int:
    """Append what the token of `kind` at `i` leaves in the result, and return the index after it."""
    if kind == "interpolated":  # s!"…{e}…": the holes are code (lexed once: it can nest)
        replacement, end = _interpolated(text, i)
        out.append(replacement)
        return end
    end = _token_end(text, i, kind, m) if kind != "code" else i + 1
    if kind == "escaped":  # a name, whatever it contains (--, /-, braces, quotes)
        out.append(text[i:end])
    elif kind == "block":  # only the line breaks stay
        out.append("\n" * text.count("\n", i, end))
    elif kind == "raw":  # delimiters kept: columns stay put
        close = '"' + m.group(1)
        out.append(text[i : m.end()] + _blank(text[m.end() : _raw_close(text, m)]) + close)
    elif kind == "string":
        out.append('"' + _blank(text[i + 1 : min(_string_close(text, i), len(text))]) + '"')
    elif kind == "char":
        out.append("' '")
    elif kind == "code":
        out.append(text[i])
    return end


def code_only(text: str) -> str:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        kind, m = _classify(text, i)
        i = _emit(text, i, kind, m, out)
    return "".join(out)
