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


def _hole_end(text: str, j: int) -> int:
    """The index just past the `}` that closes the interpolation hole whose `{` is at `j`. Braces count only in code:
    strings (interpolated ones included), character literals and comments inside the hole are stepped over whole."""
    depth, k, n = 1, j + 1, len(text)
    while k < n and depth:
        prev_ident = bool(_IDENT.match(text[k - 1]))
        if text.startswith("/-", k):
            d, k = 1, k + 2
            while k < n and d:
                if text.startswith("/-", k):
                    d, k = d + 1, k + 2
                elif text.startswith("-/", k):
                    d, k = d - 1, k + 2
                else:
                    k += 1
        elif text.startswith("--", k):
            nl = text.find("\n", k)
            k = n if nl < 0 else nl
        elif text[k] == '"' and k >= 2 and text[k - 1] == "!" and _IDENT.match(text[k - 2]):
            _, k = _interpolated(text, k)
        elif text[k] == '"':
            k += 1
            while k < n and text[k] != '"':
                k += 2 if text[k] == "\\" else 1
            k += 1
        elif text[k] == "'" and not prev_ident and (m := _CHAR.match(text, k)):
            k = m.end()
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
            out.append("{" + code_only(text[j + 1 : k - 1]) + "}")
            j = k
        else:
            out.append("\n" if text[j] == "\n" else " ")
            j += 1
    out.append('"')
    return "".join(out), j + 1


def code_only(text: str) -> str:
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth:  # inside a block comment: only nested delimiters and line breaks matter
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        c = text[i]
        prev_ident = i > 0 and bool(_IDENT.match(text[i - 1]))
        if text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif c == "r" and not prev_ident and (m := _RAW_OPEN.match(text, i)):
            close = '"' + m.group(1)
            j = text.find(close, m.end())
            j = n if j < 0 else j
            out.append(text[i : m.end()] + _blank(text[m.end() : j]) + close)  # delimiters kept: columns stay put
            i = j + len(close)
        elif c == '"' and i >= 2 and text[i - 1] == "!" and _IDENT.match(text[i - 2]):
            s, i = _interpolated(text, i)  # s!"…{e}…": the holes are code
            out.append(s)
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('"' + _blank(text[i + 1 : min(j, n)]) + '"')
            i = j + 1
        elif c == "'" and not prev_ident and (m := _CHAR.match(text, i)):
            out.append("' '")
            i = m.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)
