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


def _interpolated(text: str, i: int) -> tuple[str, int]:
    """An interpolated string (`s!"…{e}…"`, `m!`, `f!`…) from its opening quote at `i`: the literal text blanked, each
    `{…}` hole kept as code (lexed in turn, so a string or comment inside a hole is handled too). Returns the
    replacement and the index after the closing quote."""
    out, j, n = ['"'], i + 1, len(text)
    while j < n and text[j] != '"':
        if text[j] == "\\":
            out.append(_blank(text[j : j + 2]))
            j += 2
        elif text[j] == "{":
            depth, k = 1, j + 1
            while k < n and depth:
                if text[k] == '"':  # a string inside the hole: skip it whole
                    k += 1
                    while k < n and text[k] != '"':
                        k += 2 if text[k] == "\\" else 1
                depth += {"{": 1, "}": -1}.get(text[k], 0) if k < n else 0
                k += 1
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
