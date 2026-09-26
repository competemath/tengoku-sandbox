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
