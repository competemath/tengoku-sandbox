#!/usr/bin/env python3
"""_git.plain and _git.annotation: they make text from a PR (a record name, a file, an error) safe to print in a
workflow log, where a line starting with `::` is a command to the runner (::add-mask::, ::stop-commands::, …).

Properties, for any text:
  plain(text)       holds no `::` at all and no CR, so no line of it can start a command
  annotation(text)  holds no line break, and the runner's decoding gives back exactly the text
"""

from __future__ import annotations

from _harness import instrumenting, main

with instrumenting():
    import _git

COVERS = ["scripts/ci/_git.py"]
RUNS = 200_000


def unescape(s: str) -> str:
    """How the Actions runner decodes a command's message (%0D, %0A, then %25)."""
    return s.replace("%0D", "\r").replace("%0A", "\n").replace("%25", "%")


def TestOneInput(data: bytes) -> None:
    text = data.decode("utf-8", "replace")
    out = _git.plain(text)
    assert "::" not in out and "\r" not in out, f"plain({text!r}) = {out!r}"
    enc = _git.annotation(text)
    assert "\n" not in enc and "\r" not in enc, f"annotation({text!r}) = {enc!r}"
    assert unescape(enc) == text, f"annotation({text!r}) = {enc!r} decodes to {unescape(enc)!r}"


if __name__ == "__main__":
    main(TestOneInput)
