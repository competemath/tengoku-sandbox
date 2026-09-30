#!/usr/bin/env python3
"""lean_lex.code_only and what reads it (_git.declared_names, _git.unplaced): every text check of the gate sees
a record's Lean through code_only, and the queue matches records to modules with declared_names.

Properties, for any text: none of them raises, and code_only keeps every line break (the checks report line
numbers of the original text).
"""

from __future__ import annotations

from _harness import instrumenting, main

with instrumenting():
    import _git
    import lean_lex

COVERS = ["scripts/ci/lean_lex.py", "scripts/ci/_git.py"]
RUNS = 50_000  # ~1,500 a second on a GitHub runner


def TestOneInput(data: bytes) -> None:
    text = data.decode("utf-8", "replace")
    code = lean_lex.code_only(text)
    assert code.count("\n") == text.count("\n"), f"code_only({text!r}) = {code!r} lost or added a line"
    _git.declared_names(text)
    _git.unplaced({"Lib.thm", "thm"}, [text])


if __name__ == "__main__":
    main(TestOneInput)
