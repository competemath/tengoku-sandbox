#!/usr/bin/env python3
"""validate_records.py and lint_banked.py, which read every line a PR adds to data/.

Property, for any added lines: each script passes, or fails with its own message (_git.fail, exit 1); never with
a traceback, whatever the line holds (not JSON, not an object, a field of the wrong type, …).

An input is `<path>\\n<line>\\n<line>…`: the file the lines are added to (data/<tier>/<library>….jsonl; anything
else stands for data/staging/mathlib.jsonl) and the lines. The scripts run against the real schemas and a small
trusted file, with git replaced by the input.
"""

from __future__ import annotations

import contextlib
import io
import json
import shutil
import sys
import tempfile
from pathlib import Path

from _harness import ROOT, code_of, instrumenting, main

with instrumenting():
    import _git

    SCRIPTS = [("validate_records.py", code_of("validate_records")), ("lint_banked.py", code_of("lint_banked"))]

COVERS = [
    "scripts/ci/validate_records.py",
    "scripts/ci/lint_banked.py",
    "scripts/ci/_git.py",
    "schemas/record.schema.json",
    "schemas/sources.json",
    "schemas/allowed-options.json",
]
RUNS = 20_000  # ~1,700 a second on a GitHub runner

TREE = Path(tempfile.mkdtemp(prefix="fuzz-records-"))
shutil.copytree(ROOT / "schemas", TREE / "schemas")
(TREE / "data" / "trusted").mkdir(parents=True)
(TREE / "data" / "trusted" / "mathlib.jsonl").write_text(
    json.dumps({"name": "Known.thm", "statement": "theorem Known.thm : True", "status": "trusted", "library": "mathlib"})
    + "\n"
    + json.dumps({"tombstone": "Known.gone", "category": "duplicate", "reason": "r", "at": "2026-01-01"})
    + "\n"
)
PATCHED = ("ROOT", "changed_files", "added_lines", "blob")


def TestOneInput(data: bytes) -> None:
    path, _, rest = data.decode("utf-8", "replace").partition("\n")
    if not (path.startswith("data/") and path.endswith(".jsonl")) or ".." in path:
        path = "data/staging/mathlib.jsonl"
    lines = rest.split("\n")
    saved, argv = {k: getattr(_git, k) for k in PATCHED}, sys.argv
    _git.ROOT = TREE
    _git.changed_files = lambda base, head: [("A", path)]
    _git.added_lines = lambda base, head, p: list(enumerate(lines, 1)) if p == path else []
    _git.blob = lambda rev, p: rest.encode() if p == path else None
    try:
        for name, code in SCRIPTS:
            sys.argv = [name, "base", "head"]
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    exec(code, {"__name__": "__main__", "__file__": name})  # noqa: S102 — the gate script itself
            except SystemExit as e:
                assert e.code in (None, 0, 1), f"{name} exited {e.code!r}"
    finally:  # the unit tests import this target next to the other gate tests
        for k, v in saved.items():
            setattr(_git, k, v)
        sys.argv = argv


if __name__ == "__main__":
    main(TestOneInput)
