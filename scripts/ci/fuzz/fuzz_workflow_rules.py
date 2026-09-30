#!/usr/bin/env python3
"""workflow_rules.py, which reads the workflow and action files a PR adds or changes.

Properties, for any file: the checker never raises, and what it prints for a finding cannot start a workflow
command: the `::error` annotation is one line, and no line of the readable form starts with `::`.

An input is the file's text; the repository's own workflows are seeds. An input of odd length is read as an
action (action.yml), even as a workflow.
"""

from __future__ import annotations

import re

from _harness import instrumenting, main

with instrumenting():
    import workflow_rules as wr

COVERS = ["scripts/ci/workflow_rules.py", "scripts/ci/_git.py"]
RUNS = 20_000
SEEDS = [".github/workflows"]


def TestOneInput(data: bytes) -> None:
    path = ".github/actions/a/action.yml" if len(data) % 2 else ".github/workflows/t.yml"
    checker = wr.Checker(path, data.decode("utf-8", "replace")).run()
    for finding in checker.findings:
        readable, annotation = wr.report(*finding)
        assert not re.search(r"(?m)^\s*::", readable) and "\r" not in readable, f"{finding!r} prints {readable!r}"
        assert annotation.startswith("::error ") and not re.search(r"[\r\n]", annotation), f"{finding!r} annotates {annotation!r}"


if __name__ == "__main__":
    main(TestOneInput)
