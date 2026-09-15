#!/usr/bin/env python3
"""queue_comment.py <build log> <run url> — explain a merge-queue failure to its authors.
Finds the PRs in the merge group from the merge commits, quotes the first Lean
error with file:line:col, the source line and the record it came from, adds a
hint keyed on the error class, and posts one comment per PR."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

from _git import ROOT, run

log_path, run_url = sys.argv[1], sys.argv[2]
log = Path(log_path).read_text(errors="replace") if Path(log_path).exists() else ""
HINTS = [
    (
        r"unknown (identifier|constant)",
        "That name does not exist in the tree at this commit. Check the spelling, or put the definition it needs into `context` (the generator supplies no imports).",
    ),
    (
        r"failed to synthesize",
        "An instance is missing where the statement is compiled. The generator supplies no `variable`/`open`/`instance` lines beyond the record's `context`; copy the ones the source file relies on into `context`.",
    ),
    (
        r"type mismatch",
        "The statement and the proof disagree about a type. Compare the elaborated types in the error; a coercion (`↑`, `Nat.cast`) is the usual fix.",
    ),
    (
        r"unsolved goals",
        "The proof ends before every goal is closed. Run it locally with `lake build <module>` and finish the goals listed.",
    ),
    (r"declaration uses .sorry.|sorryAx", "Trusted content cannot contain `sorry`. Complete the proof or leave the record in tentative."),
    (
        r"\(deterministic\) timeout|maximum recursion depth",
        "The proof exceeds the default heartbeat/recursion budget. Simplify it or add an allowed `set_option maxHeartbeats` in `context` (see schemas/allowed-options.json).",
    ),
    (r"axiom", "A non-standard axiom is not allowed in trusted content. Only propext, Classical.choice and Quot.sound are accepted."),
    (
        r"forbidden|content lint",
        "The content lint rejected a construct that runs or links code. See scripts/ci/lint_banked.py for the list.",
    ),
    (
        r"regenerat",
        "A derived file differs from what the generator produces. Do not edit Tengoku/<Library>/** by hand; change the records instead.",
    ),
]
m = re.search(r"^(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+): error: (?P<msg>.*)$", log, re.M)
if m:
    f, line, col, msg = m.group("file"), int(m.group("line")), m.group("col"), m.group("msg").strip()
    src = ""
    p = ROOT / f
    if p.exists():
        lines = p.read_text(errors="replace").splitlines()
        src = lines[line - 1].strip() if line - 1 < len(lines) else ""
        record = next(
            (
                re.sub(r"^.*?(theorem|lemma|def|abbrev|instance)\s+(\S+).*$", r"\2", l)
                for l in reversed(lines[:line])
                if re.match(r"^\s*(theorem|lemma|def|abbrev|instance)\s", l)
            ),
            "?",
        )
    else:
        record = "?"
    where = f"`{f}:{line}:{col}`"
    detail = f"**{msg}**\n\n```lean\n{src}\n```\nRecord: `{record}`"
else:
    err = re.search(r"^(error|FAIL|::error::)(.*)$", log, re.M)
    where, detail, msg = "the build log", f"**{(err.group(0) if err else 'see the log')[:300]}**", (err.group(0) if err else "")
hint = next(
    (h for pat, h in HINTS if re.search(pat, msg, re.I)),
    "Reproduce locally with the commands in CONTRIBUTING.md, fix, push, and the PR re-enters the queue.",
)
body = f"""### Removed from the merge queue

The queue build failed at {where}.

{detail}

**What to do:** {hint}

Full log: {run_url}

Re-queue after fixing (`gh pr merge --queue`, or the *Merge when ready* button). This message is generated; an AI reviewer will add more context later."""
prs = sorted({n for n in re.findall(r"Merge pull request #(\d+)", run("log", "--format=%s", "-n", "50"))})
if not prs:
    print(body)
    sys.exit(0)
for n in prs:
    subprocess.run(["gh", "pr", "comment", n, "--body", body], check=False)
    print(f"commented on #{n}")
