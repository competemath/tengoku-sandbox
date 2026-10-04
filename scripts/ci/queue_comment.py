#!/usr/bin/env python3
"""queue_comment.py <build log> <run url> — explain a merge-queue failure to its authors.
Finds the PRs in the merge group from the merge commits, quotes the first Lean
error with file:line:col, the source line and the record it came from, adds a
hint keyed on the error class, and posts one comment per PR."""

from __future__ import annotations

import os
import re
import subprocess
import sys
import urllib.parse
from pathlib import Path

from _git import ROOT, run

log_path, run_url = sys.argv[1], sys.argv[2]
base_sha = sys.argv[3] if len(sys.argv) > 3 else ""  # the merge group's base: its commits name the PRs
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
    (
        r"axiom|allowed: propext|_native\.decide|ofReduceBool",
        "A non-standard axiom is not allowed in trusted content (native_decide / decide +native introduce one). Only propext, Classical.choice and Quot.sound are accepted.",
    ),
    (
        r"forbidden|content lint",
        "The content lint rejected a construct that runs or links code. See scripts/ci/lint_banked.py for the list.",
    ),
    (
        r"regenerat",
        "A derived file differs from what the generator produces. Do not edit Tengoku/<Library>/** by hand; change the records instead.",
    ),
]
# lake prints `error: <file>:<line>:<col>: <msg>`; lean alone prints `<file>:<line>:<col>: error: <msg>`.
m = re.search(r"^(?:error: )?(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):(?: error:)? (?P<msg>.*)$", log, re.M)
if m:
    f, line, col, msg = m.group("file"), int(m.group("line")), m.group("col"), m.group("msg").strip()
    # lean continues a message on indented lines ("Tactic `decide` proved that the proposition\n  1 + 1 = 3\nis false")
    tail = []
    for extra in log[m.end() :].splitlines()[1:8]:
        if re.match(r"^(Some required targets|error|warning|info|✖|✔|\[|trace)", extra):
            break
        if extra.startswith((" ", "\t")) or tail:
            tail.append(extra.rstrip())
        else:
            break
    if tail:
        msg = msg + "\n" + "\n".join(tail)
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
    detail = f"```text\n{msg}\n```\n```lean\n{src}\n```\nRecord: `{record}`"
else:
    err = re.search(r"^(error|FAIL|::error::)(.*)$", log, re.M)
    where, detail, msg = "the build log", f"**{(err.group(0) if err else 'see the log')[:300]}**", (err.group(0) if err else "")
    stat = re.findall(r"^ (\S+\.lean)\s+\|", log, re.M)  # `git diff --stat` lines from the regeneration check
    if stat:
        where = "the regeneration check"
        detail += "\n\nFiles that differ from the generator's output:\n" + "\n".join(f"- `{f}`" for f in stat[:10])
hint = next(
    (h for pat, h in HINTS if re.search(pat, msg, re.I)),
    "Reproduce locally with the commands in CONTRIBUTING.md, fix, and push.",
)
subjects = run("log", "--format=%s", f"{base_sha}..HEAD") if base_sha else run("log", "--format=%s", "-n", "50")
prs = sorted({n for n in re.findall(r"(?:Merge pull request #|\(#)(\d+)\)?\s*$", subjects, re.M)}, key=int)
# The entry's own PR is the one GitHub removed (the ref is gh-readonly-queue/<branch>/pr-<N>-<base>); the others
# named in the group are retried, so only it is labelled and told.
own = re.search(r"/pr-(\d+)-[0-9a-f]+$", os.environ.get("GITHUB_REF", ""))
targets = [own.group(1)] if own and own.group(1) in prs else prs
group_note = (
    f" This group also contained {', '.join('#' + n for n in prs)}; GitHub removes the newest PR and retries the rest, so if the error is not in your files, wait for the retry."
    if len(prs) > 1
    else ""
)
_repo = os.environ.get("GITHUB_REPOSITORY", "")
_server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
issue_link = f"{_server}/{_repo}/issues/new?" + urllib.parse.urlencode(
    {
        "labels": "gate-bug",
        "title": f"queue bug? {where}",
        "body": f"Run: {run_url}\nFailed at: {where}\n\n```\n{msg[:600]}\n```\n\nWhy I think the queue is wrong:\n",
    }
)
body = f"""### Removed from the merge queue

The queue build failed at {where}.{group_note}

{detail}

**What to do:** {hint}

Full log: {run_url}

{{requeue}} This message is generated; an AI reviewer will add more context later.

If your change is right and the queue is not (candidate generation, the axiom scan and the regeneration diff are the complex parts): **[Report a gate bug]({issue_link})** — a maintainer looks at every one."""
# A squash merge group carries one commit per PR, subject "<title> (#N)"; a merge-commit group says "Merge pull request #N".
if not prs:
    print(body.replace("{requeue}", ""))
    sys.exit(0)
if os.environ.get("TENGOKU_COMMENT_DRY"):  # tests: show what would be posted, post nothing
    print("would comment on:", ", ".join("#" + n for n in targets))
    print(body.replace("{requeue}", "AUTO re-queue" if os.environ.get("TENGOKU_REARM") == "1" else "MANUAL re-queue"))
    sys.exit(0)
# The label puts the PR back into the queue on its next push (.github/workflows/rearm.yml): leaving the queue turns
# "merge when ready" off, and an outside contributor rarely thinks to press it again. Without the bot's token
# rearm.yml cannot, so the PR is not labelled and the author is asked to re-queue by hand.
rearm = os.environ.get("TENGOKU_REARM") == "1"
subprocess.run(
    ["gh", "label", "create", "ejected", "--color", "d93f0b", "--description", "Left the merge queue; the next push re-queues it"],
    check=False,
    capture_output=True,
)
AUTO = "Push the fix and the PR goes back into the queue by itself once its checks pass (the `ejected` label does that; remove it to stop)."
MANUAL = "Re-queue after fixing (`gh pr merge --auto`, or the *Merge when ready* button)."
for n in targets:
    # the promise of an automatic re-queue only where the label that makes it happen is really on the PR
    labelled = rearm and subprocess.run(["gh", "pr", "edit", n, "--add-label", "ejected"], check=False, capture_output=True).returncode == 0
    r = subprocess.run(
        ["gh", "pr", "comment", n, "--body", body.replace("{requeue}", AUTO if labelled else MANUAL)],
        check=False,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        print(f"could not comment on #{n}: {r.stderr.strip()[:200]}")
        if labelled:  # no re-queue the author was never told about
            subprocess.run(["gh", "pr", "edit", n, "--remove-label", "ejected"], check=False, capture_output=True)
        continue
    print(f"commented on #{n}" + ("" if labelled else " (no ejected label: asked to re-queue by hand)"))
