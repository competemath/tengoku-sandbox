#!/usr/bin/env python3
"""queue_comment.py — explain a merge-queue failure to its authors.

    queue_comment.py <build log> <run url> [<base sha>]          extract, render and post in one go (the earlier use, and the tests')
    queue_comment.py --facts OUT.json <build log> <run url> [<base sha>]    only extract the facts (no token, no posting)
    queue_comment.py --post FACTS.json                                      validate the facts, render the comment, post it

The failure is read in the job that built the group's code, which holds no write token: that job only writes the facts (the
first Lean error with file:line:col, the source line and the record it came from, the PRs of the merge group). The job that
may write runs main's copy of this script on the facts, as data: it accepts only what has the right shape, cuts every text
to a length, and cannot be made to close a code fence or name a PR that is not a number. The comment says what failed, a
hint keyed on the error class, and where to read more; one comment per PR."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.parse
from pathlib import Path

from _git import ROOT, fail, run

PR_NUMBER = re.compile(r"\d{1,9}", re.ASCII)  # ASCII only: \d alone also matches other scripts' digits
DECL = re.compile(r"\s*(?:theorem|lemma|def|abbrev|instance)\s+(\S+)")
REQUEUE = "{requeue}"  # filled in when the comment is posted
RECORD_NAME = re.compile(r"[\w.'«»!?]{1,200}")
LIMITS = {"msg": 1500, "src": 300, "where": 200, "err": 300, "file": 200}

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


def fence_safe(text: str) -> str:
    """Text that sits inside a code fence of ours and cannot close it."""
    return text.replace("```", "'''")


def cut(value: object, key: str) -> str:
    return str(value if value is not None else "")[: LIMITS[key]]


def lean_error(log: str) -> re.Match | None:
    # lake prints `error: <file>:<line>:<col>: <msg>`; lean alone prints `<file>:<line>:<col>: error: <msg>`.
    return re.search(r"^(?:error: )?(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):(?: error:)? (?P<msg>.*)$", log, re.M)


def message_with_tail(log: str, m: re.Match) -> str:
    # lean continues a message on indented lines ("Tactic `decide` proved that the proposition\n  1 + 1 = 3\nis false")
    msg, tail = m.group("msg").strip(), []
    for extra in log[m.end() :].splitlines()[1:8]:
        if re.match(r"^(Some required targets|error|warning|info|✖|✔|\[|trace)", extra):
            break
        if not (extra.startswith((" ", "\t")) or tail):
            break
        tail.append(extra.rstrip())
    return msg + ("\n" + "\n".join(tail) if tail else "")


def source_of(path: str, line: int) -> tuple[str, str]:
    """The source line of the error and the declaration it sits in, read from the working tree (only from inside it)."""
    p = (ROOT / path).resolve()
    if not p.is_relative_to(ROOT.resolve()) or not p.is_file():
        return "", "?"
    lines = p.read_text(errors="replace").splitlines()
    src = lines[line - 1].strip() if line - 1 < len(lines) else ""
    decl = next((m.group(1) for ln in reversed(lines[:line]) if (m := DECL.match(ln))), "?")
    return src, decl


def group_prs(base_sha: str) -> list[str]:
    subjects = (
        run("log", "--format=%s", f"{base_sha}..HEAD", check=False) if base_sha else run("log", "--format=%s", "-n", "50", check=False)
    )
    return sorted(set(re.findall(r"(?:Merge pull request #|\(#)(\d+)\)?\s*$", subjects, re.M)), key=int)


def extract(log: str, run_url: str, base_sha: str) -> dict:
    """What the log and the working tree say about the failure, as strings and numbers only."""
    facts: dict = {"run_url": run_url, "prs": group_prs(base_sha), "stat": [], "kind": "log"}
    m = lean_error(log)
    if m:
        src, record = source_of(m.group("file"), int(m.group("line")))
        facts |= {
            "kind": "lean",
            "file": m.group("file"),
            "line": int(m.group("line")),
            "col": m.group("col"),
            "msg": message_with_tail(log, m),
        }
        facts |= {"src": src, "record": record}
        return facts
    err = re.search(r"^(error|FAIL|::error::)(.*)$", log, re.M)
    facts |= {
        "err": err.group(0) if err else "",
        "stat": re.findall(r"^ (\S+\.lean)\s+\|", log, re.M)[:10],
    }  # `git diff --stat` lines of the regeneration check
    return facts


def as_list(value: object) -> list:
    return value if isinstance(value, list) else []


def valid(facts: dict) -> dict:
    """The facts as data: shapes checked, lengths cut, the PR list digits only. Anything else is dropped, never repaired."""
    prs = [str(n) for n in as_list(facts.get("prs")) if PR_NUMBER.fullmatch(str(n))][:20]
    out = {"kind": "lean" if facts.get("kind") == "lean" else "log", "prs": prs, "run_url": cut(facts.get("run_url"), "where")}
    out["stat"] = [cut(f, "file") for f in as_list(facts.get("stat"))[:10] if re.fullmatch(r"[\w./-]{1,200}", str(f))]
    out |= {k: cut(facts.get(k), k) for k in ("msg", "src", "err")}
    out["file"] = cut(facts.get("file"), "file") if re.fullmatch(r"[\w./+-]{1,200}", str(facts.get("file", ""))) else "?"
    if not re.fullmatch(r"https://[\w.:/-]{1,190}", out["run_url"]):
        out["run_url"] = "(no link)"
    out["line"] = int(facts["line"]) if str(facts.get("line", "")).isdigit() else 0
    out["col"] = str(facts["col"]) if str(facts.get("col", "")).isdigit() else "0"
    out["record"] = str(facts.get("record")) if RECORD_NAME.fullmatch(str(facts.get("record", ""))) else "?"
    return out


def describe(f: dict) -> tuple[str, str, str]:
    """(where, detail, text to match a hint against)"""
    if f["kind"] == "lean":
        where = f"`{f['file']}:{f['line']}:{f['col']}`"
        detail = f"```text\n{fence_safe(f['msg'])}\n```\n```lean\n{fence_safe(f['src'])}\n```\nRecord: `{f['record']}`"
        return where, detail, f["msg"]
    where, detail = "the build log", f"```text\n{fence_safe(f['err'] or 'see the log')}\n```"
    if f["stat"]:
        where = "the regeneration check"
        detail += "\n\nFiles that differ from the generator's output:\n" + "\n".join(f"- `{x}`" for x in f["stat"])
    return where, detail, f["err"]


def render(f: dict, strict: bool = False) -> tuple[str, list[str]]:
    """(the comment, with {requeue} left to fill; the PRs to tell). Strict: the PR to tell comes only from the queue ref, never from the facts."""
    where, detail, msg = describe(f)
    hint = next(
        (h for pat, h in HINTS if re.search(pat, msg, re.I)), "Reproduce locally with the commands in CONTRIBUTING.md, fix, and push."
    )
    prs = f["prs"]
    # The entry's own PR is the one GitHub removed (the ref is gh-readonly-queue/<branch>/pr-<N>-<base>); the others
    # named in the group are retried, so only it is labelled and told.
    own = re.search(r"/pr-(\d+)-[0-9a-f]+$", os.environ.get("GITHUB_REF", ""))
    if strict:
        targets = [own.group(1)] if own else []
    else:
        targets = [own.group(1)] if own and own.group(1) in prs else prs
    group_note = (
        f" This group also contained {', '.join('#' + n for n in prs)}; GitHub removes the newest PR and retries the rest, so if the error is not in your files, wait for the retry."
        if len(prs) > 1
        else ""
    )
    link = (
        f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/{os.environ.get('GITHUB_REPOSITORY', '')}/issues/new?"
        + urllib.parse.urlencode(
            {
                "labels": "gate-bug",
                "title": f"queue bug? {where}",
                "body": f"Run: {f['run_url']}\nFailed at: {where}\n\n```\n{fence_safe(msg[:600])}\n```\n\nWhy I think the queue is wrong:\n",
            }
        )
    )
    body = f"""### Removed from the merge queue

The queue build failed at {where}.{group_note}

{detail}

**What to do:** {hint}

Full log: {f["run_url"]}

{{requeue}} This message is generated; an AI reviewer will add more context later.

If your change is right and the queue is not (candidate generation, the axiom scan and the regeneration diff are the complex parts): **[Report a gate bug]({link})** — a maintainer looks at every one."""
    return body, targets


AUTO = "Push the fix and the PR goes back into the queue by itself once its checks pass (the `ejected` label does that; remove it to stop)."
MANUAL = "Re-queue after fixing (`gh pr merge --auto`, or the *Merge when ready* button)."


def post(body: str, targets: list[str]) -> None:
    # The label puts the PR back into the queue on its next push (.github/workflows/rearm.yml): leaving the queue turns
    # "merge when ready" off, and an outside contributor rarely thinks to press it again. Without the bot's token
    # rearm.yml cannot, so the PR is not labelled and the author is asked to re-queue by hand.
    rearm = os.environ.get("TENGOKU_REARM") == "1"
    gh_label = [
        "gh",
        "label",
        "create",
        "ejected",
        "--color",
        "d93f0b",
        "--description",
        "Left the merge queue; the next push re-queues it",
    ]
    subprocess.run(gh_label, check=False, capture_output=True)
    for n in targets:
        # the promise of an automatic re-queue only where the label that makes it happen is really on the PR
        labelled = (
            rearm and subprocess.run(["gh", "pr", "edit", n, "--add-label", "ejected"], check=False, capture_output=True).returncode == 0
        )
        r = subprocess.run(
            ["gh", "pr", "comment", n, "--body", body.replace(REQUEUE, AUTO if labelled else MANUAL)],
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


def announce(facts: dict, strict: bool = False) -> None:
    body, targets = render(valid(facts), strict)
    # A squash merge group carries one commit per PR, subject "<title> (#N)"; a merge-commit group says "Merge pull request #N".
    if not targets:
        print(body.replace(REQUEUE, ""))
        return
    if os.environ.get("TENGOKU_COMMENT_DRY"):  # tests: show what would be posted, post nothing
        print("would comment on:", ", ".join("#" + n for n in targets))
        print(body.replace(REQUEUE, "AUTO re-queue" if os.environ.get("TENGOKU_REARM") == "1" else "MANUAL re-queue"))
        return
    post(body, targets)


def checked_path(arg: str) -> Path:
    """A file given on the command line: it must lie in the working directory or the temporary directory."""
    p = Path(arg).resolve()
    if not any(p.is_relative_to(root.resolve()) for root in (Path.cwd(), Path(tempfile.gettempdir()))):
        fail(f"{arg} is outside the working directory and the temporary directory")
    return p


def main(argv: list[str]) -> None:
    if argv[:1] == ["--post"]:
        announce(json.loads(checked_path(argv[1]).read_text(errors="replace")), strict=True)
        return
    out = None
    if argv[:1] == ["--facts"]:
        out, argv = checked_path(argv[1]), argv[2:]
    log_path = checked_path(argv[0])
    facts = extract(log_path.read_text(errors="replace") if log_path.exists() else "", argv[1], argv[2] if len(argv) > 2 else "")
    if out:
        out.write_text(json.dumps(facts, ensure_ascii=False))
    else:
        announce(facts)


if __name__ == "__main__":
    main(sys.argv[1:])
