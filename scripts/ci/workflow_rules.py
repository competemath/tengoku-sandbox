#!/usr/bin/env python3
"""workflow_rules.py — the rules every GitHub Actions workflow in this repository follows.

The pr-gate `workflows` job runs main's copy of this script on the workflow files a PR adds or changes,
read from the PR's commit as data. The rules:

  pinned       every `uses:` names a full 40-character commit, with the tag it was taken from as a comment
               (`uses: actions/checkout@11d5…77262 # v4`). A tag can be moved to new code by whoever controls
               the action. Self-repository `$/<path>` and local `./` actions and digest-pinned images pass.
  token        every actions/checkout sets `persist-credentials: false`. No job pushes with git (`gh` reads
               GH_TOKEN), and a token left in the checkout is readable by anything the job runs, a Lean build included.
  permissions  every workflow starts with `permissions: {}` and each job grants its own; never write-all or read-all.
  expressions  no `${{ }}` inside `run:` or github-script's `script:` whose value can carry text: a context goes in
               only if its shape is fixed (a number, a commit, the repository's name, …) or it is only compared.
               Pass anything else through `env:` and quote it as "$VAR".
  pr-code      a pull_request_target or workflow_run workflow runs with the repository's token, so it never checks
               out the PR's code (actions/checkout, `gh pr checkout`), applies no patch (`git apply`, `patch`), no git
               command puts the PR's files in the tree or runs them, and local actions use `$/<path>`: a `./` action is loaded from the workspace, which may hold
               the PR's files. The one exception is `git checkout <pr> -- data…`: the PR's records, as data.

  write-and-pr a job of a pull_request_target, workflow_run or merge_group workflow that holds a write permission never reads the PR's
               (or the queue entry's) commits: no `git fetch`/`checkout`/`merge`/... of a name that can carry them (a ref, `$HEAD`, any
               env var built from a context outside the base side), no actions/checkout of them, and in a merge_group workflow an
               actions/checkout always names its `ref` (the default is the queue entry). Reading untrusted data and holding a token that
               can write are split over two jobs, and the one that writes takes only validated outputs. Without this, a later step that
               ever ran a file of the PR would hold the token.

  cancelable   in a workflow whose runs a newer run cancels (`concurrency: cancel-in-progress`), no job runs on `always()`: a cancelled run would still run it, and what it
               reports (a failure, for an aggregating required check) outlives the run and blocks the commit after the newer run has passed. `!cancelled()` runs after
               failed jobs as `always()` does, and is skipped in a cancelled run.

  --online     genuine pins: the tag named in the comment contains the commit. A repository shares commits with
               all its forks, so a pin can name a commit that exists only in an attacker's fork (an impostor commit).

Usage:
  workflow_rules.py [--online] PATH...                files, or directories searched for *.yml and *.yaml
  workflow_rules.py [--online] --changed BASE HEAD    the workflow and action files BASE...HEAD adds or changes, read from HEAD
"""

from __future__ import annotations

import os
import re
import shlex
import subprocess
import sys
import urllib.parse
from pathlib import Path

import yaml
from _git import annotation, plain

LINE = "__line__"
SHA = re.compile(r"[0-9a-f]{40}")
USES_LINE = re.compile(r"""^\s*(?:-\s+)?uses:\s*["']?([^\s"'#]+)["']?\s*(?:#\s*(\S+))?""")
EXPR = re.compile(r"\$\{\{(.*?)\}\}", re.S)
ALWAYS_CALL = re.compile(r"\balways\s*\(")
EXPR_OPERATOR = re.compile(r"&&|\|\||[=!<>]=|[<>!(),\[\].*]")
EXPR_WORD = re.compile(r"[A-Za-z_][\w-]*|\d+(?:\.\d+)?")
UNKNOWN = frozenset({True, False})
# what a call is on a cancelled run: `always()` and `cancelled()` are true, `success()` and `failure()` false, any other call or context is unknown
STATUS_ON_CANCELLED = {
    "always": frozenset({True}),
    "cancelled": frozenset({True}),
    "success": frozenset({False}),
    "failure": frozenset({False}),
}
LITERALS = {"true": frozenset({True}), "false": frozenset({False}), "null": frozenset({False})}
STRING = r"'(?:[^']|'')*'"
EXPR_TOKENS = (EXPR_OPERATOR, re.compile(STRING), EXPR_WORD)
NAME = r"[A-Za-z_][\w-]*(?:\.[\w*-]+|\[[^\]]*\])*"
OPERAND = rf"(?:{STRING}|{NAME}|-?\d+(?:\.\d+)?)"
COMPARISON = re.compile(rf"{OPERAND}\s*(?:==|!=|<=|>=|<|>)\s*{OPERAND}")
NEGATION = re.compile(rf"!\s*{NAME}")
BOOLEAN_CALL = re.compile(r"\b(?:contains|startsWith|endsWith|hashFiles|success|failure|always|cancelled)\s*\(")
REFERENCE = re.compile(rf"(?<![\w.'])({NAME})(\s*\()?")
# contexts whose value has a fixed shape: nothing in them can be read by a shell as code
FIXED = re.compile(
    r"""^(?:github\.(?:sha|run_id|run_number|run_attempt|repository|repository_owner|server_url|api_url|workspace|event_name|job
                      |event\.(?:number|pull_request\.number|pull_request\.(?:base|head)\.sha|merge_group\.(?:base|head)_sha))
          |runner\.(?:os|arch|temp)|job\.status|steps\.[\w-]+\.(?:outcome|conclusion)|needs\.[\w-]+\.result|strategy\.job-(?:index|total))$""",
    re.X,
)
SELF = "scripts/ci/workflow_rules.py"
PRIVILEGED = {"pull_request_target", "workflow_run"}
UNTRUSTED_REF = re.compile(
    r"PR_REF|refs/pull|head_ref|pull_request\.head|merge_group\.head"
)  # what names the PR's or the queue entry's commits
# what a checkout in a privileged workflow may name: the base side only
BASE_SIDE = {
    "github.event.pull_request.base.sha",
    "github.event.pull_request.base.ref",
    "github.base_ref",
    "github.event.merge_group.base_sha",
    "github.sha",
    "github.ref",
    "github.workflow_sha",  # the commit of the workflow file itself: the base branch's
    "github.event.repository.default_branch",
}
# What reads a commit into the workspace or out of it. In a job that can write, none of it may touch the PR's or the queue entry's commits.
GIT_VERBS = (
    *("fetch", "pull", "clone", "checkout", "switch", "merge", "cherry-pick", "worktree", "read-tree", "restore", "archive", "apply", "am"),
    *("show", "cat-file", "ls-tree", "log", "diff", "rev-list", "checkout-index", "submodule"),
)
GIT_READS = re.compile(r"\bgit(?:\s+-[Cc]\s+\S+)*\s+(?:" + "|".join(GIT_VERBS) + r")\b")
# In a merge_group event the workflow's own commit and ref are the queue entry (the PR merged onto the base), not the base side.
ENTRY_CONTEXTS = {"github.sha", "github.ref", "github.ref_name", "github.workflow_sha"}
ENTRY_VARS = re.compile(r"\$\{?(?:GITHUB_SHA|GITHUB_REF|GITHUB_REF_NAME|GITHUB_WORKFLOW_SHA)\b")
HEAD_VARS = re.compile(r"\$\{?GITHUB_HEAD_REF\b")  # the PR's branch, for any trigger


def base_side(on: set[str]) -> set[str]:
    """The contexts that name the base of the change under this workflow's triggers."""
    return BASE_SIDE - ENTRY_CONTEXTS if "merge_group" in on else BASE_SIDE


def untrusted_names(allowed: set[str], *envs: object) -> set[str]:
    """The env names whose value can name the PR's or the queue entry's commits: any context outside the base side."""
    return {
        str(k) for env in envs for k, v in items(env) if any(c not in allowed for m in EXPR.finditer(str(v)) for c in contexts(m.group(1)))
    }


def untrusted_text(text: str, envs: tuple, on: set[str]) -> bool:
    """Can this ref or script name the PR's or the queue entry's commits? By a literal marker, by a context outside the base side
    (for a merge_group event that excludes github.sha and github.ref), or through an env var built from one (`$HEAD`, `$PR_REF`,
    `$GITHUB_SHA` in the queue, whatever a workflow calls it)."""
    resolved = resolve_env(text, *envs)
    allowed = base_side(on)
    if UNTRUSTED_REF.search(resolved) or PR_MARK.search(resolved) or HEAD_VARS.search(resolved):
        return True
    if "merge_group" in on and ENTRY_VARS.search(resolved):
        return True
    if any(c not in allowed for m in EXPR.finditer(resolved) for c in contexts(m.group(1))):
        return True
    return any(re.search(r"\$\{?" + re.escape(n) + r"\b", resolved) for n in untrusted_names(allowed, *envs))


GIT_WRITE = re.compile(
    r"\bgit(?:\s+-[Cc]\s+\S+)*\s+(?:checkout|switch|restore|reset|read-tree|worktree\s+add|merge|pull|cherry-pick|rebase|archive|apply|am|stash)\b"
)
PR_MARK = re.compile(
    r"\$\{?(?:HEAD|PR_REF|PR_HEAD|HEAD_SHA)\b|pr-head|refs/pull/|FETCH_HEAD|head[._](?:sha|ref)|workflow_run\.head|\bgh\s+pr\s+diff\b"
)
RUNS_PR_FILE = re.compile(
    r"\bgit\s+show\b.*\|\s*(?:sudo\s+)?(?:ba|z|da)?sh\b|\bgit\s+show\b.*\|\s*(?:python3?|node|perl|ruby)\b|<\(\s*git\s+show\b"
)
GH_CHECKOUT = re.compile(r"\bgh\s+pr\s+checkout\b")
# applying a patch: in a privileged job its content is the PR's whatever its path, and a saved diff hides the source
APPLY = re.compile(
    r"\bgit(?:\s+-[Cc]\s+\S+)*\s+(?:apply|am)\b"  # anywhere: an unambiguous command
    r"|(?:^|[|({!`]|\$\(|\b(?:then|do|else|elif|if|while|until|exec|time|sudo|env|command|xargs|nohup)\s)\s*patch\b"  # patch where a command starts
    r"|(?<![\w./-])patch\s+(?:-|<)"  # patch with an option or a redirect after it
)
DATA_CHECKOUT = re.compile(r"\bgit\s+checkout(?:\s+-q|\s+--quiet)*\s+\S+\s+--\s+(.+)$")


class CancelledRun:
    """Whether a job's `if` can be true on a run that was cancelled: parses the condition (`!`, comparisons, `&&`, `||`, parentheses, calls, contexts) and
    evaluates it with the status functions as they are on a cancelled run; everything else is unknown. Raises ValueError for text it does not understand."""

    def __init__(self, cond: str):
        self.tokens: list[str] = []
        text, pos = cond.strip(), 0
        while pos < len(text):
            if text[pos].isspace():
                pos += 1
                continue
            m = next((m for m in (t.match(text, pos) for t in EXPR_TOKENS) if m), None)
            if m is None:
                raise ValueError(f"unexpected text at {pos}")
            self.tokens.append(m.group())
            pos = m.end()
        self.at = 0

    def peek(self) -> str | None:
        return self.tokens[self.at] if self.at < len(self.tokens) else None

    def take(self, want: str | None = None) -> str:
        tok = self.peek()
        if tok is None or (want is not None and tok != want):
            raise ValueError(f"expected {want or 'more'}")
        self.at += 1
        return tok

    def can_run(self) -> bool:
        value = self.either()
        if self.peek() is not None:
            raise ValueError("trailing text")
        return True in value

    def either(self) -> frozenset:
        value = self.both()
        while self.peek() == "||":
            self.take()
            right = self.both()  # once: parsing it advances the position
            value = frozenset(a or b for a in value for b in right)
        return value

    def both(self) -> frozenset:
        value = self.compared()
        while self.peek() == "&&":
            self.take()
            right = self.compared()
            value = frozenset(a and b for a in value for b in right)
        return value

    def compared(self) -> frozenset:
        value = self.negated()
        while self.peek() in ("==", "!=", "<", "<=", ">", ">="):
            self.take()
            self.negated()
            value = UNKNOWN
        return value

    def negated(self) -> frozenset:
        if self.peek() == "!":
            self.take()
            return frozenset(not v for v in self.negated())
        return self.atom()

    def atom(self) -> frozenset:
        tok = self.take()
        if tok == "(":
            value = self.either()
            self.take(")")
            return value
        if tok[0] == "'" or tok[0].isdigit():
            return UNKNOWN
        if not (tok[0].isalpha() or tok[0] == "_"):
            raise ValueError(f"unexpected {tok}")
        if self.peek() == "(":
            self.arguments()
            return STATUS_ON_CANCELLED.get(tok.lower(), UNKNOWN)
        if tok.lower() in LITERALS and self.peek() not in (".", "["):
            return LITERALS[tok.lower()]
        self.accessors()
        return UNKNOWN

    def arguments(self) -> None:
        self.take("(")
        while self.peek() != ")":
            self.either()
            if self.peek() == ",":
                self.take()
        self.take(")")

    def accessors(self) -> None:
        while self.peek() in (".", "["):
            if self.take() == "[":
                self.either()
                self.take("]")
            else:
                self.take()  # the name after the dot, or the `*` of `.*`


def runs_when_cancelled(cond: str) -> bool:
    """`cond` (a job's `if`) can be true on a cancelled run; text that cannot be parsed counts as yes."""
    wrapped = EXPR.fullmatch(cond.strip())
    try:
        return CancelledRun(wrapped.group(1) if wrapped else cond).can_run()
    except ValueError:
        return True


class Loader(yaml.SafeLoader):
    """SafeLoader that records each mapping's line (for messages)."""


def _mapping(loader: Loader, node: yaml.MappingNode) -> dict:
    m = loader.construct_mapping(node, deep=True)
    m[LINE] = node.start_mark.line + 1
    return m


Loader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _mapping)


def items(m: object) -> list[tuple]:
    return [(k, v) for k, v in m.items() if k != LINE] if isinstance(m, dict) else []


def contexts(expr: str) -> list[str]:
    """The contexts whose value an expression can return: compared or boolean-only contexts are dropped."""
    e = re.sub(STRING, "''", expr)  # first: a parenthesis inside a string is not one
    while m := BOOLEAN_CALL.search(e):  # a boolean function's arguments never reach the value
        depth, i = 0, m.end() - 1
        for i in range(m.end() - 1, len(e)):
            depth += {"(": 1, ")": -1}.get(e[i], 0)
            if depth == 0:
                break
        e = e[: m.start()] + "true" + e[i + 1 :]
    e = COMPARISON.sub("true", e)
    e = NEGATION.sub("true", e)
    return [m.group(1) for m in REFERENCE.finditer(e) if not m.group(2) and m.group(1) not in ("true", "false", "null")]


def triggers(wf: dict) -> set[str]:
    on = wf.get("on", wf.get(True))  # YAML 1.1 reads a bare `on` key as true
    if isinstance(on, str):
        return {on}
    if isinstance(on, list):
        return {str(t) for t in on}
    return {str(k) for k, _ in items(on)}


def resolve_env(value: str, *envs: dict) -> str:
    """Substitute `${{ env.X }}` from the step, job and workflow env (one level)."""

    def sub(m: re.Match) -> str:
        name = m.group(1)
        for env in envs:
            if isinstance(env, dict) and name in env:
                return str(env[name])
        return m.group(0)

    return re.sub(r"\$\{\{\s*env\.([\w-]+)\s*\}\}", sub, value)


class Checker:
    def __init__(self, path: str, text: str):
        self.path, self.text, self.lines = path, text, text.splitlines()
        self.findings: list[tuple[str, int, str, str]] = []
        self.pins: list[tuple[str, int, str, str, str]] = []  # path, line, repo, sha, tag

    def add(self, line: int, rule: str, msg: str) -> None:
        self.findings.append((self.path, line, rule, msg))

    def line_of(self, needle: str, start: int) -> int:
        for i in range(max(start - 1, 0), len(self.lines)):
            if needle in self.lines[i]:
                return i + 1
        return start

    def run(self) -> Checker:
        try:
            doc = yaml.load(self.text, Loader=Loader)  # noqa: S506 — SafeLoader subclass
        except (yaml.YAMLError, RecursionError) as e:  # RecursionError: nested thousands deep
            self.add(1, "yaml", f"not valid YAML: {e}")
            return self
        if not isinstance(doc, dict):
            self.add(1, "yaml", "not a mapping")
            return self
        if Path(self.path).name in ("action.yml", "action.yaml"):
            runs = doc.get("runs") if isinstance(doc.get("runs"), dict) else {}
            self.steps(runs.get("steps") or [], {}, {}, set())
            return self
        perms = doc.get("permissions", "missing")
        if not (isinstance(perms, dict) and not items(perms)):
            self.add(1, "permissions", f"the workflow must start with `permissions: {{}}` (found {perms!r}); each job grants what it needs")
        on = triggers(doc)
        for name, job in items(doc.get("jobs")):
            if not isinstance(job, dict):
                continue
            line = job.get(LINE, 1)
            if job.get("permissions") in ("write-all", "read-all"):
                self.add(line, "permissions", f"job `{name}` grants {job['permissions']}: list the scopes it needs")
            if isinstance(job.get("uses"), str):
                self.pinned(job["uses"], line)
            self.steps(job.get("steps") or [], job.get("env") or {}, doc.get("env") or {}, on)
            self.write_and_pr(name, job, on, doc.get("env") or {})
            self.cancelable(name, job, doc)
        return self

    def cancelable(self, name: str, job: dict, doc: dict) -> None:
        """A job of a workflow whose runs are cancelled by newer ones does not run on `always()`."""
        conc = [c for c in (doc.get("concurrency"), job.get("concurrency")) if isinstance(c, dict)]
        cancels = any(str(c.get("cancel-in-progress", "false")).strip().lower() not in ("false", "") for c in conc)
        cond = job.get("if")
        if cancels and isinstance(cond, str) and ALWAYS_CALL.search(cond) and runs_when_cancelled(cond):
            self.add(
                job.get(LINE, 1),
                "cancelable",
                f"job `{name}` runs on `always()` in a workflow whose runs are cancelled by newer ones: a cancelled run still runs it and its result outlives the run; "
                "use `!cancelled()`",
            )

    def write_and_pr(self, name: str, job: dict, on: set[str], wf_env: object) -> None:
        """A job that can write never reads the commits of the PR or of the queue entry."""
        writes = [k for k, v in items(job.get("permissions")) if str(v).lower() == "write"]
        if not writes or not on & (PRIVILEGED | {"merge_group"}):
            return
        for step in job.get("steps") or []:
            if not isinstance(step, dict):
                continue
            what = self.reads_untrusted(step, on, (step.get("env") or {}, job.get("env") or {}, wf_env))
            if what:
                self.add(
                    step.get(LINE, 1),
                    "write-and-pr",
                    f"job `{name}` holds `{writes[0]}: write` and {what}: read them in a job without a write permission "
                    "and pass only validated outputs to this one",
                )

    def reads_untrusted(self, step: dict, on: set[str], envs: tuple) -> str:
        """What a step does with the PR's or the queue entry's commits, in words; '' when it does nothing of the kind."""
        uses = step.get("uses") if isinstance(step.get("uses"), str) else ""
        if uses.lower().startswith("actions/checkout@"):
            return self.checkout_reads(step, on, envs)
        run = step.get("run")
        if not isinstance(run, str):
            return ""
        if GH_CHECKOUT.search(run):
            return "runs `gh pr checkout`"
        if APPLY.search(run):
            return "applies a patch"
        if GIT_READS.search(run) and untrusted_text(run, envs, on):
            return "runs git on a name that can carry the PR's commits"
        return ""

    def checkout_reads(self, step: dict, on: set[str], envs: tuple) -> str:
        with_ = {str(k).lower(): v for k, v in items(step.get("with"))}
        ref = resolve_env(str(with_["ref"]), *envs).strip() if with_.get("ref") is not None else ""
        if "merge_group" in on and not ref:  # omitted, empty or an env var that is empty: the default is the queue entry
            return "checks out the queue entry (an actions/checkout without a `ref`, or with an empty one, in a merge_group workflow)"
        if ref and untrusted_text(ref, envs, on):
            return f"checks out `ref: {with_['ref']}`"
        repo = resolve_env(str(with_.get("repository", "")), *envs)
        if any(c != "github.repository" for m in EXPR.finditer(repo) for c in contexts(m.group(1))):
            return f"checks out `repository: {with_['repository']}`"
        return ""

    def steps(self, steps: list, job_env: dict, wf_env: dict, on: set[str]) -> None:
        for step in steps if isinstance(steps, list) else []:  # `steps: 5` used to end the check in a traceback (scripts/ci/fuzz)
            if not isinstance(step, dict):
                continue
            line = step.get(LINE, 1)
            uses = step.get("uses") if isinstance(step.get("uses"), str) else ""
            action = uses.lower()  # GitHub resolves owner and repository names regardless of case
            # action inputs are case-insensitive too (`REF:` is `ref:`)
            with_ = {str(k).lower(): v for k, v in items(step.get("with"))}
            if uses:
                self.pinned(uses, line)
            if uses.startswith("./") and on & PRIVILEGED:
                self.add(
                    line,
                    "pr-code",
                    f"`{uses}` is loaded from the workspace, which may hold the PR's files: name the action in this repository as `$/<path>`",
                )
            if action.startswith("actions/checkout@"):
                if str(with_.get("persist-credentials")).lower() != "false":
                    self.add(line, "token", "actions/checkout keeps the job's token in the checkout: set `persist-credentials: false`")
                if on & PRIVILEGED:
                    self.pr_checkout(with_, line, step.get("env") or {}, job_env, wf_env)
            scripts = [step["run"]] if isinstance(step.get("run"), str) else []
            if action.startswith("actions/github-script@") and isinstance(with_.get("script"), str):
                scripts.append(with_["script"])
            for script in scripts:
                self.expressions(script, line)
                if on & PRIVILEGED:
                    self.pr_commands(script, line)

    def pinned(self, uses: str, line: int) -> None:
        if uses.startswith("./"):
            return
        if uses.startswith("$/"):  # self-repository: the running commit's own action, takes no @ref
            if uses == "$/" or "@" in uses:
                self.add(line, "pinned", f"`{uses}`: a `$/<path>` reference needs a path and takes no `@ref`")
            return
        if uses.startswith("docker://"):
            if not re.search(r"@sha256:[0-9a-f]{64}$", uses):
                self.add(line, "pinned", f"`{uses}`: pin the image by digest (docker://image@sha256:<64 hex>)")
            return
        target, _, ref = uses.rpartition("@")
        if not SHA.fullmatch(ref):
            self.add(
                line, "pinned", f"`{uses}` names a tag or branch, which can be moved to new code: pin the full commit, tag as a comment"
            )
            return
        comment = None
        for i in range(max(line - 1, 0), len(self.lines)):
            m = USES_LINE.match(self.lines[i])
            if m and m.group(1) == uses:
                comment, line = m.group(2), i + 1
                break
        if not comment:
            self.add(line, "pinned", f"`{uses}` has no `# <tag>` comment: name the tag the commit was taken from")
            return
        self.pins.append((self.path, line, "/".join(target.split("/")[:2]), ref, comment))

    def expressions(self, script: str, line: int) -> None:
        for m in EXPR.finditer(script):
            bad = [c for c in contexts(m.group(1)) if not FIXED.match(c)]
            if bad:
                self.add(
                    self.line_of(m.group(0).splitlines()[0], line),
                    "expressions",
                    f"`{m.group(0).strip()}` pastes {', '.join(sorted(set(bad)))} into the script, where text becomes code: "
                    'pass it through `env:` and quote it as "$VAR"',
                )

    def pr_checkout(self, with_: dict, line: int, *envs: dict) -> None:
        for key, allowed in (("ref", BASE_SIDE), ("repository", {"github.repository"})):
            value = with_.get(key)
            if value is None:
                continue
            resolved = resolve_env(str(value), *envs)
            names = [c for m in EXPR.finditer(resolved) for c in contexts(m.group(1))]
            if any(c not in allowed for c in names) or (not names and key == "ref" and "pull/" in resolved):
                self.add(
                    line, "pr-code", f"this workflow holds the repository's token and checks out `{key}: {value}`: check out the base only"
                )

    def pr_commands(self, script: str, line: int) -> None:
        joined = re.sub(r"\\\n\s*", " ", script)
        for raw in joined.splitlines():
            raw = re.sub(r"\$\(\s*git\s+merge-base\b[^)]*\)", "BASE", raw)  # a merge base is a commit of the base branch
            for cmd in re.split(r"&&|\|\||;", raw):
                if APPLY.search(cmd):
                    self.add(
                        self.line_of(raw.strip()[:40], line),
                        "pr-code",
                        f"`{cmd.strip()}` applies a patch in a job that holds the repository's token",
                    )
                    continue
                if GH_CHECKOUT.search(cmd):
                    self.add(
                        self.line_of(raw.strip()[:40], line),
                        "pr-code",
                        f"`{cmd.strip()}` checks out the PR in a job that holds the repository's token",
                    )
                    continue
                if RUNS_PR_FILE.search(cmd) and PR_MARK.search(cmd):
                    self.add(
                        self.line_of(raw.strip()[:40], line),
                        "pr-code",
                        f"`{cmd.strip()}` runs a file from the PR with the repository's token",
                    )
                    continue
                if not (GIT_WRITE.search(cmd) and PR_MARK.search(cmd)):
                    continue
                m = DATA_CHECKOUT.search(cmd)
                try:
                    paths = shlex.split(m.group(1)) if m else []
                except ValueError:
                    paths = []
                if paths and all((p == "data" or p.startswith("data/")) and ".." not in p for p in paths):
                    continue
                self.add(
                    self.line_of(raw.strip()[:40], line),
                    "pr-code",
                    f"`{cmd.strip()}` puts the PR's files in the tree of a job that holds the repository's token; only `git checkout <pr> -- data` may",
                )


def verify_pins(pins: list[tuple[str, int, str, str, str]]) -> list[tuple[str, int, str, str]]:
    findings, seen = [], {}
    for path, line, repo, sha, tag in pins:
        key = (repo, sha, tag)
        if key not in seen:
            r = subprocess.run(
                ["gh", "api", f"repos/{repo}/compare/{urllib.parse.quote(tag, safe='')}...{sha}", "--jq", ".status"],
                capture_output=True,
                text=True,
            )
            seen[key] = r.stdout.strip() if r.returncode == 0 else "error: " + (r.stderr or r.stdout).strip()[:200]
        status = seen[key]
        if status not in ("identical", "behind"):
            findings.append(
                (
                    path,
                    line,
                    "pinned",
                    f"{repo}@{sha[:12]} is not in the history of {repo}'s `{tag}` ({status}): the comment names the wrong tag, "
                    "or the commit exists only in a fork (an impostor commit)",
                )
            )
    return findings


def report(path: str, line: int, rule: str, msg: str) -> tuple[str, str]:
    """A finding as the log prints it, and as a check-run annotation. The path and the message come from the PR (a
    YAML error quotes the file, lines and all): neither may start a workflow command of its own (scripts/ci/fuzz)."""
    prop = annotation(path).replace(":", "%3A").replace(",", "%2C")
    return plain(f"{path}:{line}: [{rule}] {msg}"), f"::error file={prop},line={line},title=workflow rule: {rule}::{annotation(msg)}"


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout


def workflow_file(path: str) -> bool:
    p = Path(path)
    if path.startswith(".github/workflows/") and p.suffix in (".yml", ".yaml"):
        return True
    return path.startswith(".github/") and p.name in ("action.yml", "action.yaml")


def main(argv: list[str]) -> int:
    online = "--online" in argv
    args = [a for a in argv if a != "--online"]
    if args[:1] == ["--changed"] and len(args) == 3:
        base, head = args[1], args[2]
        if git("diff", "--name-only", "--no-renames", "--diff-filter=D", f"{base}...{head}", "--", SELF).strip():
            print(f"{SELF}: [removed] the PR deletes or moves the workflow rules; change them in place instead")
            return 1
        names = git("diff", "--name-only", "-z", "--diff-filter=AMR", f"{base}...{head}", "--", ".github").split("\0")
        docs = [(n, git("show", f"{head}:{n}")) for n in names if n and workflow_file(n)]
        if not docs:
            print("no workflow or action file changed")
            return 0
    elif args and not args[0].startswith("-"):
        files: list[Path] = []
        for a in map(Path, args):
            files += sorted(p for p in a.rglob("*") if p.suffix in (".yml", ".yaml")) if a.is_dir() else [a]
        docs = [(str(p), p.read_text()) for p in files]
    else:
        print(__doc__)
        return 2
    findings, pins = [], []
    for path, text in docs:
        c = Checker(path, text).run()
        findings += c.findings
        pins += c.pins
    if online:
        findings += verify_pins(pins)
    for finding in findings:
        readable, annotation = report(*finding)
        print(readable)
        if os.environ.get("GITHUB_ACTIONS"):
            print(annotation)
    pinned = f", {len({(p[2], p[3], p[4]) for p in pins})} pins verified online" if online else ""
    print(f"{len(docs)} files{pinned}: " + (f"{len(findings)} findings" if findings else "every rule holds"))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
