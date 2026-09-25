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

LINE = "__line__"
SHA = re.compile(r"[0-9a-f]{40}")
USES_LINE = re.compile(r"""^\s*(?:-\s+)?uses:\s*["']?([^\s"'#]+)["']?\s*(?:#\s*(\S+))?""")
EXPR = re.compile(r"\$\{\{(.*?)\}\}", re.S)
STRING = r"'(?:[^']|'')*'"
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
    e = expr
    while m := BOOLEAN_CALL.search(e):  # a boolean function's arguments never reach the value
        depth, i = 0, m.end() - 1
        for i in range(m.end() - 1, len(e)):
            depth += {"(": 1, ")": -1}.get(e[i], 0)
            if depth == 0:
                break
        e = e[: m.start()] + "true" + e[i + 1 :]
    e = re.sub(STRING, "''", e)
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
        except yaml.YAMLError as e:
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
        return self

    def steps(self, steps: list, job_env: dict, wf_env: dict, on: set[str]) -> None:
        for step in steps:
            if not isinstance(step, dict):
                continue
            line = step.get(LINE, 1)
            uses = step.get("uses") if isinstance(step.get("uses"), str) else ""
            with_ = step.get("with") if isinstance(step.get("with"), dict) else {}
            if uses:
                self.pinned(uses, line)
            if uses.startswith("./") and on & PRIVILEGED:
                self.add(
                    line,
                    "pr-code",
                    f"`{uses}` is loaded from the workspace, which may hold the PR's files: name the action in this repository as `$/<path>`",
                )
            if uses.startswith("actions/checkout@"):
                if str(with_.get("persist-credentials")).lower() != "false":
                    self.add(line, "token", "actions/checkout keeps the job's token in the checkout: set `persist-credentials: false`")
                if on & PRIVILEGED:
                    self.pr_checkout(with_, line, step.get("env") or {}, job_env, wf_env)
            scripts = [step["run"]] if isinstance(step.get("run"), str) else []
            if uses.startswith("actions/github-script@") and isinstance(with_.get("script"), str):
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
    for path, line, rule, msg in findings:
        print(f"{path}:{line}: [{rule}] {msg}")
        if os.environ.get("GITHUB_ACTIONS"):
            print(f"::error file={path},line={line},title=workflow rule: {rule}::{msg}")
    pinned = f", {len({(p[2], p[3], p[4]) for p in pins})} pins verified online" if online else ""
    print(f"{len(docs)} files{pinned}: " + (f"{len(findings)} findings" if findings else "every rule holds"))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
