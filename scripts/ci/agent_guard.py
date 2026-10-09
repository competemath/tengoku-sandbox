#!/usr/bin/env python3
"""agent_guard.py check|publish — the advisory `scope` check of agent-written pull requests (docs/agent-security.md).

  agent_guard.py check   --repo . --base SHA --head SHA --out DIR     the read-only half: judge the PR, write DIR/result.json and DIR/summary.md
  agent_guard.py publish --dir DIR --repo OWNER/NAME                  the write half: post DIR/result.json as the check run `scope`
  agent_guard.py ownership [--codeowners F] [--policy F]              only the CODEOWNERS divergence check, for use by hand

`check` reads the PR only as git objects (two commits, never a checkout) and judges it with the vendored tengoku-warden modules
(scripts/ci/warden/, pinned and tested for drift) under two policies it takes from main: scripts/ci/agent-paths.json (what an agent
PR may touch: the scope policy) and .github/agent-paths.json (who owns what: the single source CODEOWNERS must agree with). It looks
for five things:

  scope      a PR from a bot account, or one that says in its branch or title that it is a factory PR, is held to the scope policy of
             its class: allowed paths, file modes (100644 only: no symlink, submodule or executable), size caps, no binary files.
  modes      every PR: no symlink, submodule or executable file is added under data/ or Tengoku/. (The content lint and the record
             validator read file contents, not git modes; restructure_check.py compares modes only for its own class.)
  secrets    every PR: the PR title, body, each commit message and the lines it adds are scanned for secrets (the content scanners
             of pr-gate read files; what an agent also publishes is its metadata). A `pragma: allowlist secret` hides nothing in metadata.
  dropped    a push by an agent (a bot account, or commits that carry an AI co-author trailer) that changes human-owned paths
             relative to the previous head: the way an agent turns a human's PR green by stripping the parts that fail.
  ownership  CODEOWNERS and .github/agent-paths.json agree in effect, and the scope policy lies outside what humans own.

Nothing here decides: the result is a check run named `scope` (success, neutral or failure) on the PR head, advisory until the
maintainer makes it required and pins it to the App that makes it (tengoku-warden docs/RUNBOOK.md, item 4). The two halves are two
jobs: `check` holds a read token, `publish` holds `checks: write` and takes only the validated result file, never the PR.

Credit: Tau Ceti Project, the `scope` status and scope linter of TauCeti (pr-build.yml, scripts/lint_scope_files.py; issue 12085 and PR
12207, 2026-10-05), its CODEOWNERS history (PRs 41, 204, 246, 6018), and the 2026-06-23 incident (PRs 351, 370, 371) in which an agent
stripped the CI parts of a human-owned PR; see tengoku-warden docs/TAU-CETI.md. The code is independent. Standard library only."""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

from _git import plain
from warden import ownership, safegit, scope, secretscan

CI = Path(__file__).resolve().parent
ROOT = CI.parents[1]
SCHEMA = "tengoku-agent-guard/1"
CHECK_NAME = "scope"
SHA = re.compile(r"^[0-9a-f]{40}$")
LOGIN = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9/\[\]-]{0,59})$")  # a user, or a bot such as dependabot[bot]
REPO = re.compile(r"^[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}$")
CHECKS = ("scope", "modes", "secrets", "dropped", "ownership")
SEVERITIES = ("violation", "notice")
MAX_FINDINGS = 200
MAX_DIFF_BYTES = 5_000_000
# the account that is the factory in production; the repository variable TENGOKU_BOT names the one a repository uses (the sandbox's is a person)
FACTORY_ACCOUNT = "tengoku-bot"
# the classes classify.py gives the PRs the factory opens
FACTORY_CLASSES = frozenset({"promotion", "intake", "extend", "tag", "native", "scope-fix", "restructure"})
# what the factory's own workflows name their branches (promote.yml, isnad-tag.yml, open_intake_pr.py, the scope-fix tool) and titles
FACTORY_BRANCH = re.compile(r"^(?:(?:intake|promote|isnad|bump|native|topup)/|scopefix-)", re.I)
FACTORY_TITLE = re.compile(r"^(?:intake|promote|promotion|isnad|bump|native|scope[- ]fix)\s*[:(]", re.I)
# a trailer an AI coding agent leaves on the commits it makes ("Co-Authored-By: Claude …", "Generated with Claude Code")
AGENT_TRAILER = re.compile(
    r"^\W*(?:co-authored-by|assisted-by|generated[- ]with|generated[- ]by)\b.*\b(?:claude|codex|copilot|gemini|cursor|aider|devin|openai|anthropic)\b",
    re.I | re.M,
)
ALLOW_PRAGMA = re.compile(r"pragma:\s*allowlist[ _-]*secret", re.I)
MODE_NAMES = {"120000": "symlink", "160000": "submodule", "100755": "executable"}
MODE_PREFIXES = ("data/", "Tengoku/")


@dataclass
class Finding:
    check: str
    code: str
    path: str = ""
    detail: str = ""
    severity: str = "violation"

    def to_dict(self) -> dict:
        return {
            "check": self.check,
            "code": self.code,
            "path": safe(self.path, 200),
            "detail": safe(self.detail, 200),
            "severity": self.severity,
        }


@dataclass
class Inputs:
    """Everything that comes from the pull request event. Strings here are untrusted text: they are compared and scanned, never run."""

    repo: str
    base: str
    head: str
    actor: str = ""
    actor_type: str = ""
    sender: str = ""
    head_ref: str = ""
    title: str = ""
    body: str = ""
    before: str = ""
    tengoku_bot: str = FACTORY_ACCOUNT
    scope_policy: str = str(CI / "agent-paths.json")
    notices: list = field(default_factory=list)


def safe(text: object, limit: int = 120) -> str:
    """Text from a PR as it may appear in a check run or a job summary: a small alphabet, no markup, no control character, cut short."""
    s = re.sub(r"[^A-Za-z0-9 ._/+@#:=(),'\-]", "?", str(text))
    return s[:limit]


# ----------------------------------------------------------------------------------------------------- who is an agent PR


def bot_account(login: str, user_type: str = "") -> bool:
    return login.endswith("[bot]") or user_type == "Bot" or login == FACTORY_ACCOUNT


def scope_class(login: str, user_type: str, head_ref: str, title: str, tengoku_bot: str, pr_class: str) -> tuple:
    """(the class of the scope policy that judges this PR, why) or (None, why not).

    dependabot             its own class: workflow files and the pinned requirements, nothing else
    the factory            tengoku-bot; the account the repository variable TENGOKU_BOT names, when classify.py gave the PR one of the
                           factory's classes (in the sandbox that account is a person, whose tooling PRs are not the factory's)
    any other bot account  the strictest class: it may touch nothing
    a factory-shaped PR    a branch or title the factory's workflows use, from any account: held to the factory's class, because
                           the name asks for the factory's treatment."""
    if login.startswith("dependabot") and login.endswith("[bot]"):
        return "dependabot", "dependabot's account"
    if login == FACTORY_ACCOUNT or (tengoku_bot and login == tengoku_bot and pr_class in FACTORY_CLASSES):
        return "factory", "the factory's account"
    if bot_account(login, user_type):
        return "bot", "a bot account"
    if FACTORY_BRANCH.match(head_ref):
        return "factory", "a branch named like the factory's"
    if FACTORY_TITLE.match(title):
        return "factory", "a title worded like the factory's"
    return None, "not an agent PR"


def agent_commits(messages: list) -> int:
    """How many commit messages carry an AI co-author trailer."""
    return sum(1 for m in messages if AGENT_TRAILER.search(m))


# ----------------------------------------------------------------------------------------------------------------- git reads


def git(repo: str, *args: str) -> str:
    return scope.run_git(repo, list(args)).decode("utf-8", "replace")


def has_commit(repo: str, sha: str) -> bool:
    try:
        scope.run_git(repo, ["cat-file", "-e", sha + "^{commit}"])
        return True
    except scope.GitError:
        return False


def blob_at(repo: str, commit: str, path: str) -> str | None:
    """A file as the commit has it, or None when it has none."""
    try:
        return scope.run_git(repo, ["cat-file", "blob", f"{commit}:{path}"]).decode("utf-8", "replace")
    except scope.GitError:
        return None


def commit_messages(repo: str, merge_base: str, head: str) -> list:
    out = scope.run_git(repo, ["log", "--no-color", "--format=%H%x1f%B%x1e", f"{merge_base}..{head}"]).decode("utf-8", "replace")
    msgs = []
    for entry in out.split("\x1e"):
        if "\x1f" in entry:
            sha, body = entry.strip("\n").split("\x1f", 1)
            msgs.append((sha.strip()[:12], body))
    return msgs


def added_text(repo: str, merge_base: str, head: str) -> tuple:
    """(the unified diff of what the PR adds outside data/ and Tengoku/, whether it was cut). Those two trees are scanned by
    TruffleHog in pr-gate and are too large to scan with a regex scanner: an intake bundle adds a hundred thousand lines."""
    out = scope.run_git(
        repo,
        [
            "diff",
            "-U0",
            "--no-color",
            "--no-renames",
            "--no-ext-diff",
            "--no-textconv",
            merge_base,
            head,
            "--",
            ".",
            ":(exclude)data",
            ":(exclude)Tengoku",
            ":(exclude).lake",
        ],
    )
    return out[:MAX_DIFF_BYTES].decode("utf-8", "replace"), len(out) > MAX_DIFF_BYTES


# ----------------------------------------------------------------------------------------------------------------- the checks


def mode_findings(changes: list) -> list:
    """No symlink, submodule or executable file arrives under data/ or Tengoku/ (added, or changed to that mode)."""
    out = []
    for c in changes:
        if c.status == "D" or not c.path.startswith(MODE_PREFIXES):
            continue
        if (c.status == "A" or c.old_mode != c.new_mode) and c.new_mode != "100644":
            out.append(Finding("modes", MODE_NAMES.get(c.new_mode, "odd_mode") + "_added", c.path, f"mode {c.new_mode}"))
    return out


def scope_findings(repo: str, merge_base: str, head: str, policy_path: str, klass: str) -> list:
    try:
        policy = scope.Policy.load(policy_path)
    except scope.PolicyError as exc:
        return [Finding("scope", "policy_unreadable", detail=str(exc))]
    result = scope.check(repo, merge_base, head, policy, klass)
    return [Finding("scope", v.code, v.path or "", v.detail) for v in result.violations]


def neutralise(text: str) -> str:
    """Metadata is scanned as it is: the pragma that tells a scanner to skip a line of source hides nothing in a title or a message."""
    return ALLOW_PRAGMA.sub("pragma-removed", text)


def secret_findings(title: str, body: str, messages: list, diff: str) -> list:
    out = []
    for source, text in (("PR title", title), ("PR body", body), *((f"commit {sha}", msg) for sha, msg in messages)):
        for f in secretscan.scan(neutralise(text), source):
            out.append(Finding("secrets", f.kind, source, f"line {f.line}"))
    for f in secretscan.scan_diff(diff):
        out.append(Finding("secrets", f.kind, f.source, f"line {f.line}"))
    return out


def dropped_findings(repo: str, before: str, head: str, base: str, merge_base: str, human: list) -> list:
    """Human-owned paths whose content differs between the previous head and this one, among the paths the PR itself changes
    (a rebase onto a moved base changes other paths in the same way on both sides and is not the PR's doing)."""
    own = {c.path for c in scope.changed(repo, merge_base, head)}
    try:
        own |= {c.path for c in scope.changed(repo, git(repo, "merge-base", base, before).strip(), before)}
    except scope.GitError:
        pass
    return [
        Finding("dropped", "human_work_" + d.kind, d.path) for d in scope.dropped_human_owned(repo, before, head, human) if d.path in own
    ]


def normalise_owners(codeowners: str, human_owners: tuple, token: str = "@human") -> str:
    """CODEOWNERS with every rule whose owners are exactly the human set rewritten to one owner (warden.ownership compares one owner;
    the repository's rules name two accounts, either of whose approval counts)."""
    out = []
    for raw in codeowners.splitlines():
        line = raw.split("#", 1)[0].split()
        if len(line) > 1 and frozenset(line[1:]) == frozenset(human_owners):
            out.append(f"{line[0]} {token}")
        else:
            out.append(raw)
    return "\n".join(out) + "\n"


def human_owners_of(codeowners: str) -> tuple:
    """The owners most rules name: the human set."""
    sets = collections.Counter(
        tuple(sorted(set(line))) for raw in codeowners.splitlines() if len(line := raw.split("#", 1)[0].split()[1:]) > 0
    )
    return sets.most_common(1)[0][0] if sets else ()


def scope_policy_problems(scope_doc: dict, own_doc: dict) -> list:
    """The scope policy must lie inside the ownership policy: what it protects is human-owned, and a class that may not touch protected
    paths is not allowed to write one."""
    problems = []
    try:
        scope.Policy.from_dict(scope_doc)
    except scope.PolicyError as exc:
        return [f"the scope policy does not parse: {exc}"]
    human = set(own_doc.get("human", []))
    for glob in scope_doc.get("protected", []):
        if glob not in human:
            problems.append(f"protected path {glob} is not human-owned in .github/agent-paths.json")
    for name, cls in scope_doc.get("classes", {}).items():
        if cls.get("touch_protected"):
            continue
        for glob in scope_doc.get("protected", []):
            overlap = [p for p in ownership.sample_paths(glob) if scope.matches_any(cls.get("allow", []), p)]
            overlap += [
                p for a in cls.get("allow", []) for p in ownership.sample_paths(a) if scope.glob_match(glob, p)
            ]  # an allowed path inside a protected one
            if overlap:
                problems.append(f"class {name} may write {overlap[0]}, which is protected")
    return problems


def ownership_findings(codeowners: str | None, own_text: str | None, scope_text: str | None) -> list:
    if codeowners is None or own_text is None:
        return [Finding("ownership", "file_missing", ".github/CODEOWNERS" if codeowners is None else ".github/agent-paths.json")]
    try:
        own_doc = json.loads(own_text)
        policy = _policy_from(own_doc)
    except (ValueError, ownership.OwnershipError) as exc:
        return [Finding("ownership", "policy_invalid", ".github/agent-paths.json", str(exc))]
    owners = human_owners_of(codeowners)
    if not owners:
        return [Finding("ownership", "no_owners", ".github/CODEOWNERS", "no rule names an owner")]
    out = [
        Finding("ownership", "diverged", d.pattern, f"{d.probe}: committed {d.committed}, policy {d.expected}")
        for d in ownership.divergence(normalise_owners(codeowners, owners), policy, human_owner="@human")
    ]
    if scope_text is not None:
        try:
            out += [
                Finding("ownership", "scope_policy", "scripts/ci/agent-paths.json", p)
                for p in scope_policy_problems(json.loads(scope_text), own_doc)
            ]
        except ValueError as exc:
            out.append(Finding("ownership", "scope_policy", "scripts/ci/agent-paths.json", f"not JSON: {exc}"))
    return out


def _policy_from(doc: object) -> dict:
    problems = ownership.validate_policy(doc)
    if problems:
        raise ownership.OwnershipError("; ".join(problems))
    return {k: list(doc[k]) for k in ("human", "agent", "review")}


# ------------------------------------------------------------------------------------------------------------------- the guard


def pr_class(inp: Inputs) -> str:
    """The class classify.py gives the PR, read the way the merge queue reads it (the gate already judged the actor)."""
    env = {
        **os.environ,
        "PR_ACTOR": inp.actor,
        "TENGOKU_ACTOR_CHECKED": "1",
        "TENGOKU_CI_ROOT": os.path.abspath(inp.repo),
        "TENGOKU_BOT": inp.tengoku_bot,
    }
    done = subprocess.run(
        [sys.executable, str(CI / "classify.py"), inp.base, inp.head],
        cwd=inp.repo,
        capture_output=True,
        text=True,
        env=env,
        timeout=300,
        check=False,
    )
    m = re.search(r"^class=([a-z-]+)", done.stdout, re.M)
    return m.group(1) if done.returncode == 0 and m else "other"


def check(inp: Inputs, cls: str | None = None) -> dict:
    """Judge one pull request. Returns the result document (see validate_result)."""
    for label, sha in (("base", inp.base), ("head", inp.head)):
        safegit.check_oid(sha, label)
    repo = inp.repo
    merge_base = git(repo, "merge-base", inp.base, inp.head).strip()
    findings: list = []
    pr_cls = cls if cls is not None else pr_class(inp)
    klass, why = scope_class(inp.actor, inp.actor_type, inp.head_ref, inp.title, inp.tengoku_bot, pr_cls)

    changes = scope.changed(repo, merge_base, inp.head)
    findings += mode_findings(changes)
    if klass is not None and pr_cls == "restructure":
        why += "; the move of the seed is recomputed byte for byte by restructure_check.py, so the path rules are not applied"
    elif klass is not None:
        findings += scope_findings(repo, merge_base, inp.head, inp.scope_policy, klass)

    messages = commit_messages(repo, merge_base, inp.head)
    diff, cut = added_text(repo, merge_base, inp.head)
    findings += secret_findings(inp.title, inp.body, messages, diff)
    pragmas = sum(1 for ln in diff.splitlines() if ln.startswith("+") and ALLOW_PRAGMA.search(ln))
    notices = list(inp.notices)
    if cut:
        notices.append(f"only the first {MAX_DIFF_BYTES // 1_000_000} MB of added lines outside data/ and Tengoku/ were scanned")
    if pragmas:
        notices.append(f"{pragmas} added line(s) carry an allowlist pragma (the content scanners skip them)")

    agent_commits_n = 0
    if SHA.match(inp.before) and set(inp.before) != {"0"}:
        if has_commit(repo, inp.before):
            agent_commits_n = agent_commits([m for _sha, m in commit_messages(repo, inp.before, inp.head)])
            agent_push = bot_account(inp.sender) or agent_commits_n > 0
            # a bot account updating its own PR has no human work to drop (a person's PR in a factory's shape is not the factory's own)
            own_bot_pr = inp.sender == inp.actor and (
                bot_account(inp.actor, inp.actor_type) or (inp.tengoku_bot != "" and inp.actor == inp.tengoku_bot)
            )
            if agent_push and not own_bot_pr:
                try:
                    trusted = blob_at(repo, inp.base, ".github/agent-paths.json")  # the ownership policy of the base, never the PR's
                    human = json.loads(trusted)["human"] if trusted else []
                    findings += dropped_findings(repo, inp.before, inp.head, inp.base, merge_base, human)
                except (scope.GitError, ValueError, KeyError) as exc:
                    findings.append(Finding("dropped", "unreadable", detail=str(exc)[:150], severity="notice"))
        else:
            findings.append(
                Finding(
                    "dropped",
                    "previous_head_gone",
                    detail="a force-push removed it: what the push dropped could not be compared",
                    severity="notice",
                )
            )

    findings += ownership_findings(
        blob_at(repo, inp.head, ".github/CODEOWNERS"),
        blob_at(repo, inp.head, ".github/agent-paths.json"),
        blob_at(repo, inp.head, "scripts/ci/agent-paths.json"),
    )
    return build_result(inp, merge_base, pr_cls, klass, why, findings, notices, agent_commits_n)


def build_result(
    inp: Inputs, merge_base: str, pr_cls: str, klass: str | None, why: str, findings: list, notices: list, agent_commits_n: int
) -> dict:
    violations = [f for f in findings if f.severity == "violation"]
    conclusion = "failure" if violations else ("neutral" if any(f.severity == "notice" for f in findings) else "success")
    return {
        "schema": SCHEMA,
        "head_sha": inp.head,
        "base_sha": inp.base,
        "merge_base": merge_base,
        "class": safe(pr_cls, 20),
        "actor": safe(inp.actor, 60),
        "scope_class": klass or "",
        "scope_reason": safe(why, 200),
        "agent_commits": agent_commits_n,
        "conclusion": conclusion,
        "counts": {c: sum(1 for f in violations if f.check == c) for c in CHECKS},
        "findings": [f.to_dict() for f in findings[:MAX_FINDINGS]],
        "truncated": max(0, len(findings) - MAX_FINDINGS),
        "notices": [safe(n, 240) for n in notices][:20],
    }


# ---------------------------------------------------------------------------------------------------------- the result file


def validate_result(doc: object) -> dict:
    """The write half takes only a result that has exactly this shape: fixed vocabularies, bounded and printable strings.
    Raises ValueError otherwise."""
    if not isinstance(doc, dict) or doc.get("schema") != SCHEMA:
        raise ValueError("not an agent-guard result")
    keys = {
        "schema", "head_sha", "base_sha", "merge_base", "class", "actor", "scope_class", "scope_reason", "agent_commits", "conclusion",
        "counts", "findings", "truncated", "notices",
    }  # fmt: skip
    if set(doc) != keys:
        raise ValueError("unexpected keys")
    for k in ("head_sha", "base_sha", "merge_base"):
        if not isinstance(doc[k], str) or not SHA.match(doc[k]):
            raise ValueError(f"{k} is not a commit")
    if doc["conclusion"] not in ("success", "neutral", "failure"):
        raise ValueError("bad conclusion")
    if doc["scope_class"] not in ("", "factory", "dependabot", "bot"):
        raise ValueError("bad scope class")
    for k in ("class", "actor", "scope_reason"):
        if not isinstance(doc[k], str) or safe(doc[k], 400) != doc[k]:
            raise ValueError(f"{k} is not plain text")
    if not isinstance(doc["agent_commits"], int) or isinstance(doc["agent_commits"], bool) or not 0 <= doc["agent_commits"] <= 100000:
        raise ValueError("bad agent_commits")
    if not isinstance(doc["truncated"], int) or isinstance(doc["truncated"], bool) or doc["truncated"] < 0:
        raise ValueError("bad truncated")
    counts = doc["counts"]
    if (
        not isinstance(counts, dict)
        or set(counts) != set(CHECKS)
        or not all(isinstance(v, int) and not isinstance(v, bool) and v >= 0 for v in counts.values())
    ):
        raise ValueError("bad counts")
    findings = doc["findings"]
    if not isinstance(findings, list) or len(findings) > MAX_FINDINGS:
        raise ValueError("bad findings")
    for f in findings:
        if not isinstance(f, dict) or set(f) != {"check", "code", "path", "detail", "severity"}:
            raise ValueError("bad finding")
        if f["check"] not in CHECKS or f["severity"] not in SEVERITIES:
            raise ValueError("bad finding vocabulary")
        for k in ("code", "path", "detail"):
            if not isinstance(f[k], str) or safe(f[k], 200) != f[k]:
                raise ValueError("a finding is not plain text")
    if (
        not isinstance(doc["notices"], list)
        or len(doc["notices"]) > 20
        or not all(isinstance(n, str) and safe(n, 240) == n for n in doc["notices"])
    ):
        raise ValueError("bad notices")
    return doc


def summary(doc: dict) -> str:
    """The markdown of the job summary and of the check run: fixed words, counts, and the findings as plain code spans."""
    mark = {"success": "no finding", "neutral": "could not verify everything", "failure": "findings"}[doc["conclusion"]]
    lines = [
        f"### scope: {mark}",
        "",
        "> **Advisory.** This check blocks nothing. It is read from git objects by main's copy of the guard; the PR's code never runs.",
        "",
        f"- class of the PR: `{doc['class']}`; opened by `{doc['actor']}`",
        f"- held to the scope policy of: {('`' + doc['scope_class'] + '` (' + doc['scope_reason'] + ')') if doc['scope_class'] else 'nobody: ' + doc['scope_reason']}",
    ]
    if doc["agent_commits"]:
        lines.append(f"- commits of the last push with an AI co-author trailer: {doc['agent_commits']}")
    lines += ["", "| check | findings |", "| --- | --- |"] + [f"| {c} | {doc['counts'][c]} |" for c in CHECKS]
    lines.append("")
    for f in doc["findings"]:
        tag = "" if f["severity"] == "violation" else " (notice)"
        lines.append(f"- **{f['check']}** `{f['code']}`{tag} `{f['path'] or '-'}` {f['detail']}")
    if doc["truncated"]:
        lines.append(f"- … and {doc['truncated']} more")
    lines += [f"- notice: {n}" for n in doc["notices"]]
    return "\n".join(lines) + "\n"


def check_run_body(doc: dict) -> dict:
    """The body of POST /repos/{repo}/check-runs for a validated result."""
    title = {"success": "No finding", "neutral": "Could not verify everything", "failure": "Findings (advisory)"}[doc["conclusion"]]
    return {
        "name": CHECK_NAME,
        "head_sha": doc["head_sha"],
        "status": "completed",
        "conclusion": doc["conclusion"],
        "output": {"title": title, "summary": summary(doc)[:60000]},
    }


# ------------------------------------------------------------------------------------------------------------------------ CLI


def run_check(a: argparse.Namespace) -> int:
    env = os.environ
    inp = Inputs(
        repo=a.repo,
        base=a.base,
        head=a.head,
        actor=a.actor or env.get("PR_ACTOR", ""),
        actor_type=env.get("ACTOR_TYPE", ""),
        sender=env.get("SENDER", ""),
        head_ref=env.get("HEAD_REF", ""),
        title=env.get("PR_TITLE", ""),
        body=env.get("PR_BODY", ""),
        before=env.get("BEFORE", ""),
        tengoku_bot=env.get("TENGOKU_BOT", FACTORY_ACCOUNT),
        scope_policy=a.policy,
    )
    for label, login in (("actor", inp.actor), ("sender", inp.sender)):
        if login and not LOGIN.match(login):
            print(f"agent_guard: the {label} is not a GitHub login", file=sys.stderr)
            return 2
    doc = validate_result(check(inp))
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "result.json").write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out / "summary.md").write_text(summary(doc), encoding="utf-8")
    print(json.dumps({"conclusion": doc["conclusion"], "counts": doc["counts"]}))
    return 0


def run_publish(a: argparse.Namespace) -> int:
    if not REPO.match(a.repo):
        print("agent_guard: the repository is not owner/name", file=sys.stderr)
        return 2
    doc = validate_result(json.loads((Path(a.dir) / "result.json").read_text(encoding="utf-8")))
    done = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{a.repo}/check-runs", "--input", "-"],
        input=json.dumps(check_run_body(doc)),
        capture_output=True,
        text=True,
        check=False,
    )
    if done.returncode != 0:
        print(plain(f"agent_guard: the check run was not created: {done.stderr.strip()[:300]}"), file=sys.stderr)
        return 1
    print(f"posted `{CHECK_NAME}`: {doc['conclusion']}")
    return 0


def run_ownership(a: argparse.Namespace) -> int:
    texts = [Path(p).read_text(encoding="utf-8") if Path(p).is_file() else None for p in (a.codeowners, a.policy, a.scope_policy)]
    found = ownership_findings(*texts)
    for f in found:
        print(plain(f"{f.code}\t{f.path}\t{f.detail}"))
    print("ownership: " + ("in step" if not found else f"DIVERGED ({len(found)})"))
    return 1 if found else 0


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="agent_guard")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check")
    c.add_argument("--repo", default=".")
    c.add_argument("--base", required=True)
    c.add_argument("--head", required=True)
    c.add_argument("--actor")
    c.add_argument("--policy", default=str(CI / "agent-paths.json"))
    c.add_argument("--out", required=True)
    c.set_defaults(fn=run_check)
    p = sub.add_parser("publish")
    p.add_argument("--dir", required=True)
    p.add_argument("--repo", required=True)
    p.set_defaults(fn=run_publish)
    o = sub.add_parser("ownership")
    o.add_argument("--codeowners", default=str(ROOT / ".github" / "CODEOWNERS"))
    o.add_argument("--policy", default=str(ROOT / ".github" / "agent-paths.json"))
    o.add_argument("--scope-policy", default=str(CI / "agent-paths.json"))
    o.set_defaults(fn=run_ownership)
    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except (ValueError, OSError, scope.GitError, safegit.UnsafePush, subprocess.SubprocessError) as exc:
        print(plain(f"agent_guard: {type(exc).__name__}: {exc}"), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
