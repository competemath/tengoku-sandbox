#!/usr/bin/env python3
"""goals_check.py <base> <head> — GOALS.md keeps its shape, and the AI reviewer only writes Suggestions.

Runs when a PR changes GOALS.md (docs/goals.md explains the page). At the PR's head:
- every goal is a `<!-- goal: id -->` … `<!-- /goal -->` block with a unique id, a title and a status
  (open, partly done, done), a people part and one Suggestions part after it;
- the people part has the standard fields (a `done` goal also names what proved it), and no others;
- every `tengoku:Name` reference, in either part, names a record or a declaration that exists;
- every link is http(s).
A PR from the AI reviewer (its branch starts with `goals-suggest/`, or its author is vars.GOALS_AI_ACCOUNT;
the workflow sets GOALS_AI=1) may change only the text inside Suggestions, and no other file.
Goals whose Lean statement a trusted record now proves are reported (not a failure: a person marks them done)."""

from __future__ import annotations

import json
import os
import re
import sys

from _git import ROOT, added_lines, blob, changed_files, fail, match

PAGE = "GOALS.md"
STATUSES = ("open", "partly done", "done")
REQUIRED = ("The statement", "Why it matters", "Why it looks doable", "What it builds on", "Built on the work of")
OPTIONAL = ("Already tried", "Size", "Proved by")
GOAL_RE = re.compile(r"<!-- goal: ([^ ]+) -->\n(.*?)\n<!-- /goal -->", re.S)
ID_RE = re.compile(r"[a-z0-9][a-z0-9-]*")
SUMMARY_RE = re.compile(r"<summary><b>(.+?)</b> · (.+?)</summary>")
PEOPLE_RE = re.compile(r"<!-- people -->\n(.*?)\n<!-- /people -->", re.S)
SUGGEST_RE = re.compile(r"<!-- suggestions -->\n(.*?)\n<!-- /suggestions -->", re.S)
FIELD_RE = re.compile(r"<details><summary>(.+?)</summary>")
REF_RE = re.compile(r"tengoku:([^\s`)\]<>,;]+)")
LINK_RE = re.compile(r"\]\(([^)\s]+)\)|<(\w+:[^>\s]+)>")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local|public)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|opaque|axiom|inductive|structure|class)\s+([^\s:({\[]+)",
    re.M,
)


def text_at(rev: str) -> str:
    b = blob(rev, PAGE)
    return b.decode("utf-8") if b is not None else ""


SCOPE_LINE_RE = re.compile(r"^(?:(?:noncomputable|public|private)\s+)*(namespace|section|end)\b[ \t]*(\S*)")


def lean_full_names(text: str, namespaces: set[str] | None = None) -> set[str]:
    """The full names a Lean file declares: the written name under the namespaces open at that point. The namespaces
    it opens are added to `namespaces` when given."""
    out: set[str] = set()
    stack: list[tuple[str, str]] = []
    decl_at = {m.start(): m.group(1) for m in DECL_RE.finditer(text)}
    pos = 0
    for line in text.splitlines(keepends=True):
        s = SCOPE_LINE_RE.match(line)
        if s:
            kind, name = s.group(1), s.group(2)
            if kind == "end":
                if stack:
                    stack.pop()
            else:
                stack.append((kind, name))
                if kind == "namespace" and name and namespaces is not None:
                    namespaces.add(".".join([n for k, n in stack if k == "namespace" and n]))
        for start, written in decl_at.items():
            if pos <= start < pos + len(line):
                if written.startswith("_root_."):
                    out.add(written[len("_root_.") :])
                else:
                    ns = [n for k, n in stack if k == "namespace" and n]
                    out.add(".".join(ns + [written]))
        pos += len(line)
    return out


def known_names(base: str, head: str) -> tuple[set[str], set[str], set[str]]:
    """(full names, last components, namespaces) of every record (the base's and the ones this PR adds) and every
    declaration in the tree."""
    full: set[str] = set()
    namespaces: set[str] = set()
    for f in (ROOT / "data").glob("*/**/*.jsonl"):
        for line in f.open("rb"):
            m = re.search(rb'"name"\s*:\s*"([^"]+)"', line)
            if m:
                full.add(json.loads(b'"' + m.group(1) + b'"'))
    for _, p in changed_files(base, head):  # a record added by this PR can be referenced by it
        if match(p, ["data/*/*.jsonl", "data/*/*/*.jsonl"]):
            for _, text in added_lines(base, head, p):
                try:
                    r = json.loads(text)
                except ValueError:
                    continue
                if isinstance(r, dict) and isinstance(r.get("name"), str):
                    full.add(r["name"])
    for f in (ROOT / "Tengoku").rglob("*.lean"):
        full |= lean_full_names(f.read_text(encoding="utf-8", errors="ignore"), namespaces)
    for n in full:  # a record's or declaration's own prefix is a namespace too
        parts = n.split(".")
        namespaces.update(".".join(parts[:i]) for i in range(1, len(parts)))
    return full, {n.rsplit(".", 1)[-1] for n in full}, namespaces


# `@[to_additive]` writes the additive lemma from the multiplicative one, so `sum_range_succ` appears in no file:
# its multiplicative twin does
ADDITIVE = [("nsmul", "pow"), ("vadd", "smul"), ("sum", "prod"), ("add", "mul"), ("zero", "one"), ("neg", "inv"), ("sub", "div")]


def multiplicative(name: str) -> str:
    return "_".join(next((m for a, m in ADDITIVE if tok == a), tok) for tok in name.split("_"))


def check_page(text: str) -> list[str]:
    errors: list[str] = []
    ids: set[str] = set()
    # nothing may sit between goal blocks but the page's own text: a stray marker means a broken block
    # one page-level Suggestions part, after the goals: goals worth adding that nobody has written yet
    goal_spans = [m.span() for m in GOAL_RE.finditer(text)]
    page_level = [m for m in SUGGEST_RE.finditer(text) if not any(a <= m.start() < b for a, b in goal_spans)]
    if len(page_level) > 1:
        errors.append("at most one page-level Suggestions part (goals worth adding)")
    if page_level and goal_spans and page_level[0].start() < goal_spans[-1][1]:
        errors.append("the page-level Suggestions part (goals worth adding) goes after the last goal")
    outside = SUGGEST_RE.sub("", GOAL_RE.sub("", text))
    for marker in ("<!-- goal:", "<!-- /goal -->", "<!-- people -->", "<!-- suggestions -->"):
        if marker in outside:
            errors.append(
                f"a `{marker}` marker outside a complete goal block (each goal runs from `<!-- goal: id -->` to `<!-- /goal -->`)"
            )
    for gid, body in GOAL_RE.findall(text):
        where = f"goal {gid}"
        if not ID_RE.fullmatch(gid):
            errors.append(f"{where}: id must be lowercase letters, digits and dashes")
        if gid in ids:
            errors.append(f"{where}: id used twice")
        ids.add(gid)
        s = SUMMARY_RE.search(body)
        if not s:
            errors.append(f"{where}: needs `<summary><b>Title</b> · status</summary>`")
            status = ""
        else:
            status = s.group(2).strip()
            if status not in STATUSES:
                errors.append(f"{where}: status {status!r} is not one of {', '.join(STATUSES)}")
        people = PEOPLE_RE.findall(body)
        suggestions = SUGGEST_RE.findall(body)
        if len(people) != 1:
            errors.append(f"{where}: needs exactly one `<!-- people -->` … `<!-- /people -->` part")
            continue
        if len(suggestions) != 1:
            errors.append(f"{where}: needs exactly one `<!-- suggestions -->` … `<!-- /suggestions -->` part")
        elif body.index("<!-- suggestions -->") < body.index("<!-- /people -->"):
            errors.append(f"{where}: Suggestions go after the people part")
        fields = FIELD_RE.findall(people[0])
        for f in REQUIRED:
            if f not in fields:
                errors.append(f"{where}: missing the field `{f}`")
        for f in fields:
            if f not in REQUIRED + OPTIONAL:
                errors.append(f"{where}: unknown field `{f}` (the fields are: {', '.join(REQUIRED + OPTIONAL)})")
        if len(fields) != len(set(fields)):
            errors.append(f"{where}: a field appears twice")
        if status == "done":
            proved = people[0].split("<details><summary>Proved by</summary>", 1)
            if len(proved) != 2 or not REF_RE.search(proved[1].split("</details>", 1)[0]):
                errors.append(f"{where}: a done goal names what proved it: a `Proved by` field with a `tengoku:Name`")
    for m in LINK_RE.finditer(text):
        url = m.group(1) or m.group(2)
        if not re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", url):
            continue  # no scheme: a link inside the repository
        if not url.startswith(("https://", "http://")):
            errors.append(f"link {url!r} is not http(s)")
    return errors


def check_refs(text: str, base: str, head: str) -> list[str]:
    refs = sorted({m.group(1).rstrip(".") for m in REF_RE.finditer(text)})
    if not refs:
        return []
    full, short, namespaces = known_names(base, head)

    def exists(r: str) -> bool:
        if r in full:
            return True
        ns, _, last = r.rpartition(".")
        known_last = last in short or multiplicative(last) in short
        # a qualified name whose namespace is real and whose last part is declared somewhere (a name Lean's core
        # or an attribute like to_additive generates, which no file spells out); a bare name: any declaration
        return known_last and (not ns or ns in namespaces)

    return [f"`tengoku:{r}` names nothing in the library (no record or declaration by that name)" for r in refs if not exists(r)]


def ai_changed_people(base_text: str, head_text: str) -> bool:
    def blank(t: str) -> str:
        return SUGGEST_RE.sub("<!-- suggestions -->\n\n<!-- /suggestions -->", t)

    return blank(base_text) != blank(head_text)


def statement_type(lean: str) -> str | None:
    """What a statement claims, without its name, docstring or attributes: for comparing a goal with a record."""
    lean = re.sub(r"/-.*?-/", " ", lean, flags=re.S)
    lean = re.sub(r"--[^\n]*", " ", lean)
    m = re.search(r"(?:theorem|lemma)\s+\S+(.*)", lean, re.S)
    if not m:
        return None
    body = m.group(1).split(":=", 1)[0]
    return " ".join(body.split()) or None


def proved_goals(text: str) -> list[tuple[str, str]]:
    wanted = {}
    for gid, body in GOAL_RE.findall(text):
        s = SUMMARY_RE.search(body)
        if s and s.group(2).strip() == "done":
            continue
        people = PEOPLE_RE.findall(body)
        if not people:
            continue
        block = re.search(r"<details><summary>The statement</summary>.*?```lean\n(.*?)```", people[0], re.S)
        t = statement_type(block.group(1)) if block else None
        if t:
            wanted[t] = gid
    found = []
    if not wanted:
        return found
    for f in (ROOT / "data" / "trusted").glob("*.jsonl"):
        for line in f.open(encoding="utf-8"):
            if '"statement"' not in line:
                continue
            try:
                r = json.loads(line)
            except ValueError:
                continue
            t = statement_type(str(r.get("statement", "")))
            if t in wanted:
                found.append((wanted[t], r["name"]))
    return found


def main() -> None:
    base, head = sys.argv[1], sys.argv[2]
    files = [p for _, p in changed_files(base, head)]
    ai = os.environ.get("GOALS_AI") == "1"
    others = [p for p in files if p != PAGE]
    if ai and others:  # whether or not GOALS.md changed
        fail(f"the AI reviewer's PR may change only GOALS.md, not {', '.join(others[:5])}")
    if PAGE not in files:
        print("goals: GOALS.md unchanged")
        return
    head_text = text_at(head)
    errors = check_page(head_text) + check_refs(head_text, base, head)
    if ai and ai_changed_people(text_at(base), head_text):
        errors.append("the AI reviewer may change only the text inside Suggestions; this PR changes the part people write")
    for gid, name in proved_goals(head_text):
        print(f"goals: goal {gid} looks proved by the trusted record {name}: mark it done, with `Proved by` tengoku:{name}")
    if errors:
        fail("GOALS.md:\n  " + "\n  ".join(errors[:30]))
    print(f"goals OK ({len(GOAL_RE.findall(head_text))} goals)")


if __name__ == "__main__":
    main()
