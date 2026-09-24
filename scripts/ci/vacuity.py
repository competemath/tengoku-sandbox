#!/usr/bin/env python3
"""vacuity.py <base> <head> <pr body file> — a new theorem whose hypotheses can never all hold
must be acknowledged. Builds the PR's candidate modules (the same modules the merge queue builds),
runs tools/vacuity/vacuity.lean on them, and fails while any reported theorem lacks a line

    Vacuous-Ack: <theorem name>: <why the empty hypothesis set is intended>

in the PR description. Runs before the queue on purpose: after it, nobody would look.
`VACUITY_REPORT=<file>` replaces the build and the run with a saved report (tests)."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

from _git import ROOT, added_lines, changed_files, fail

base, head, body_path = sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else ""
body = open(body_path, encoding="utf-8").read() if body_path and os.path.exists(body_path) else ""
ACK = re.compile(r"^\s*Vacuous-Ack:\s*([^\s:]+)\s*:\s*(\S.*\S|\S)\s*$", re.M | re.I)
acks = {name: reason for name, reason in ACK.findall(body)}


def record_names() -> set[str]:
    """The names of the records this PR adds (one JSON object per added line under data/)."""
    names: set[str] = set()
    for status, path in changed_files(base, head):
        if status == "D" or not path.startswith("data/") or not path.endswith(".jsonl"):
            continue
        for _, text in added_lines(base, head, path):
            try:
                names.add(str(json.loads(text).get("name", "")))
            except (ValueError, AttributeError):
                pass
    return names - {""}


def ack_for(full: str) -> str | None:
    """The reason acknowledging `full`. The checker reports the name with the namespaces the module opens
    around the record; the author knows the name as the record writes it, so a PR record's name that
    ends `full` acknowledges it too. Any shorter tail does not."""
    if full in acks:
        return acks[full]
    for name, reason in acks.items():
        if name in records and (full == name or full.endswith("." + name)):
            return reason
    return None


def candidate_targets() -> list[str]:
    r = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "ci" / "queue_targets.py"), base, head], cwd=ROOT, capture_output=True, text=True
    )
    if r.returncode != 0:
        fail(f"could not determine the PR's candidate modules:\n{r.stderr[-1500:]}")
    return [line.strip() for line in r.stdout.splitlines() if line.strip() and line.startswith("Tengoku.")]


def report_for(targets: list[str]) -> str:
    saved = os.environ.get("VACUITY_REPORT")
    if saved:
        return open(saved, encoding="utf-8").read()
    build = subprocess.run(["lake", "build", *targets], cwd=ROOT, capture_output=True, text=True)
    if build.returncode != 0:
        # A candidate that does not build cannot be assessed; the queue says why. A push that fixes it re-runs this check.
        print("vacuity: the candidate modules did not build, so nothing was assessed (the merge queue reports build errors):")
        print((build.stdout + build.stderr)[-1200:])
        sys.exit(0)
    run = subprocess.run(
        ["lake", "env", "lean", "--run", str(ROOT / "tools" / "vacuity" / "vacuity.lean"), *targets],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if run.returncode != 0:
        fail(f"the vacuity checker itself failed:\n{(run.stdout + run.stderr)[-1500:]}")
    return run.stdout


def parse(report: str) -> list[tuple[str, str, str, list[str]]]:
    """(theorem, module, tactic, hypotheses) per VACUOUS block."""
    found: list[tuple[str, str, str, list[str]]] = []
    for line in report.splitlines():
        m = re.match(r"^VACUOUS (\S+) (\S+) (\S+)$", line)
        if m:
            found.append((m.group(1), m.group(2), m.group(3), []))
        elif found and line.startswith("    "):
            found[-1][3].append(line.strip())
    return found


targets = candidate_targets() if not os.environ.get("VACUITY_REPORT") or os.environ.get("VACUITY_TARGETS") != "0" else ["Tengoku.Test"]
if not targets:
    print("vacuity OK: this PR adds no theorem the queue would compile")
    sys.exit(0)
vacuous = parse(report_for(targets))
if not vacuous:
    print(f"vacuity OK: every new theorem's hypotheses can hold together ({len(targets)} candidate modules)")
    sys.exit(0)

records = record_names() if acks else set()
unacked = [v for v in vacuous if ack_for(v[0]) is None]
for name, _, _, _ in vacuous:
    if ack_for(name) is not None:
        print(f"vacuity: {name} is vacuous and acknowledged: {ack_for(name)}")
if not unacked:
    print("vacuity OK: every vacuous theorem is acknowledged in the description")
    sys.exit(0)

lines = [f"{len(unacked)} new theorem{'s' if len(unacked) > 1 else ''} whose hypotheses can never all hold:"]
for name, module, tactic, hyps in unacked:
    lines.append(f"  {name} ({module}): `{tactic}` derives a contradiction from")
    lines += [f"      {h}" for h in hyps] or ["      (its binders alone)"]
lines += [
    "",
    "Such a theorem is vacuously true: no case satisfies its assumptions, so whatever it claims, it",
    "proves nothing. Usually one hypothesis is wrong — a `<` that should be `≤`, a bound on the wrong",
    "variable, a condition a natural number cannot meet. Fix the statement and push.",
    "",
    "If it is intended (the theorem records that these hypotheses are incompatible, or it faithfully",
    "translates a source that has it), say so: add one line per theorem to the PR description and the",
    "gate re-runs (the name as your record writes it is accepted too, without the namespaces the module",
    "opens around it):",
    "",
]
lines += [f"  Vacuous-Ack: {name}: <why the empty hypothesis set is intended>" for name, _, _, _ in unacked]
fail("\n".join(lines))
