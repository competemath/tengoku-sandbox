#!/usr/bin/env python3
"""assess.py <base> <head> [--promotion] — the blind re-proof test (scripts/assess/).

A PR that adds ORIGINAL theorems to staging (records whose source is not one of the
`translations` in schemas/sources.json) must carry a claim: the record of a blind
attempt to re-prove up to ten headline theorems in 5 minutes (hard stop at 7) from
the library as it was without the PR. If EVERY headline was re-proved, the PR is
rejected. Otherwise it passes — provided the record is credible, which is what
most of this file checks: nothing in the claim is taken on trust, every number is
recomputed from the raw transcript, and the readable log is rendered again and
compared byte for byte. Translations and promotions are exempt."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "assess"))
import common as C  # noqa: E402
from _git import ROOT, added_lines, blob, changed_files, fail, load_schema, match  # noqa: E402

base, head = sys.argv[1], sys.argv[2]
SECRET = re.compile(
    r"AKIA[0-9A-Z]{16}|gh[pousr]_[A-Za-z0-9]{36,}|github_pat_[A-Za-z0-9_]{40,}|sk-ant-[A-Za-z0-9_-]{20,}|hf_[A-Za-z0-9]{30,}|-----BEGIN [A-Z ]*PRIVATE KEY-----"
)


def say(text: str) -> None:
    print(text)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as f:
            f.write(text + "\n")


if "--promotion" in sys.argv:
    say("exempt: a promotion moves records that were assessed when they entered staging")
    sys.exit(0)

translations = load_schema("sources.json").get("translations", [])
files = changed_files(base, head)
original: dict[str, dict] = {}
for st, p in files:
    if st != "D" and match(p, ["data/staging/*.jsonl", "data/staging/*/*.jsonl"]):
        for _, text in added_lines(base, head, p):
            try:
                r = json.loads(text)
            except ValueError:
                continue
            if "tombstone" in r or not r.get("name") or not r.get("statement"):
                continue
            if not any(str(r.get("source_url", "")).startswith(t) for t in translations):
                original[r["name"]] = r
if not original:
    say("exempt: this PR adds no original theorems (translations of existing libraries are not assessed)")
    sys.exit(0)

claims = [p for st, p in files if st != "D" and match(p, ["claims/*/claim.json"])]
HOWTO = "Run `python3 scripts/assess/run.py <your staging file> --headlines <up to ten names>` and commit the `claims/` directory it writes (CONTRIBUTING.md, 'Original theorems')."
if not claims:
    fail(
        f"this PR adds {len(original)} original theorem(s) ({', '.join(list(original)[:4])}{'…' if len(original) > 4 else ''}) and carries no blind re-proof claim. {HOWTO}"
    )

problems: list[str] = []
rows: list[tuple[str, str, float, dict]] = []
signers = set(
    re.findall(
        r"Signed-off-by:.*<([^>]+)>",
        subprocess.run(["git", "log", "--format=%B", f"{base}..{head}"], cwd=ROOT, capture_output=True, text=True).stdout,
    )
)
services = json.loads(os.environ.get("TENGOKU_ASSESS_SERVICES") or "null") or C.SERVICES  # the override exists for the unit tests


def known_on_main(commit: str) -> bool:
    if not re.fullmatch(r"[0-9a-f]{40}", commit or ""):
        return False
    # main as the gate sees it now (the services follow main, so they may be ahead of the PR's own base)
    return any(
        subprocess.run(["git", "merge-base", "--is-ancestor", commit, ref], cwd=ROOT, capture_output=True).returncode == 0
        for ref in ("origin/main", base)
    )


for claim_path in claims:
    d = str(Path(claim_path).parent)
    try:
        claim = json.loads(blob(head, claim_path) or b"")
    except ValueError:
        problems.append(f"{claim_path}: not JSON")
        continue

    def bad(msg: str, where: str = d) -> None:
        problems.append(f"{where}: {msg}")

    if claim.get("version") != C.VERSION:
        bad(f"claim version {claim.get('version')}, this gate reads version {C.VERSION}: run the test again")
        continue
    if claim.get("digest") != C.digest(claim):
        bad("the claim's digest does not match its contents (edited after the run?)")
    if claim.get("budget") != {"soft_s": C.SOFT_S, "hard_s": C.HARD_S}:
        bad(f"budget {claim.get('budget')} is not the test's {C.SOFT_S}/{C.HARD_S} s")
    if claim.get("services") != services:
        bad("the attempt did not use the library's hosted services")
    who = re.search(r"<([^>]+)>", claim.get("attested_by") or "")
    if not who or who.group(1) not in signers:
        bad(f"attested by {claim.get('attested_by')!r}, who signed off no commit of this PR (git commit -s)")
    for when in ("pinned_start", "pinned_end"):
        for svc, commit in (claim.get(when) or {}).items():
            if not known_on_main(commit):
                bad(
                    f"{when}: the {svc} service reported {str(commit)[:12] or 'nothing'}, which is not a commit of main — the attempt must run against the library without this PR"
                )
    for h in claim.get("headlines") or []:
        name = h.get("name", "?")
        where = f"{d} / {name}"
        rec = original.get(name)
        if rec is None:
            bad("is not an original theorem added by this PR", where)
            continue
        raw_t, raw_w = blob(head, f"{d}/{h.get('transcript')}"), blob(head, f"{d}/{h.get('working')}")
        if raw_t is None or raw_w is None:
            bad("its transcript or working log is not in the PR", where)
            continue
        if C.sha256(raw_t) != h.get("transcript_sha256") or C.sha256(raw_w) != h.get("working_sha256"):
            bad("transcript or working log does not match the digest in the claim", where)
            continue
        try:
            import gzip

            lines = [json.loads(x) for x in gzip.decompress(raw_t).decode().splitlines() if x.strip()]
            first = lines[0]
        except Exception as e:
            bad(f"unreadable transcript ({type(e).__name__})", where)
            continue
        if SECRET.search(gzip.decompress(raw_t).decode("utf-8", "replace")):
            bad(
                "something that looks like a credential is in the transcript — remove the claim from the branch history and rotate it",
                where,
            )
        if h.get("statement_sha256") != C.sha256(C.theorem_text(rec)) or first.get("statement_sha256") != h.get("statement_sha256"):
            bad("the attempt was made on a different statement than the record in this PR", where)
        if first.get("prompt") != C.prompt_for(rec):
            bad("the instructions the agent was given are not the test's (edited, or the test changed since): run it again", where)
        if first.get("budget") != claim.get("budget") or first.get("services") != claim.get("services"):
            bad("transcript and claim disagree about budget or services", where)
        m = C.measure(lines, rec)
        init = next(((x.get("event") or {}) for x in lines if (x.get("event") or {}).get("subtype") == "init"), {})
        builtin = [t for t in init.get("tools") or [] if not re.match(r"mcp__(search|states|verify)__", t)]
        if builtin or m["foreign_tools"]:
            bad(
                f"not blind: the agent had or used tools outside the library's services ({', '.join((builtin + m['foreign_tools'])[:4])})",
                where,
            )
        if m["outcome"] != h.get("outcome") or m["calls"] != h.get("calls") or abs(m["seconds"] - float(h.get("seconds", -99))) > 2:
            bad(
                f"the claim says {h.get('outcome')} in {h.get('seconds')} s with {h.get('calls')}; the transcript shows {m['outcome']} in {m['seconds']} s with {m['calls']}",
                where,
            )
        if not m["monotonic"] or m["longest_silence"] > C.MAX_SILENCE_S:
            bad(
                f"the record has a gap of {m['longest_silence']} s (limit {C.MAX_SILENCE_S}) or runs backwards: not one continuous attempt",
                where,
            )
        if m["outcome"] == "resisted":
            total = sum(m["calls"].values())
            if (
                m["seconds"] < C.MIN_RESISTED_S
                or m["calls"]["verify"] < C.MIN_RESISTED_VERIFY
                or total < C.MIN_RESISTED_CALLS
                or m["ended"] not in ("soft-budget", "hard-limit")
            ):
                bad(
                    f"'resisted' needs a full attempt: at least {C.MIN_RESISTED_S} s, {C.MIN_RESISTED_VERIFY} verifications and {C.MIN_RESISTED_CALLS} calls, run to the budget. This one: {m['seconds']} s, {m['calls']['verify']} verifications, {total} calls, ended '{m['ended']}'",
                    where,
                )
        if raw_w.decode("utf-8", "replace") != C.render_working(lines, rec):
            bad(
                "the working log is not what the transcript renders to (edited by hand, or rendered by an older version: `python3 scripts/assess/run.py --rerender "
                + d
                + "`)",
                where,
            )
        rows.append((name, m["outcome"], m["seconds"], m["calls"]))

names = [r[0] for r in rows]
if len(set(names)) != len(names):
    problems.append("a headline appears twice")
if not 1 <= len(rows) <= C.MAX_HEADLINES and not problems:
    problems.append(f"{len(rows)} headlines: a PR names between 1 and {C.MAX_HEADLINES}")

if rows:
    say("| headline | outcome | seconds | searches | proof-state steps | verifications |\n| --- | --- | --- | --- | --- | --- |")
    for name, outcome, secs, calls in rows:
        say(f"| `{name}` | **{outcome}** | {secs} | {calls['search']} | {calls['states']} | {calls['verify']} |")
if problems:
    fail("the blind re-proof claim does not hold up:\n- " + "\n- ".join(problems) + f"\n{HOWTO}")
if all(outcome == "closed" for _, outcome, _, _ in rows):
    fail(f"every headline ({len(rows)}) was re-proved from the existing library inside the {C.HARD_S // 60}-minute limit, so this PR adds nothing the library could not already reach. "
         "Name theorems that carry the contribution as headlines, or build towards a result that resists.")  # fmt: skip
resisted = [n for n, o, _, _ in rows if o == "resisted"]
say(f"\npasses the blind re-proof test: {len(resisted)} of {len(rows)} headline(s) resisted ({', '.join(resisted[:5])})")
