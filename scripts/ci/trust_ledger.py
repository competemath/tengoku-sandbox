#!/usr/bin/env python3
"""trust_ledger.py verdict|label — append to the trust ledger, an append-only hash-chained JSONL on the `trust-ledger` branch.

  trust_ledger.py verdict --dir DIR            DIR holds verdict.json (the judge's output) written by an earlier, read-only job
  trust_ledger.py label --head SHA --label accept|reject --by LOGIN

Holds the only write permission of the trust workflows and takes only validated JSON, never a PR's files or text it would
interpret. Writes through the contents API: the file's blob sha is a compare-and-swap, so a racing writer makes this one
re-read and try again instead of overwriting (no git push, per workflow_rules.py). The chain is the juridicator's own
(`entry_hash` of its ledger module, from the pinned checkout in $TRUST_TOOLS) and is verified before every append."""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import subprocess
import sys
from pathlib import Path

SHA = re.compile(r"^[0-9a-f]{40}$")
LOGIN = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$")
DECISIONS = {"ACCEPT", "HOLD", "ESCALATE", "REJECT"}
BRANCH = os.environ.get("TRUST_LEDGER_BRANCH", "trust-ledger")  # the override is for rehearsals on a scratch branch
PATH = "ledger.jsonl"
MAX_BYTES = 900_000
ATTEMPTS = 6


def tools() -> None:
    sys.path.insert(0, str(Path(os.environ["TRUST_TOOLS"]) / "tengoku-juridicator"))


def validate_verdict(v: object) -> dict:
    if not isinstance(v, dict) or v.get("schema") != "tengoku-verdict/1" or v.get("decision") not in DECISIONS:
        raise ValueError("not a verdict")
    case = v.get("case")
    if not isinstance(case, dict) or not SHA.match(str(case.get("head_sha"))):
        raise ValueError("the verdict names no commit")
    if len(json.dumps(v)) > 60_000:
        raise ValueError("verdict too large")
    return v


def append_entry(text: str, kind: str, body: dict) -> str:
    """The ledger text with one entry added, after checking the chain. Raises ValueError on a broken chain."""
    tools()
    from juridicator.ledger import GENESIS, entry_hash

    prev, n = GENESIS, 0
    for line in text.splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        if e.get("seq") != n or e.get("prev") != prev or e.get("hash") != entry_hash(n, e.get("kind", ""), e.get("body", {}), prev):
            raise ValueError(f"the ledger chain is broken at entry {n}; not appending")
        prev, n = e["hash"], n + 1
    entry = {"seq": n, "kind": kind, "body": body, "prev": prev, "hash": entry_hash(n, kind, body, prev)}
    return text + json.dumps(entry, sort_keys=True, ensure_ascii=False) + "\n"


def gh(*args: str, payload: dict | None = None) -> tuple[int, str]:
    done = subprocess.run(["gh", "api", *args], input=json.dumps(payload) if payload else None, capture_output=True, text=True, check=False)
    return done.returncode, done.stdout if done.returncode == 0 else done.stderr


def append_remote(repo: str, kind: str, body: dict) -> int:
    for attempt in range(1, ATTEMPTS + 1):
        rc, out = gh(f"repos/{repo}/contents/{PATH}?ref={BRANCH}")
        if rc != 0:
            print(f"trust_ledger: cannot read {BRANCH}:{PATH} ({out.strip()[:200]}); is the branch created?", file=sys.stderr)
            return 1
        meta = json.loads(out)
        text = base64.b64decode(meta["content"]).decode("utf-8") if meta.get("content") else ""
        if len(text) > MAX_BYTES:
            print("trust_ledger: the ledger file is too large for the contents API; rotate it", file=sys.stderr)
            return 1
        new = append_entry(text, kind, body)
        rc, out = gh(
            "-X",
            "PUT",
            f"repos/{repo}/contents/{PATH}",
            "--input",
            "-",
            payload={
                "message": f"ledger: {kind} {body.get('case', {}).get('head_sha', body.get('head_sha', ''))[:12]}",
                "content": base64.b64encode(new.encode("utf-8")).decode("ascii"),
                "sha": meta["sha"],
                "branch": BRANCH,
            },
        )
        if rc == 0:
            print(f"appended {kind} (attempt {attempt})")
            return 0
        print(f"trust_ledger: attempt {attempt} lost a race or failed: {out.strip()[:160]}", file=sys.stderr)
    return 1


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="trust_ledger")
    sub = ap.add_subparsers(dest="cmd", required=True)
    v = sub.add_parser("verdict")
    v.add_argument("--dir", required=True)
    lb = sub.add_parser("label")
    lb.add_argument("--head", required=True)
    lb.add_argument("--label", required=True, choices=["accept", "reject"])
    lb.add_argument("--by", required=True)
    args = ap.parse_args(argv)
    repo = os.environ["GITHUB_REPOSITORY"]
    try:
        if args.cmd == "verdict":
            verdict = validate_verdict(json.loads((Path(args.dir) / "verdict.json").read_text(encoding="utf-8")))
            return append_remote(repo, "verdict", verdict)
        if not SHA.match(args.head) or not LOGIN.match(args.by):
            raise ValueError("bad head or login")
        return append_remote(repo, "label", {"repo": repo, "head_sha": args.head, "label": args.label, "by": args.by})
    except (ValueError, OSError, KeyError) as exc:
        print(f"trust_ledger: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
