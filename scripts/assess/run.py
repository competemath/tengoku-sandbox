#!/usr/bin/env python3
"""Blind re-proof test — run it yourself before opening a PR with ORIGINAL theorems.

    python3 scripts/assess/run.py data/staging/<library>/<your-file>.jsonl --headlines Name.one,Name.two

For each headline (at most ten) a fresh Claude Code agent, on YOUR subscription,
sees only the statement and gets about 5 minutes (hard stop at 7) with the hosted
library services: search, proof states, verification. They hold the library as it
is on main, so without your PR. Everything the agent says and does is recorded.

It writes, next to your records, the three things the PR must carry:

    claims/<your-file>/claim.json                        what happened, with digests
    claims/<your-file>/<n>-<Name>.working.md             the attempt, readable
    claims/<your-file>/<n>-<Name>.transcript.jsonl.gz    the attempt, raw

If EVERY headline is re-proved, the PR would be rejected: the library could
already reach all of it in minutes. If at least one resists, it passes this test.
Needs the `claude` CLI, logged in. Standard library only.
"""

from __future__ import annotations

import argparse
import json
import os
import queue
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

HOME = str(Path.home())


def pinned(services: dict) -> dict:
    out = {}
    for name, url in services.items():
        try:
            with urllib.request.urlopen(url + "/refresh", timeout=60) as r:
                out[name] = json.loads(r.read()).get("pinned", "")
        except Exception as e:
            sys.exit(f"cannot reach the {name} service at {url}: {e}")
    return out


def sanitise(ev: dict) -> dict | None:
    """Keep what the attempt consisted of; drop what identifies the machine it ran on."""
    t = ev.get("type")
    if t == "system" and ev.get("subtype") == "init":
        keep = {
            "type": "system",
            "subtype": "init",
            "model": ev.get("model"),
            "tools": ev.get("tools"),
            "mcp_servers": [{"name": s.get("name"), "status": s.get("status")} for s in ev.get("mcp_servers") or []],
        }
    elif t == "assistant":
        msg = ev.get("message") or {}
        content = [
            {k: c.get(k) for k in ("type", "text", "id", "name", "input") if k in c}
            for c in msg.get("content") or []
            if c.get("type") in ("text", "tool_use")
        ]
        keep = {
            "type": "assistant",
            "message": {
                "model": msg.get("model"),
                "content": content,
                "usage": {k: v for k, v in (msg.get("usage") or {}).items() if isinstance(v, int)},
            },
        }
    elif t == "user":
        content = (ev.get("message") or {}).get("content")
        if not isinstance(content, list):
            return None
        keep = {
            "type": "user",
            "message": {
                "content": [
                    {k: c.get(k) for k in ("type", "tool_use_id", "content", "is_error") if k in c}
                    for c in content
                    if c.get("type") == "tool_result"
                ]
            },
        }
    elif t == "result":
        keep = {k: ev.get(k) for k in ("type", "subtype", "duration_ms", "num_turns", "total_cost_usd", "is_error")}
    else:
        return None
    return json.loads(json.dumps(keep, ensure_ascii=False).replace(HOME, "~"))


WARMUP_S = (15, 30, 60)  # the CLI connects to the services in the background; the prompt is sent once they are up


def user_message(text: str) -> str:
    return json.dumps({"type": "user", "message": {"role": "user", "content": [{"type": "text", "text": text}]}}) + "\n"


def attempt(record: dict, args, services: dict, pins: dict) -> list[dict]:
    """One blind attempt. The clock starts when the agent receives the statement, with every service connected."""
    mcp = {"mcpServers": {name: {"type": "sse", "url": url + "/sse"} for name, url in services.items()}}
    cmd = [args.claude, "-p", "--input-format", "stream-json", "--output-format", "stream-json", "--verbose", "--model", args.model, "--tools", "", "--strict-mcp-config",
           "--mcp-config", json.dumps(mcp), "--allowedTools", *C.ALLOWED_TOOLS, "--disallowedTools", *[f"mcp__{s}__tengoku_sync" for s in services]]  # fmt: skip
    prompt = C.prompt_for(record)
    head = {"t": 0.0, "kind": "runner", "version": C.VERSION, "headline": record["name"], "statement_sha256": C.sha256(C.theorem_text(record)), "prompt": prompt,
            "budget": {"soft_s": args.soft, "hard_s": args.hard}, "services": services, "pinned": pins, "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}  # fmt: skip
    for warmup in WARMUP_S:
        work = tempfile.mkdtemp(prefix="tengoku-blind-")  # an empty directory: nothing of the PR is within reach
        proc = subprocess.Popen(
            cmd, cwd=work, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True
        )
        q: queue.Queue = queue.Queue()

        def pump(p=proc, q=q):
            for ln in p.stdout:
                q.put(ln)
            q.put(None)  # the CLI has exited

        threading.Thread(target=pump, daemon=True).start()
        lines, end, ready, calls_at_last_stop = [dict(head)], None, None, -1
        try:
            time.sleep(args.warmup if args.warmup is not None else warmup)
            if proc.poll() is not None:
                sys.exit(
                    "the claude CLI exited before the attempt began (is it logged in? try `claude -p hello`):\n"
                    + (proc.stderr.read() or "")[-800:]
                )
            proc.stdin.write(user_message(prompt))
            proc.stdin.flush()
            start = time.time()
            while end is None:
                now = time.time() - start
                if now >= args.hard:
                    end = "hard-limit"
                    break
                try:
                    raw = q.get(timeout=1)
                except queue.Empty:
                    continue
                if raw is None:
                    end = "cli-exit"
                    break
                try:
                    ev = json.loads(raw)
                except ValueError:
                    continue
                kept = sanitise(ev)
                if kept is None:
                    continue
                lines.append({"t": round(time.time() - start, 2), "kind": "event", "event": kept})
                if kept.get("subtype") == "init" and ready is None:
                    up = {s["name"] for s in kept.get("mcp_servers") or [] if s.get("status") == "connected"}
                    ready = up >= set(services) and set(C.ALLOWED_TOOLS) <= set(kept.get("tools") or [])
                    if not ready:
                        break  # the agent would be working without its tools: not an attempt. Start over with a longer warm-up.
                elif kept["type"] == "user":
                    if C.measure(lines, record)["outcome"] == "closed":
                        end = "closed"
                    else:
                        print(f"    {lines[-1]['t']:6.1f}s  {str(C.steps(lines)[-1]['tool']).split('__')[-1]}", flush=True)
                elif kept["type"] == "result":  # the agent stopped by itself
                    now = time.time() - start
                    calls = sum(1 for s in C.steps(lines) if s["tool"])
                    if calls == calls_at_last_stop and now < args.soft - 15:  # a turn of pure talk: do not hammer it
                        time.sleep(min(args.idle, max(0.0, args.soft - 15 - now)))
                        now = time.time() - start
                    calls_at_last_stop = calls
                    if now >= args.soft - 15:
                        end = "soft-budget"
                    else:
                        say = C.continue_prompt(int(args.soft - now))
                        lines.append({"t": round(now, 2), "kind": "runner", "continue": say})
                        proc.stdin.write(user_message(say))
                        proc.stdin.flush()
        finally:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except Exception:
                proc.kill()
            proc.wait()
            shutil.rmtree(work, ignore_errors=True)
        if ready:
            lines.append({"t": round(time.time() - start, 2), "kind": "runner", "end": end, "seconds": round(time.time() - start, 1)})
            return lines
        print(f"    the services were not all connected after {warmup} s; starting over with a longer warm-up", flush=True)
    sys.exit(
        "the library's services could not all be reached from the claude CLI (are they up? https://barkingtree-leak-iv.hf.space/refresh)"
    )


def rerender(d: Path) -> int:
    """Rewrite the working logs and digests of an existing claim from its transcripts (after the renderer changed)."""
    claim = json.loads((d / "claim.json").read_text())
    records = {
        r["name"]: r for r in (json.loads(ln) for ln in Path(claim["records"]).read_text().splitlines() if ln.strip()) if "name" in r
    }
    for h in claim["headlines"]:
        (d / h["working"]).write_text(C.render_working(C.read_transcript(d / h["transcript"]), records[h["name"]]))
        h["working_sha256"] = C.sha256((d / h["working"]).read_bytes())
    claim["digest"] = C.digest(claim)
    (d / "claim.json").write_text(json.dumps(claim, indent=2, ensure_ascii=False) + "\n")
    print(f"re-rendered {len(claim['headlines'])} working log(s) in {d}")
    return 0


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "--rerender":
        return rerender(Path(sys.argv[2]))
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("records", type=Path, help="your staging file (one JSON record per line)")
    ap.add_argument(
        "--headlines", default="", help="comma-separated record names, at most ten (default: every record, if there are at most ten)"
    )
    ap.add_argument("--out", type=Path, help="default: claims/<records file name>/")
    ap.add_argument("--model", default="sonnet")
    ap.add_argument("--claude", default=os.environ.get("TENGOKU_ASSESS_CLAUDE", "claude"))
    ap.add_argument("--soft", type=int, default=C.SOFT_S, help=argparse.SUPPRESS)
    ap.add_argument("--hard", type=int, default=C.HARD_S, help=argparse.SUPPRESS)
    ap.add_argument("--warmup", type=float, default=None, help=argparse.SUPPRESS)
    ap.add_argument("--idle", type=float, default=C.IDLE_PAUSE_S, help=argparse.SUPPRESS)
    args = ap.parse_args()

    records = [json.loads(ln) for ln in args.records.read_text().splitlines() if ln.strip()]
    by_name = {r["name"]: r for r in records if "name" in r and "statement" in r}
    names = [n for n in args.headlines.split(",") if n] or list(by_name)
    missing = [n for n in names if n not in by_name]
    if missing:
        sys.exit(f"not in {args.records}: {', '.join(missing)}")
    if not 1 <= len(names) <= C.MAX_HEADLINES:
        sys.exit(f"name between 1 and {C.MAX_HEADLINES} headlines with --headlines (the file has {len(by_name)} records)")
    if not shutil.which(args.claude):
        sys.exit("the `claude` CLI is not installed (https://claude.com/claude-code); it runs the attempt on your own subscription")

    services = json.loads(os.environ.get("TENGOKU_ASSESS_SERVICES") or "null") or C.SERVICES
    out = args.out or Path("claims") / args.records.stem
    out.mkdir(parents=True, exist_ok=True)
    pins = pinned(services)
    print(f"library as the services hold it: {', '.join(f'{k} {v[:12]}' for k, v in pins.items())}")
    who = (
        subprocess.run(["git", "config", "user.name"], capture_output=True, text=True).stdout.strip(),
        subprocess.run(["git", "config", "user.email"], capture_output=True, text=True).stdout.strip(),
    )

    headlines = []
    for i, name in enumerate(names, 1):
        rec = by_name[name]
        print(f"[{i}/{len(names)}] {name}: blind attempt, about {args.soft // 60} minutes (hard stop {args.hard // 60})", flush=True)
        lines = attempt(rec, args, services, pins)
        m = C.measure(lines, rec)
        stem = f"{i}-{C.slug(name)}"
        C.write_transcript(out / f"{stem}.transcript.jsonl.gz", lines)
        (out / f"{stem}.working.md").write_text(C.render_working(lines, rec))
        headlines.append({"name": name, "statement_sha256": C.sha256(C.theorem_text(rec)), "outcome": m["outcome"], "seconds": m["seconds"], "calls": m["calls"], "models": m["models"],
                          "working": f"{stem}.working.md", "working_sha256": C.sha256((out / f"{stem}.working.md").read_bytes()),
                          "transcript": f"{stem}.transcript.jsonl.gz", "transcript_sha256": C.sha256((out / f"{stem}.transcript.jsonl.gz").read_bytes())})  # fmt: skip
        print(
            f"    → {m['outcome'].upper()} after {m['seconds']} s ({m['calls']['search']} searches, {m['calls']['states']} proof-state steps, {m['calls']['verify']} verifications)",
            flush=True,
        )

    claim = {"version": C.VERSION, "records": str(args.records), "headlines": headlines, "others": sorted(set(by_name) - set(names)), "budget": {"soft_s": args.soft, "hard_s": args.hard},
             "services": services, "pinned_start": pins, "pinned_end": pinned(services), "runner_sha256": C.sha256(Path(__file__).read_bytes()), "common_sha256": C.sha256(Path(C.__file__).read_bytes()),
             "attested_by": f"{who[0]} <{who[1]}>", "made_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}  # fmt: skip
    claim["digest"] = C.digest(claim)
    (out / "claim.json").write_text(json.dumps(claim, indent=2, ensure_ascii=False) + "\n")
    resisted = [h["name"] for h in headlines if h["outcome"] == "resisted"]
    print()
    if resisted:
        print(
            f"PASSES this test: {len(resisted)} of {len(headlines)} headline(s) resisted a blind re-proof. Commit {out}/ with your records (git commit -s)."
        )
        return 0
    print(
        f"WOULD BE REJECTED: all {len(headlines)} headline(s) were re-proved from the existing library in minutes. {out}/ records it; the PR gate reads the same files."
    )
    return 3


if __name__ == "__main__":
    sys.exit(main())
