#!/usr/bin/env python3
"""leak_canary.py [--space NAME] [--wait-refresh S] — compile the canary on a Leak space and fail when it does not compile.

The canary (scripts/ci/canary/Canary.lean) is ordinary Lean and Mathlib that must elaborate under `import Tengoku.All`. A Leak space (`verify_full_script` over MCP/SSE, the same
tool the provers use) compiles it on its pinned tree; a failure is a library of the tree that leaks into everybody else (a global instance, notation or reserved word). Exit status:
0 compiled, 1 did not compile (the lines and messages are printed), 2 the space could not be asked (unreachable, timed out): a red run either way, with a different message.
CanaryKnown.lean (bugs known to be open) is compiled too and only reported.

The space is named, not addressed: `--space` is one of SPACES (the address is the program's own constant, never a string from the command line or the workflow input), and
the tests call `run()` with a fake space on this machine. `--wait-refresh S` (after a promotion): first `--settle` seconds for the space to start its refresh, then up to S
seconds until it reports `refreshing: false`, `status: current`, and a pinned tree that is the base of the published cache pointer; exit 2 when it never does.
The space reports the base commit it has pinned, not the top-up commit it loaded on top: a promotion that only changes the top-up cannot be told apart (the scheduled run
catches it within six hours, and the merge queue's own canary judges every group before it merges).
"""

from __future__ import annotations

import argparse
import http.client
import json
import re
import sys
import threading
import time
import urllib.request
from pathlib import Path
from urllib.parse import urlsplit

HERE = Path(__file__).resolve().parent
SPACES = {"leak-iv": "https://barkingtree-leak-iv.hf.space"}  # the Leak spaces this client knows; another one is one more line here
POINTER = "https://github.com/competemath/tengoku/releases/download/cache-latest/cache-latest.json"  # the published cache pointer the spaces follow
ENDPOINT = re.compile(r"/messages/\?session_id=([0-9a-fA-F-]{8,64})")
ERROR = re.compile(r"^Line (\d+) \((Error|Warning)\): (.*)$", re.M)
RETRY_PAUSE = 30  # seconds, times the number of the attempt that failed
MAX_JSON = 1_000_000  # bytes read of a /refresh status or the cache pointer
MIN_CALL = 60  # an attempt that would get less than this is not started


class Unreachable(Exception):
    pass


LOCAL_HOSTS = ("127.0.0.1", "localhost", "::1")  # a server on this machine: the tests' fake space


def checked_space(url: str) -> str:
    """the origin of a Leak space: `https://host[:port]` (http only for a server on this machine), no credentials, no path, no query. A ValueError otherwise: the client
    sends the script it compiles to this address and follows the endpoint its stream names, so it must not be a `file:` URL or somebody else's host."""
    u = urlsplit(url.strip())
    if not (u.scheme == "https" or (u.scheme == "http" and u.hostname in LOCAL_HOSTS)):
        raise ValueError(f"the space must be an https URL (http only on this machine), not {url!r}")
    if not u.hostname or u.username or u.password or u.query or u.fragment or u.path not in ("", "/"):
        raise ValueError(f"the space must be an origin (https://host[:port]), not {url!r}")
    return f"{u.scheme}://{u.netloc}"


def as_object(raw: bytes) -> dict:
    if len(raw) > MAX_JSON:
        raise ValueError(f"more than {MAX_JSON} bytes")
    data = json.loads(raw.decode("utf-8", "replace"))
    if not isinstance(data, dict):
        raise ValueError("not a JSON object")
    return data


def read_status(base: str, timeout: float = 30.0) -> dict:
    """GET {base}/refresh of the space: http.client, so no redirect is followed and no scheme but the space's own is possible"""
    u = urlsplit(checked_space(base))
    conn = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(u.hostname, u.port, timeout=timeout)
    try:
        conn.request("GET", "/refresh")
        resp = conn.getresponse()
        raw = resp.read(MAX_JSON + 1)  # a status is a few hundred bytes: nothing longer is read
        if resp.status != 200:
            raise ValueError(f"/refresh answered {resp.status}")
    finally:
        conn.close()
    return as_object(raw)


def read_pointer(timeout: float = 30.0) -> dict:
    """the published cache pointer: this module's own constant URL (GitHub answers with a redirect to its CDN, which urllib follows)"""
    with urllib.request.urlopen(POINTER, timeout=timeout) as r:  # noqa: S310 — a constant https URL
        raw = r.read(MAX_JSON + 1)
    return as_object(raw)


def ready(status: dict, pointer: dict | None) -> tuple[bool, str]:
    """is the space on the tree the cache pointer names, and not busy: (yes/no, why not)"""
    if status.get("refreshing") is not False:
        return False, "it is refreshing"
    if status.get("status") != "current":
        return False, f"its status is {status.get('status')!r}, not 'current'"
    if pointer is None:
        return False, "the published cache pointer could not be read"
    want = pointer.get("commit")
    if not isinstance(want, str) or not want:
        return False, "the published cache pointer names no commit"
    if status.get("pinned") != want:
        return False, f"it has pinned {str(status.get('pinned'))[:12]}, the pointer names {want[:12]}"
    return True, ""


def wait_ready(base: str, settle: float, wait: float, poll: float = 30.0) -> bool:
    """after a promotion: let the space start its refresh, then poll until it is ready or `wait` seconds are over"""
    time.sleep(settle)
    deadline = time.monotonic() + wait
    why = "never asked"
    while True:
        try:
            status = read_status(base)
        except Exception as e:
            status, why = None, f"/refresh not readable ({e!r})"
        if status is not None:
            try:
                pointer = read_pointer()
            except Exception:
                pointer = None
            print("space:", json.dumps(status)[:400])
            ok, why = ready(status, pointer)
            if ok:
                print("the space follows the published cache pointer")
                if pointer and (pointer.get("topup") or {}).get("commit"):
                    print(
                        f"(the pointer also names the top-up {pointer['topup']['commit'][:12]}; the space does not report which top-up it loaded)"
                    )
                return True
        if time.monotonic() + poll > deadline:
            print(f"the space did not become ready: {why}")
            return False
        time.sleep(poll)


def call_tool(base: str, tool: str, args: dict, timeout: float = 900.0) -> str:
    """One MCP tool call over SSE: open the stream, take the message endpoint it names, initialize, call, read the reply from the stream."""
    base = checked_space(base)
    replies: dict[int, dict] = {}
    cond = threading.Condition()
    state: dict = {"endpoint": None, "dead": None}
    deadline = time.monotonic() + timeout

    def pump() -> None:
        try:
            req = urllib.request.Request(f"{base}/sse", headers={"accept": "text/event-stream"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                event, data = None, []
                for raw in resp:
                    line = raw.decode("utf-8", "replace").rstrip("\r\n")
                    if line == "":
                        with cond:
                            if event == "endpoint":
                                # the stream says where to post; only the session id is taken from it: the address is this client's (base + the path every Leak space serves)
                                m = ENDPOINT.fullmatch("\n".join(data).strip())
                                if m:
                                    state["endpoint"] = f"/messages/?session_id={m.group(1)}"
                                else:
                                    state["dead"] = Unreachable(
                                        f"the stream names an endpoint that is not /messages/?session_id=<hex>: {chr(10).join(data)[:120]!r}"
                                    )
                            elif event == "message":
                                try:
                                    msg = json.loads("\n".join(data))
                                    if isinstance(msg, dict) and msg.get("id") is not None:
                                        replies[msg["id"]] = msg
                                except ValueError:
                                    pass
                            cond.notify_all()
                        event, data = None, []
                    elif line.startswith("event:"):
                        event = line[6:].strip()
                    elif line.startswith("data:"):
                        data.append(line[5:].lstrip())
        except Exception as e:  # the stream ended or never opened
            with cond:
                state["dead"] = e
                cond.notify_all()

    threading.Thread(target=pump, daemon=True).start()

    def wait(pred) -> None:
        with cond:
            while not pred():
                if state["dead"] is not None and not pred():
                    raise Unreachable(f"{base}: the stream ended: {state['dead']!r}")
                left = deadline - time.monotonic()
                if left <= 0:
                    raise Unreachable(f"{base}: no answer in {timeout:.0f} s")
                cond.wait(min(left, 5))

    def post(body: dict) -> None:
        # http.client, not urllib: no redirect is followed and no scheme other than the connection's is possible (Snyk flagged the script travelling in a urllib Request)
        u = urlsplit(base)
        conn = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(u.hostname, u.port, timeout=60)
        try:
            conn.request("POST", state["endpoint"], body=json.dumps(body).encode(), headers={"content-type": "application/json"})
            resp = conn.getresponse()
            resp.read()
            if resp.status >= 400:
                raise Unreachable(f"{base}: POST answered {resp.status}")
        except Unreachable:
            raise
        except Exception as e:
            raise Unreachable(f"{base}: POST failed: {e!r}") from e
        finally:
            conn.close()

    wait(lambda: state["endpoint"] is not None)
    post(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": "tengoku-canary", "version": "1"},
            },
        }
    )
    wait(lambda: 1 in replies)
    post({"jsonrpc": "2.0", "method": "notifications/initialized"})
    post(
        {
            "jsonrpc": "2.0",
            "id": 2,
            "method": "tools/call",
            "params": {"name": tool, "arguments": args},
        }
    )
    wait(lambda: 2 in replies)
    out = replies[2]
    if out.get("error"):
        raise Unreachable(f"{base}: {json.dumps(out['error'])[:300]}")
    return "\n".join(c.get("text", "") for c in (out.get("result") or {}).get("content", []))


def verdict(text: str) -> tuple[str, list[tuple[int, str]]]:
    """('ok' | 'failed' | 'infra', the (line, message) of every error): the reply of verify_full_script"""
    if "Compilation Successful" in text:
        return "ok", []
    errors = [(int(m.group(1)), m.group(3)) for m in ERROR.finditer(text) if m.group(2) == "Error"]
    if re.search(r"verify exceeded|timed out|timeout|Verification Error", text) and not errors:
        return "infra", []
    return ("failed" if errors or "Compilation Failed" in text else "infra"), errors


def report(name: str, script: str, errors: list[tuple[int, str]]) -> list[str]:
    src = script.split("\n")
    out = [f"{name}: {len(errors)} error(s)"]
    for n, msg in errors[:40]:
        out.append(f"  line {n}: {src[n - 1].strip()[:110] if 0 < n <= len(src) else '?'}\n    {msg[:220]}")
    return out


def parse(argv: list[str]) -> argparse.Namespace:
    ap = argparse.ArgumentParser()
    ap.add_argument("--space", choices=sorted(SPACES), default="leak-iv", help="the Leak space (its address is SPACES' constant)")
    ap.add_argument("--settle", type=float, default=0.0, help="with --wait-refresh: seconds to let the space start its refresh first")
    ap.add_argument(
        "--wait-refresh",
        type=float,
        default=0.0,
        help="after a promotion: seconds to wait for the space to follow the published cache pointer",
    )
    # the two files are this directory's, not a path from the command line (Snyk: path traversal); the tests set `file` and `known` on the parsed arguments
    ap.set_defaults(file=str(HERE / "Canary.lean"), known=str(HERE / "CanaryKnown.lean"))
    ap.add_argument("--timeout", type=float, default=900.0)
    ap.add_argument(
        "--retries",
        type=int,
        default=2,
        help="more attempts at the canary when the space could not be asked (the known-open file gets one)",
    )
    ap.add_argument(
        "--budget",
        type=float,
        default=1800.0,
        help="seconds for the whole run, retries and pauses included (the workflow's job must outlast it)",
    )
    return ap.parse_args(argv)


def main(argv: list[str]) -> int:
    a = parse(argv)
    # the address is the constant of the name that was given: nothing of the command line is in it
    return run(next(url for name, url in SPACES.items() if name == a.space), a)


def run(base: str, a: argparse.Namespace) -> int:
    if a.wait_refresh > 0 and not wait_ready(base, a.settle, a.wait_refresh):
        return 2
    try:  # which tree the space has pinned, for the log
        print("space:", json.dumps(read_status(base))[:400])
    except Exception as e:
        print(f"space: /refresh not readable ({e!r})")
    results = {}
    start = time.monotonic()

    def left() -> float:
        return a.budget - (time.monotonic() - start)

    for label, path in (("canary", a.file), ("known open", a.known)):
        if not Path(path).is_file():
            continue
        script = Path(path).read_text(encoding="utf-8")
        tries = (
            a.retries + 1 if label == "canary" else 1
        )  # the known-open file is only reported: a slow space must not eat the canary's time
        for attempt in range(tries):
            if left() < MIN_CALL:
                kind, errors, text = "infra", [], f"the {a.budget:.0f} s budget of this run is used up"
                break
            try:
                text = call_tool(base, "verify_full_script", {"script": script}, min(a.timeout, left()))
                kind, errors = verdict(text)
            except Unreachable as e:
                kind, errors, text = "infra", [], str(e)
            if kind != "infra" or attempt == tries - 1:
                break
            time.sleep(max(0.0, min(RETRY_PAUSE * (attempt + 1), left())))
        results[label] = (kind, errors, script, text)
        print(f"{label}: {kind}")
        if kind == "failed":
            print("\n".join(report(label, script, errors)))
        if kind == "infra":
            print(f"  could not ask the space: {text[:300]}")
    kind = results.get("canary", ("infra",))[0]
    return {"ok": 0, "failed": 1}.get(kind, 2)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
