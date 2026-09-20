"""The blind re-proof test: what the runner (scripts/assess/run.py) and the gate
(scripts/ci/assess.py) must agree on. Standard library only.

A PR that adds ORIGINAL theorems (not translations of an existing library) names
up to ten of them as headlines. For each, an agent that sees only the statement
gets 5 minutes (hard stop at 7) and the hosted services — search, proof states,
verification — which hold the library WITHOUT the PR. If every headline is
re-proved, the PR adds nothing the library could not already reach: rejected.
If at least one resists, the PR passes this test.

Everything the agent said and did is recorded. The readable working log is
rendered FROM the raw transcript by `render_working`, and the gate renders it
again and compares, so the log a reviewer reads cannot drift from what happened.
"""

from __future__ import annotations

import base64
import gzip
import hashlib
import json
import re
from pathlib import Path

VERSION = 1
SOFT_S = 300  # the agent is told it has about this long; a run that has not closed is kept going until here
HARD_S = 420  # and is stopped here, whatever it is doing
MAX_HEADLINES = 10
# A run that "resisted" must show real work; anything thinner than this is not evidence.
MIN_RESISTED_S = SOFT_S - 20  # the runner stops prompting an agent that has stopped by itself 15 s before the budget
MIN_RESISTED_CALLS = 10  # of any kind: an agent that steps through proof states and never submits a full script is still working
IDLE_PAUSE_S = 15  # after a turn without a single tool call, wait this long before saying "keep going" (seen live: 32 prompts in a minute)
MAX_SILENCE_S = 150  # longest gap between two recorded events (a laptop asleep is not an attempt)

SERVICES = {
    "search": "https://barkingtree-leak-i.hf.space",
    "states": "https://barkingtree-leak-ii.hf.space",
    "verify": "https://barkingtree-leak-iv.hf.space",
}
TOOLS = {
    "search": ["loogle_search", "moogle_search"],
    "states": ["init_proof", "apply_tactic", "get_current_proof_state", "snapshot_state", "branch_tactics", "cleanup_memory"],
    "verify": ["verify_full_script"],
}
ALLOWED_TOOLS = [f"mcp__{server}__{tool}" for server, tools in TOOLS.items() for tool in tools]
KIND = {name: name.split("__")[1] for name in ALLOWED_TOOLS}  # mcp__states__apply_tactic -> states
# A "proof" that leans on any of these would not be accepted into the library, so it does not count as closing.
FORBIDDEN_IN_PROOF = ("sorry", "native_decide", "axiom ", "unsafe ", "implemented_by", "admit")
SUCCESS = re.compile(r"\[\[LEAK_NORMALIZED_SCRIPT_B64:([A-Za-z0-9+/=]+)\]\]")


def sha256(data: bytes | str) -> str:
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def norm(text: str) -> str:
    return " ".join(text.split())


def theorem_text(record: dict) -> str:
    """The statement as the agent sees it: import lines dropped (the services add the library's root import)."""
    lines = [ln for ln in record["statement"].splitlines() if not ln.strip().startswith("import ")]
    return "\n".join(lines).strip()


def prompt_for(record: dict) -> str:
    context = (record.get("context") or "").strip()
    block = (context + "\n\n" if context else "") + theorem_text(record)
    return f"""You are testing whether a theorem can be re-proved quickly from the existing Tengoku library (Lean 4; Mathlib and much more, under the `Tengoku` root).

Prove this theorem exactly as stated — same name, same statement:

```lean
{block}
```

Rules:
- You have about {SOFT_S // 60} minutes. Work fast: search, try, verify, repeat.
- Your only tools are the library's services: search it (loogle_search, moogle_search), step through a proof (init_proof, apply_tactic, branch_tactics, snapshot_state, get_current_proof_state, cleanup_memory) and check a complete script (verify_full_script). Do not write import lines: the library's root import is added for you.
- The ONLY thing that counts is a verify_full_script call that succeeds on a script containing the theorem exactly as stated. `sorry`, `admit`, `native_decide`, new axioms and `unsafe` do not count.
- Before every tool call say, in a sentence or two, what you are about to try and why. After a failure say what it told you. This commentary is part of the record.
- If the proof verifies, stop at once. If you run out of ideas, say so plainly, then keep trying variations until you are told to stop.
"""


def continue_prompt(remaining: int) -> str:
    return f"Not proved yet, and about {remaining} seconds remain. Keep going: say what you will try differently, then try it."


# ---- transcript ---------------------------------------------------------------------------------------------------
def read_transcript(path: Path) -> list[dict]:
    raw = gzip.decompress(path.read_bytes()) if path.suffix == ".gz" else path.read_bytes()
    return [json.loads(line) for line in raw.decode().splitlines() if line.strip()]


def write_transcript(path: Path, lines: list[dict]) -> None:
    body = "".join(json.dumps(x, ensure_ascii=False, sort_keys=True) + "\n" for x in lines).encode()
    # mtime=0: the same run always gives the same bytes, so its digest means something
    path.write_bytes(gzip.compress(body, mtime=0))


def _text_of(content) -> str:
    text = content if isinstance(content, str) else "\n".join(c.get("text", "") for c in content or [] if isinstance(c, dict))
    try:  # the services answer {"result": "..."}; show the answer, not its wrapping
        inner = json.loads(text)
        if isinstance(inner, dict) and isinstance(inner.get("result"), str):
            return inner["result"]
    except ValueError:
        pass
    return text


def steps(lines: list[dict]) -> list[dict]:
    """One step per tool call: when, what the agent said first, the call, what came back."""
    out, said, open_calls = [], [], {}
    for line in lines:
        ev = line.get("event") or {}
        if ev.get("type") == "assistant":
            for c in ev["message"].get("content", []):
                if c.get("type") == "text" and c.get("text", "").strip():
                    said.append(c["text"].strip())
                elif c.get("type") == "tool_use":
                    step = {
                        "t": line["t"],
                        "said": "\n\n".join(said),
                        "tool": c["name"],
                        "input": c.get("input") or {},
                        "result": None,
                        "t_result": None,
                    }
                    said = []
                    open_calls[c["id"]] = step
                    out.append(step)
        elif ev.get("type") == "user":
            for c in ev["message"].get("content", []) if isinstance(ev["message"].get("content"), list) else []:
                if c.get("type") == "tool_result" and c.get("tool_use_id") in open_calls:
                    step = open_calls.pop(c["tool_use_id"])
                    step["result"], step["t_result"] = _text_of(c.get("content")), line["t"]
    if said:
        out.append(
            {"t": lines[-1]["t"] if lines else 0, "said": "\n\n".join(said), "tool": None, "input": {}, "result": None, "t_result": None}
        )
    return out


def closing_script(step: dict, record: dict) -> str | None:
    """The verified script if this step closed the theorem by the library's standards, else None."""
    if step.get("tool") != "mcp__verify__verify_full_script" or not step.get("result"):
        return None
    m = SUCCESS.search(step["result"])
    if not m:
        return None
    try:
        script = base64.b64decode(m.group(1)).decode("utf-8", "replace")
    except Exception:
        return None
    if norm(theorem_text(record)) not in norm(script):
        return None  # it proved something, but not this statement
    if any(bad in script for bad in FORBIDDEN_IN_PROOF):
        return None
    return script


def measure(lines: list[dict], record: dict) -> dict:
    """Everything the claim says about a run, recomputed from the transcript alone."""
    st = steps(lines)
    calls = {"search": 0, "states": 0, "verify": 0}
    foreign = []
    closed_at = None
    for s in st:
        if not s["tool"]:
            continue
        kind = KIND.get(s["tool"])
        if kind is None:
            foreign.append(s["tool"])
            continue
        calls[kind] += 1
        if closed_at is None and closing_script(s, record):
            closed_at = s["t_result"]
    times = [x["t"] for x in lines]
    gaps = [b - a for a, b in zip(times, times[1:])]
    end = next((x for x in reversed(lines) if x.get("kind") == "runner" and "end" in x), None)
    models = sorted(
        {(x.get("event") or {}).get("message", {}).get("model") for x in lines if (x.get("event") or {}).get("type") == "assistant"}
        - {None}
    )
    return {
        "outcome": "closed" if closed_at is not None else "resisted",
        "seconds": round(closed_at if closed_at is not None else (end or {}).get("seconds", times[-1] if times else 0), 1),
        "calls": calls,
        "foreign_tools": foreign,
        "longest_silence": round(max(gaps), 1) if gaps else 0.0,
        "monotonic": all(g >= 0 for g in gaps),
        "words_of_commentary": sum(len(s["said"].split()) for s in st),
        "models": models,
        "ended": (end or {}).get("end"),
    }


# ---- the readable working log ------------------------------------------------------------------------------------
def _clip(text: str, limit: int) -> str:
    text = text.strip()
    return text if len(text) <= limit else text[:limit].rstrip() + f"\n… ({len(text) - limit} more characters in the transcript)"


def _call_line(step: dict) -> str:
    tool, i = step["tool"].split("__")[-1], step["input"]
    if tool in ("loogle_search", "moogle_search"):
        return f"**{tool}** `{i.get('query', '')}`"
    if tool == "apply_tactic":
        return f"**apply_tactic** on `{str(i.get('state_id', ''))[:8]}`:\n\n```lean\n{i.get('tactic', '')}\n```"
    if tool == "branch_tactics":
        return (
            f"**branch_tactics** on `{str(i.get('state_id', ''))[:8]}`:\n\n```lean\n" + "\n".join(map(str, i.get("tactics", []))) + "\n```"
        )
    if tool == "init_proof":
        return f"**init_proof**\n\n```lean\n{i.get('proposition', '')}\n```"
    if tool == "verify_full_script":
        return f"**verify_full_script**\n\n```lean\n{_clip(i.get('script', ''), 4000)}\n```"
    return f"**{tool}** `{json.dumps(i, ensure_ascii=False)[:200]}`"


def render_working(lines: list[dict], record: dict) -> str:
    head = lines[0]
    m = measure(lines, record)
    out = [
        f"# Blind re-proof attempt: `{record['name']}`",
        "",
        "```lean",
        theorem_text(record),
        "```",
        "",
        f"- **Outcome: {m['outcome'].upper()}** after {m['seconds']} s (budget {head['budget']['soft_s']} s, hard stop {head['budget']['hard_s']} s; ended: {m['ended']})",
        f"- Calls: {m['calls']['search']} searches, {m['calls']['states']} proof-state steps, {m['calls']['verify']} verifications; {m['words_of_commentary']} words of commentary; longest silence {m['longest_silence']} s",
        f"- Model: {', '.join(m['models']) or 'unknown'}; library as the services held it: "
        + ", ".join(f"{k} `{str(v)[:12]}`" for k, v in sorted((head.get("pinned") or {}).items())),
        "",
        "Rendered from the raw transcript beside this file; the gate renders it again and compares.",
        "",
    ]
    n = 0
    for s in steps(lines):
        if s["said"]:
            out += ["> " + ln for ln in _clip(s["said"], 1500).splitlines()] + [""]
        if not s["tool"]:
            continue
        n += 1
        took = f", answered after {round(s['t_result'] - s['t'], 1)} s" if s["t_result"] is not None else ", no answer recorded"
        out += [f"### {n}. at {round(s['t'], 1)} s{took}", "", _call_line(s), ""]
        if s["result"] is not None:
            verdict = " — **this closed it**" if closing_script(s, record) else ""
            out += [
                f"Result{verdict}:",
                "",
                "```text",
                _clip(SUCCESS.sub("[[verified script attached by the service]]", s["result"]), 1200),
                "```",
                "",
            ]
    return "\n".join(out).rstrip() + "\n"


# ---- the claim --------------------------------------------------------------------------------------------------
def digest(claim: dict) -> str:
    body = {k: v for k, v in claim.items() if k != "digest"}
    return sha256(json.dumps(body, ensure_ascii=False, sort_keys=True, separators=(",", ":")))


def slug(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name)[:80]
