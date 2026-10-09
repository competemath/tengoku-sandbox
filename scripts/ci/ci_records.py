#!/usr/bin/env python3
"""ci_records.py collect|append|init-branch — platform-sourced records of this repository's workflow runs (docs/ci-records.md).

  ci_records.py collect --repo R --records DIR --out DIR      the read half: fetch the completed runs since the watermark with `gh api`, build their records, write DIR/batch.json
  ci_records.py append  --batch DIR --records DIR --repo R    the write half: validate DIR/batch.json and append it to the `ci-records` branch through the contents API
  ci_records.py init-branch --repo R                          create the orphan `ci-records` branch (once; through the git data API)

The records come from the platform, never from an agent: timestamps, actors and conclusions are the API's, a run is recorded with all its jobs
and the hash of the raw jobs response, a failed job carries a short scrubbed excerpt of its log and the class an anchored rule gave it (the rule's id
is stored beside the class). A cursor (the watermark) moves past a window of runs only when the runs recorded, those still in progress and those
deliberately held back add up to the API's own count for that window (`warden.ciclean`).

The branch holds, and only ever grows:
  chain/ci-YYYY-MM-DD.ndjson   one hash-chained `audit.record` per run (and per watermark move), written with `warden.audit` (the chain runs across the files)
  runs/YYYY-MM-DD/<batch>.ndjson   the full run records, one file per collection, never edited; each chain record carries the sha256 of its record

The read half holds `actions: read`; the write half holds `contents: write` in a job of its own, takes only the validated batch, writes the
immutable files first and the chain file last, and uses the blob sha of the chain file as a compare-and-swap, so a racing writer makes it stop
and the next run start again. Standard library only, besides the vendored warden modules.

Credit: Tau Ceti Project, the TauCetiCI collector (collect.yml, 2026-09-27; its watermark incident b64d04e, its backlog incident d983506, its stuck run
3f82c1d) and the finding that its `timeout` rule matched the bare word `Killed`; see tengoku-warden docs/TAU-CETI.md. The code is independent."""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.parse
from dataclasses import dataclass, field
from pathlib import Path

from _git import plain
from warden import audit, caps, ciclean, secretscan

CI = Path(__file__).resolve().parent
BRANCH = os.environ.get("CI_RECORDS_BRANCH", "ci-records")  # the override is for rehearsals on a scratch branch
PREFIX = "ci"
CHAIN_DIR = "chain"
RUNS_DIR = "runs"
BATCH_SCHEMA = "tengoku-ci-records.batch/1"
ACTORS_FILE = CI / "ci-actors.json"
REPO = re.compile(r"^[A-Za-z0-9_.-]{1,100}/[A-Za-z0-9_.-]{1,100}$")
SHA40 = re.compile(r"^[0-9a-f]{40}$")
TS = re.compile(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$")
CTRL = re.compile(r"[\x00-\x1f\x7f]")
MAX_RECORDS = 300  # per collection
MAX_RECORD_BYTES = 200_000
MAX_CHAIN_FILE = 900_000  # the contents API reads files up to 1 MB
MAX_BATCH_FILE = 700_000
MAX_WINDOW_RUNS = 900  # the platform lists at most 1000 runs of a filtered query: a window above that can never reconcile
FAILED_JOB = ("failure", "timed_out")
RECORD_KEYS = {
    "schema", "repo", "run_id", "attempt", "workflow", "workflow_path", "event", "status", "conclusion", "head_sha", "head_branch", "actor",
    "triggering_actor", "created_at", "run_started_at", "updated_at", "queue_s", "duration_s", "jobs_complete", "jobs", "api_response_sha256",
    "failure_class", "failure_rule", "failure_version",
}  # fmt: skip


class ApiError(Exception):
    """A call to the platform failed (the message never carries a token)."""


class Conflict(Exception):
    """The branch changed between our read and our write: nothing was lost, the next run starts again."""


def utc(ts: str) -> dt.datetime:
    parsed = ciclean.parse_ts(ts)
    if parsed is None:
        raise ValueError(f"not a timestamp: {ts!r}")
    return parsed


# ------------------------------------------------------------------------------------------------------------------ the platform


class GhApi:
    """`gh api` for reads; the token is gh's own (GH_TOKEN) and never appears in a message."""

    def __init__(self) -> None:
        self.calls = 0

    def get(self, path: str) -> bytes:
        self.calls += 1
        done = subprocess.run(["gh", "api", path], capture_output=True, check=False, timeout=180)
        if done.returncode != 0:
            raise ApiError(f"GET {path.split('?')[0]}: {done.stderr.decode('utf-8', 'replace').strip()[:200]}")
        return done.stdout


def json_get(api, path: str) -> tuple:
    raw = api.get(path)
    try:
        return json.loads(raw), raw
    except ValueError as exc:
        raise ApiError(f"GET {path.split('?')[0]}: not JSON ({exc})") from exc


def runs_path(repo: str, start: str, end: str, per_page: int, page: int) -> str:
    """The runs created in [start, end): the API's range is inclusive at both ends, whole seconds, so the end is one second before."""
    last = ciclean.fmt_ts(utc(end) - dt.timedelta(seconds=1))
    return f"repos/{repo}/actions/runs?created={urllib.parse.quote(start + '..' + last, safe='')}&per_page={per_page}&page={page}"


def window_count(api, repo: str, start: str, end: str) -> int:
    body, _ = json_get(api, runs_path(repo, start, end, 1, 1))
    total = body.get("total_count") if isinstance(body, dict) else None
    if isinstance(total, bool) or not isinstance(total, int) or total < 0:
        raise ApiError("the runs list has no total_count")
    return total


def narrow(api, repo: str, start: str, end: str) -> tuple:
    """(total_count, end) for the longest window from `start`, no longer than `end`, that the platform can list in full."""
    total = window_count(api, repo, start, end)
    for _ in range(12):
        if total <= MAX_WINDOW_RUNS:
            return total, end
        end = ciclean.fmt_ts(utc(start) + (utc(end) - utc(start)) / 2)
        total = window_count(api, repo, start, end)
    raise ApiError(f"{total} runs were created in one stretch of seconds: the window cannot be narrowed to what the platform lists")


def list_runs(api, repo: str, start: str, end: str, total: int) -> list:
    runs: list = []
    for page in range(1, min(10, -(-total // 100)) + 1):
        body, _ = json_get(api, runs_path(repo, start, end, 100, page))
        batch = body.get("workflow_runs") if isinstance(body, dict) else None
        if not isinstance(batch, list):
            raise ApiError("the runs list has no workflow_runs")
        runs += [r for r in batch if isinstance(r, dict)]
    return runs


def fetch_jobs(api, repo: str, run: dict) -> tuple:
    """(jobs, hash of the raw responses, the API's total_count) of one run attempt."""
    jobs: list = []
    digest = hashlib.sha256()
    total = None
    for page in range(1, 11):
        body, raw = json_get(
            api, f"repos/{repo}/actions/runs/{run['id']}/attempts/{run.get('run_attempt', 1)}/jobs?per_page=100&page={page}"
        )
        digest.update(raw)
        got = body.get("jobs") if isinstance(body, dict) else None
        if not isinstance(got, list):
            raise ApiError("the jobs list has no jobs")
        jobs += got
        total = body.get("total_count")
        if len(got) < 100 or (isinstance(total, int) and len(jobs) >= total):
            break
    return jobs, "sha256:" + digest.hexdigest(), total if isinstance(total, int) else None


# --------------------------------------------------------------------------------------------------------------------- records


def compact(rec: dict) -> dict:
    """The steps of a job that succeeded or was skipped add size and no information: keep their count. Failed jobs keep every step."""
    for job in rec["jobs"]:
        if job.get("conclusion") in ("success", "skipped") and job.get("steps"):
            job["steps_dropped"] = len(job["steps"])
            job["steps"] = []
    return rec


def failure_of(api, repo: str, job: dict, budget: list) -> dict | None:
    """The class an anchored rule gives a failed job, from a scrubbed excerpt of its log. `budget` is [log fetches left]."""
    if job.get("conclusion") not in FAILED_JOB:
        return None
    step = job.get("failed_step") or {}
    window = (step.get("started_at"), step.get("completed_at")) if step.get("started_at") and step.get("completed_at") else None
    if budget[0] <= 0:
        return {"class": "unknown", "rule": "log_budget", "version": ciclean.VERSION, "excerpt": []}
    budget[0] -= 1
    try:
        text = api.get(f"repos/{repo}/actions/jobs/{job['id']}/logs").decode("utf-8", "replace")
    except ApiError:
        return {"class": "unknown", "rule": "log_unavailable", "version": ciclean.VERSION, "excerpt": []}
    excerpt = [secretscan.redact(line) for line in ciclean.failure_excerpt(text, window)]
    klass, rule = ciclean.classify_failure(excerpt)
    return {"class": klass, "rule": rule, "version": ciclean.VERSION, "excerpt": excerpt}


def add_failures(api, repo: str, rec: dict, budget: list) -> dict:
    first = None
    for job in rec["jobs"]:
        failure = failure_of(api, repo, job, budget)
        if failure:
            job["failure"] = failure
            first = first or failure
    if first:
        rec["failure_class"], rec["failure_rule"], rec["failure_version"] = first["class"], first["rule"], first["version"]
    return rec


def digest_of(rec: dict) -> str:
    return "sha256:" + hashlib.sha256(ciclean.canonical_json(rec).encode("utf-8")).hexdigest()


def agent_of(actor: str | None, mapping: dict) -> str | None:
    return mapping.get(actor or "")


def audit_record(rec: dict, mapping: dict, collected_at: str) -> dict:
    """The compact, schema-checked chain record of one run; `evidence` is the hash of the full record stored in runs/."""
    ts = rec.get("updated_at") if isinstance(rec.get("updated_at"), str) and TS.match(rec["updated_at"]) else collected_at
    out = {
        "schema": audit.SCHEMA_ID,
        "ts": ts,
        "actor": rec.get("actor") or "unknown",
        "action": "ci.run",
        "target": f"{rec['repo']} {rec['run_id']}:{rec['attempt']}",
        "outcome": "info",
        "evidence": digest_of(rec),
        "detail": {
            "conclusion": rec.get("conclusion") or "none",
            "event": rec.get("event") or "none",
            "duration_s": rec.get("duration_s"),
            "queue_s": rec.get("queue_s"),
            "jobs": len(rec["jobs"]),
            "branch": (rec.get("head_branch") or "")[:150] or None,
            "class": rec.get("failure_class"),
        },
    }
    if agent_of(rec.get("actor"), mapping):
        out["agent"] = agent_of(rec.get("actor"), mapping)
    if rec.get("workflow"):
        out["case"] = rec["workflow"]
    if rec.get("failure_rule"):
        out["rule"] = rec["failure_rule"]
    return out


def watermark_record(wm: dict, repo: str, collected_at: str) -> dict:
    return {
        "schema": audit.SCHEMA_ID,
        "ts": collected_at,
        "actor": "ci-records",
        "action": "ci.watermark",
        "target": repo,
        "outcome": "info",
        "detail": {"watermark": wm["to"], "counted": wm["counted"], "api_total_count": wm["api_total_count"], "held": len(wm["held_by"])},
    }


# --------------------------------------------------------------------------------------------------------------- the branch state


@dataclass
class State:
    index: set = field(default_factory=set)  # (run_id, attempt)
    watermark: str | None = None
    entries: int = 0
    head: str = caps.GENESIS
    files: dict = field(default_factory=dict)  # chain file name -> bytes


CHAIN_FILE = re.compile(rf"^{PREFIX}-(\d{{4}}-\d{{2}}-\d{{2}})\.ndjson$")


def parse_state(files: dict, repo: str) -> State:
    """The state of the chain from its files (name -> bytes): verified, then read. Raises ValueError when it does not verify."""
    work = Path(tempfile.mkdtemp())
    for name, data in files.items():
        (work / name).write_bytes(data)
    result = audit.verify_dir(str(work), prefix=PREFIX)
    if not result.ok:
        raise ValueError("the chain does not verify: " + "; ".join(result.errors[:3]))
    state = State(entries=result.entries, head=result.head, files=dict(files))
    prev, seq = caps.GENESIS, 0
    for name in sorted(n for n in files if CHAIN_FILE.match(n)):
        entries, prev = caps.parse_chain(files[name], prev, seq)
        seq += len(entries)
        for e in entries:
            body = e["body"]
            if body.get("action") == "ci.run" and isinstance(body.get("target"), str):
                m = re.fullmatch(r"(\S+) (\d+):(\d+)", body["target"])
                if m and m.group(1) == repo:
                    state.index.add((int(m.group(2)), int(m.group(3))))
            elif body.get("action") == "ci.watermark" and body.get("target") == repo:
                wm = (body.get("detail") or {}).get("watermark")
                if isinstance(wm, str) and TS.match(wm):
                    state.watermark = wm
    return state


def read_chain_files(records: Path) -> dict:
    chain = records / CHAIN_DIR
    return {p.name: p.read_bytes() for p in sorted(chain.glob("*.ndjson")) if CHAIN_FILE.match(p.name)} if chain.is_dir() else {}


def load_history(records: Path, now: dt.datetime, days: int, limit: int = 20000) -> list:
    """The full run records of the last `days` days kept in runs/."""
    out: list = []
    root = records / RUNS_DIR
    if not root.is_dir():
        return out
    cutoff = (now - dt.timedelta(days=days)).strftime("%Y-%m-%d")
    for day in sorted(d for d in root.iterdir() if d.is_dir() and re.fullmatch(r"\d{4}-\d{2}-\d{2}", d.name) and d.name >= cutoff):
        for f in sorted(day.glob("*.ndjson")):
            for line in f.read_text(encoding="utf-8").splitlines():
                try:
                    rec = json.loads(line)
                except ValueError:
                    continue
                if isinstance(rec, dict):
                    out.append(rec)
                if len(out) >= limit:
                    return out
    return out


def load_actors(path: Path = ACTORS_FILE) -> dict:
    doc = json.loads(path.read_text(encoding="utf-8"))
    actors = doc.get("actors") if isinstance(doc, dict) else None
    if not isinstance(actors, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in actors.items()):
        raise ValueError(f'{path.name}: expected {{"actors": {{login: agent}}}}')
    return actors


# -------------------------------------------------------------------------------------------------------------------------- collect


RATE_FLOOR = 200  # the token's hourly allowance is shared with every other workflow of the repository: below this, a collection waits for the next hour


def calls_left(api) -> int | None:
    """The calls the token may still make this hour (`GET /rate_limit` is free), or None when the platform does not say."""
    try:
        body, _ = json_get(api, "rate_limit")
        left = body["resources"]["core"]["remaining"]
    except (ApiError, KeyError, TypeError):
        return None
    return left if isinstance(left, int) and not isinstance(left, bool) else None


def collect(
    api, repo: str, state: State, now: dt.datetime, *, bootstrap_days: int = 2, job_budget: int = 60, log_budget: int = 25, lag_s: int = 900
) -> dict:
    """Everything the read half decides, as one document. `api.get(path) -> bytes` is the only IO."""
    now_s = ciclean.fmt_ts(now)
    prev = state.watermark or ciclean.fmt_ts(now - dt.timedelta(days=bootstrap_days))
    start, end = ciclean.window_for(prev, now_s, lag_s)
    notes: list = []
    if utc(end) <= utc(start):
        return empty_batch(repo, now_s, start, end, prev, "the window is empty: the previous collection was less than the lag ago")
    left = calls_left(api)
    if left is not None and left < RATE_FLOOR:
        return empty_batch(
            repo,
            now_s,
            start,
            end,
            prev,
            f"only {left} API calls are left this hour (the floor is {RATE_FLOOR}): nothing was collected, the next hour goes on",
        )
    if left is not None:  # a budget the allowance can pay for: about three calls a run (its jobs, and a log for a failed one) and the lists
        job_budget = min(job_budget, max(0, (left - RATE_FLOOR) // 3))
        log_budget = min(log_budget, max(0, (left - RATE_FLOOR) // 6))
    total, end = narrow(api, repo, start, end)
    if end != ciclean.window_for(prev, now_s, lag_s)[1]:
        notes.append(f"the window was cut to {end}: more than {MAX_WINDOW_RUNS} runs in it")
    runs = list_runs(api, repo, start, end, total)
    plan = ciclean.plan_collection(state.index, runs, job_budget)
    by_key = {(r["id"], r.get("run_attempt", 1)): r for r in runs if isinstance(r.get("id"), int)}
    records, logs_left = [], [log_budget]
    unrecorded = [r for r in runs if r.get("id") in set(plan.deferred)]  # over the call budget: held, recorded by a later collection
    for rid, att in plan.fetch:
        run = by_key[(rid, att)]
        try:
            jobs, digest, jobs_total = fetch_jobs(api, repo, run)
            rec = ciclean.run_record(run, jobs, digest, jobs_total_count=jobs_total)
        except (ApiError, ValueError) as exc:
            unrecorded.append(run)
            notes.append(f"run {rid}: not recorded ({str(exc)[:100]}); the watermark holds")
            continue
        records.append(compact(add_failures(api, repo, rec, logs_left)))
    recorded_runs = [by_key[k] for k in plan.already_recorded if k in by_key] + [by_key[(r["run_id"], r["attempt"])] for r in records]
    pending = [r for r in runs if r.get("id") in set(plan.pending)]
    result = ciclean.advance_watermark(
        prev, recorded_runs, pending, total, ciclean.fmt_ts(utc(end) + dt.timedelta(seconds=lag_s)), unrecorded_runs=unrecorded, lag_s=lag_s
    )
    wm = {
        "advanced": result.advanced,
        "from": prev,
        "to": result.watermark if result.advanced else prev,
        "reasons": result.reasons,
        "counted": result.counted,
        "api_total_count": total,
        "held_by": result.held_by,
    }
    return {
        "schema": BATCH_SCHEMA,
        "repo": repo,
        "collected_at": now_s,
        "window": [start, end],
        "watermark": wm,
        "plan": {
            "listed": len(runs),
            "fetched": len(records),
            "already_recorded": len(plan.already_recorded),
            "pending": len(plan.pending),
            "deferred": len(plan.deferred),
        },
        "records": records,
        "notes": notes,
        "api_calls": getattr(api, "calls", 0),
    }


def empty_batch(repo: str, now_s: str, start: str, end: str, prev: str, note: str) -> dict:
    wm = {"advanced": False, "from": prev, "to": prev, "reasons": ["empty_window"], "counted": 0, "api_total_count": 0, "held_by": []}
    return {
        "schema": BATCH_SCHEMA,
        "repo": repo,
        "collected_at": now_s,
        "window": [start, end],
        "watermark": wm,
        "plan": {"listed": 0, "fetched": 0, "already_recorded": 0, "pending": 0, "deferred": 0},
        "records": [],
        "notes": [note],
        "api_calls": 0,
    }


# ------------------------------------------------------------------------------------------------------------------------ validate


def is_plain(value: object, depth: int = 0) -> bool:
    """JSON made of short plain strings, numbers, booleans, nulls, lists and objects: no control character anywhere, bounded depth."""
    if depth > 8:
        return False
    if isinstance(value, str):
        return len(value) <= 2000 and not CTRL.search(value)
    if isinstance(value, (bool, int)) or value is None:
        return True
    if isinstance(value, float):
        return value == value and abs(value) != float("inf")
    if isinstance(value, list):
        return len(value) <= 500 and all(is_plain(v, depth + 1) for v in value)
    if isinstance(value, dict):
        return len(value) <= 64 and all(isinstance(k, str) and len(k) <= 60 and is_plain(v, depth + 1) for k, v in value.items())
    return False


def validate_record(rec: object, repo: str) -> dict:
    if not isinstance(rec, dict) or rec.get("schema") != ciclean.SCHEMA or not set(rec) <= RECORD_KEYS:
        raise ValueError("not a run record")
    if rec.get("repo") != repo:
        raise ValueError("a record of another repository")
    for k in ("run_id", "attempt"):
        if isinstance(rec.get(k), bool) or not isinstance(rec.get(k), int) or rec[k] <= 0:
            raise ValueError(f"bad {k}")
    if not isinstance(rec.get("head_sha"), str) or not SHA40.match(rec["head_sha"]):
        raise ValueError("bad head_sha")
    if not isinstance(rec.get("api_response_sha256"), str) or not re.fullmatch(r"sha256:[0-9a-f]{64}", rec["api_response_sha256"]):
        raise ValueError("bad api_response_sha256")
    if not isinstance(rec.get("jobs"), list) or len(rec["jobs"]) > 256 or not is_plain(rec):
        raise ValueError("bad jobs")
    if len(ciclean.canonical_json(rec)) > MAX_RECORD_BYTES:
        raise ValueError("record too large")
    return rec


def validate_batch(doc: object) -> dict:
    """The write half takes only a batch of exactly this shape. Raises ValueError otherwise."""
    if not isinstance(doc, dict) or doc.get("schema") != BATCH_SCHEMA:
        raise ValueError("not a ci-records batch")
    if set(doc) != {"schema", "repo", "collected_at", "window", "watermark", "plan", "records", "notes", "api_calls"}:
        raise ValueError("unexpected keys")
    if not isinstance(doc["repo"], str) or not REPO.match(doc["repo"]):
        raise ValueError("bad repo")
    if not isinstance(doc["collected_at"], str) or not TS.match(doc["collected_at"]):
        raise ValueError("bad collected_at")
    wm = doc["watermark"]
    if not isinstance(wm, dict) or set(wm) != {"advanced", "from", "to", "reasons", "counted", "api_total_count", "held_by"}:
        raise ValueError("bad watermark")
    if not isinstance(wm["advanced"], bool) or not all(isinstance(wm[k], str) and TS.match(wm[k]) for k in ("from", "to")):
        raise ValueError("bad watermark times")
    if not (is_plain(wm) and all(isinstance(wm[k], int) and not isinstance(wm[k], bool) for k in ("counted", "api_total_count"))):
        raise ValueError("bad watermark numbers")
    if not isinstance(doc["records"], list) or len(doc["records"]) > MAX_RECORDS:
        raise ValueError("too many records")
    seen = set()
    for rec in doc["records"]:
        validate_record(rec, doc["repo"])
        key = (rec["run_id"], rec["attempt"])
        if key in seen:
            raise ValueError("a run twice")
        seen.add(key)
    if not (is_plain(doc["window"]) and is_plain(doc["plan"]) and is_plain(doc["notes"])) or not isinstance(doc["api_calls"], int):
        raise ValueError("bad window, plan or notes")
    return doc


# --------------------------------------------------------------------------------------------------------------------- the append


def plan_append(doc: dict, state: State, mapping: dict) -> tuple:
    """(new files {path: bytes}, how many runs). Pure: the chain is extended in a scratch directory with `warden.audit.Chain`, and what differs
    from the state is what is returned. The chain file of the collection's day is the commit point; the full records are separate files."""
    day = doc["collected_at"][:10]
    todo = [r for r in doc["records"] if (r["run_id"], r["attempt"]) not in state.index]
    work = Path(tempfile.mkdtemp())
    for name, data in state.files.items():
        (work / name).write_bytes(data)
    chain = audit.Chain(str(work), PREFIX)
    for rec in todo:
        chain.append(audit_record(rec, mapping, doc["collected_at"]), day)
    if doc["watermark"]["advanced"] and doc["watermark"]["to"] != state.watermark:
        chain.append(watermark_record(doc["watermark"], doc["repo"], doc["collected_at"]), day)
    files: dict = {}
    for p in sorted(work.glob("*.ndjson")):
        data = p.read_bytes()
        if state.files.get(p.name) != data:
            if len(data) > MAX_CHAIN_FILE:
                raise ValueError(f"{p.name} would be {len(data)} bytes: more than the contents API reads; rotate the chain")
            files[f"{CHAIN_DIR}/{p.name}"] = data
    # the full records, never edited: one file (or a few, under the size cap) per collection
    stamp = doc["collected_at"][11:19].replace(":", "")
    part, size, lines = 1, 0, []
    for rec in todo:
        line = ciclean.canonical_json(rec) + "\n"
        if lines and size + len(line) > MAX_BATCH_FILE:
            files[f"{RUNS_DIR}/{day}/{stamp}-{os.environ.get('GITHUB_RUN_ID', '0')}-p{part}.ndjson"] = "".join(lines).encode("utf-8")
            part, size, lines = part + 1, 0, []
        lines.append(line)
        size += len(line)
    if lines:
        files[f"{RUNS_DIR}/{day}/{stamp}-{os.environ.get('GITHUB_RUN_ID', '0')}-p{part}.ndjson"] = "".join(lines).encode("utf-8")
    return files, len(todo)


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()  # noqa: S324 — git's own object id, not a security hash


class GhRemote:
    """The branch through the contents API: reads give (bytes, blob sha), writes carry the blob sha they replace (compare-and-swap)."""

    def __init__(self, repo: str, branch: str = BRANCH) -> None:
        self.repo, self.branch = repo, branch

    def _gh(self, *args: str, payload: dict | None = None) -> tuple:
        done = subprocess.run(
            ["gh", "api", *args], input=json.dumps(payload) if payload else None, capture_output=True, text=True, check=False
        )
        return done.returncode, done.stdout if done.returncode == 0 else done.stderr

    def read(self, path: str) -> tuple:
        rc, out = self._gh(f"repos/{self.repo}/contents/{path}?ref={urllib.parse.quote(self.branch, safe='')}")
        if rc != 0:
            if "404" in out or "Not Found" in out:
                return None, None
            raise ApiError(f"cannot read {self.branch}:{path}: {out.strip()[:200]}")
        meta = json.loads(out)
        if not isinstance(meta, dict) or meta.get("encoding") != "base64":
            raise ApiError(f"{path} is not a file the contents API returns whole")
        return base64.b64decode(meta.get("content", "")), meta["sha"]

    def write(self, path: str, data: bytes, sha: str | None, message: str) -> None:
        payload = {"message": message, "content": base64.b64encode(data).decode("ascii"), "branch": self.branch}
        if sha:
            payload["sha"] = sha
        rc, out = self._gh("-X", "PUT", f"repos/{self.repo}/contents/{path}", "--input", "-", payload=payload)
        if rc != 0:
            raise Conflict(f"{path}: {out.strip()[:200]}")


def append(doc: dict, state: State, remote, mapping: dict) -> dict:
    """Write what `plan_append` decided: the immutable files first, the chain file last (its blob sha is the compare-and-swap)."""
    files, n = plan_append(doc, state, mapping)
    if not files:
        return {"appended": 0, "files": []}
    chain_paths = [p for p in files if p.startswith(CHAIN_DIR + "/")]
    message = f"ci-records: {n} run(s), window to {doc['watermark']['to']}"
    for path in [p for p in files if p not in chain_paths]:
        have, _ = remote.read(path)
        if have is not None:
            raise Conflict(f"{path} exists already")
        remote.write(path, files[path], None, message)
    for path in chain_paths:
        name = path.split("/", 1)[1]
        have, sha = remote.read(path)
        if have != state.files.get(name):
            raise Conflict(f"{path} changed since it was read")
        remote.write(path, files[path], sha, message)
    return {"appended": n, "files": sorted(files)}


# --------------------------------------------------------------------------------------------------------------------- the report


def render_summary(doc: dict, history: list, mapping: dict) -> str:
    wm, plan = doc["watermark"], doc["plan"]
    lines = [
        f"### CI records: {len(doc['records'])} run(s) collected",
        "",
        f"- window `{doc['window'][0]}` to `{doc['window'][1]}`: {plan['listed']} listed, {plan['already_recorded']} already recorded, {plan['fetched']} fetched, "
        f"{plan['pending']} still running, {plan['deferred']} deferred by the call budget; {doc['api_calls']} API calls",
        f"- watermark: {'advanced' if wm['advanced'] else 'held'} `{wm['from']}` to `{wm['to']}` ({', '.join(wm['reasons']) or 'reconciled'}; counted {wm['counted']} of the API's {wm['api_total_count']})",
    ]
    lines += [f"- note: {n}" for n in doc["notes"]]
    classes: dict = {}
    for rec in doc["records"]:
        if rec.get("failure_class"):
            classes[rec["failure_class"]] = classes.get(rec["failure_class"], 0) + 1
    if classes:
        lines.append("- failures by class: " + ", ".join(f"{k} {v}" for k, v in sorted(classes.items())))
    rates = ciclean.failure_rates(history + doc["records"], mapping)
    lines += [
        "",
        f"Failure share over the last 30 days ({rates['overall']['n']} finished runs; 95% Wilson interval):",
        "",
        "| group | runs | failures | share | interval |",
        "| --- | --- | --- | --- | --- |",
    ]
    for group in ("by_agent", "by_actor"):
        for key, s in rates[group].items():
            if s["n"]:
                lines.append(
                    f"| {group[3:]} `{key}` | {s['n']} | {s['failures']} | {s['rate']:.1%} | {s['wilson_low']:.1%} to {s['wilson_high']:.1%} |"
                )
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------------------------------------------------- the branch


def init_branch(repo: str, branch: str = BRANCH) -> int:
    """An orphan branch with a README in each folder, created through the git data API (no checkout, no push)."""
    readme = {
        "README.md": "The CI records: platform-sourced, append-only, hash-chained records of this repository's workflow runs, written by the ci-records workflow "
        "(docs/ci-records.md on main). Do not edit by hand.\n",
        f"{CHAIN_DIR}/README.md": "One hash-chained audit.record per run, in chain/ci-YYYY-MM-DD.ndjson. Verified by ledger-guard.\n",
        f"{RUNS_DIR}/README.md": "The full run records, one immutable file per collection. Each chain record carries the sha256 of its record.\n",
    }

    def gh(*args: str, payload: dict | None = None) -> dict:
        done = subprocess.run(
            ["gh", "api", *args], input=json.dumps(payload) if payload else None, capture_output=True, text=True, check=False
        )
        if done.returncode != 0:
            raise ApiError(done.stderr.strip()[:300])
        return json.loads(done.stdout or "{}")

    tree = [
        {
            "path": p,
            "mode": "100644",
            "type": "blob",
            "sha": gh("-X", "POST", f"repos/{repo}/git/blobs", "--input", "-", payload={"content": t, "encoding": "utf-8"})["sha"],
        }
        for p, t in readme.items()
    ]
    tree_sha = gh("-X", "POST", f"repos/{repo}/git/trees", "--input", "-", payload={"tree": tree})["sha"]
    commit = gh(
        "-X",
        "POST",
        f"repos/{repo}/git/commits",
        "--input",
        "-",
        payload={"message": f"{branch}: an empty append-only branch", "tree": tree_sha, "parents": []},
    )["sha"]
    gh("-X", "POST", f"repos/{repo}/git/refs", "--input", "-", payload={"ref": f"refs/heads/{branch}", "sha": commit})
    print(f"created {branch} at {commit}")
    return 0


# ------------------------------------------------------------------------------------------------------------------------ CLI


def run_collect(a: argparse.Namespace) -> int:
    if not REPO.match(a.repo):
        print("ci_records: the repository is not owner/name", file=sys.stderr)
        return 2
    records = Path(a.records)
    state = parse_state(read_chain_files(records), a.repo) if records.is_dir() else State()
    now = utc(a.now) if a.now else dt.datetime.now(dt.timezone.utc).replace(microsecond=0)
    doc = collect(GhApi(), a.repo, state, now, bootstrap_days=a.bootstrap_days, job_budget=a.job_budget, log_budget=a.log_budget)
    validate_batch(doc)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "batch.json").write_text(json.dumps(doc, sort_keys=True) + "\n", encoding="utf-8")
    history = load_history(records, now, 30)
    summary = render_summary(doc, history, load_actors())
    (out / "summary.md").write_text(summary, encoding="utf-8")
    print(plain(summary))
    return 0


def run_append(a: argparse.Namespace) -> int:
    doc = validate_batch(json.loads((Path(a.batch) / "batch.json").read_text(encoding="utf-8")))
    if doc["repo"] != a.repo:
        print("ci_records: the batch is for another repository", file=sys.stderr)
        return 2
    state = parse_state(read_chain_files(Path(a.records)), a.repo)
    try:
        result = append(doc, state, GhRemote(a.repo), load_actors())
    except Conflict as exc:
        print(
            f"ci_records: the branch changed under the writer, or refused the write; nothing is lost and the next run starts again: {exc}",
            file=sys.stderr,
        )
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


def main(argv: list) -> int:
    ap = argparse.ArgumentParser(prog="ci_records")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("collect")
    c.add_argument("--repo", required=True)
    c.add_argument("--records", required=True, help="a checkout of the records branch (may be absent: then nothing is recorded yet)")
    c.add_argument("--out", required=True)
    c.add_argument("--now", help="RFC 3339, for rehearsals")
    c.add_argument("--bootstrap-days", type=int, default=2)
    c.add_argument("--job-budget", type=int, default=60, help="runs whose jobs are fetched per collection")
    c.add_argument("--log-budget", type=int, default=25, help="failed jobs whose logs are fetched per collection")
    c.set_defaults(fn=run_collect)
    p = sub.add_parser("append")
    p.add_argument("--batch", required=True)
    p.add_argument("--records", required=True)
    p.add_argument("--repo", required=True)
    p.set_defaults(fn=run_append)
    i = sub.add_parser("init-branch")
    i.add_argument("--repo", required=True)
    i.set_defaults(fn=lambda a: init_branch(a.repo))
    args = ap.parse_args(argv)
    try:
        return args.fn(args)
    except (ValueError, OSError, ApiError, audit.ChainError, caps.LedgerError, subprocess.SubprocessError) as exc:
        print(plain(f"ci_records: {type(exc).__name__}: {exc}"), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
