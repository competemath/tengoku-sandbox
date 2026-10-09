"""ci_records.py (docs/ci-records.md): the collector's decisions against a fake platform, and the writer against a fake branch with a compare-and-swap.

No network. Every rule has a case that must hold and one that must fail: a count that does not reconcile, a run still in progress, a call budget that runs out,
a log with the word Killed inside a module name, a secret in a log, a tampered chain, a record edited after the fact, a racing writer."""

from __future__ import annotations

import copy
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
import urllib.parse
from pathlib import Path
from unittest import mock

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))

import ci_records as cr  # noqa: E402
from warden import audit, ciclean  # noqa: E402

REPO = "o/r"
NOW = dt.datetime(2026, 10, 9, 12, 0, 0, tzinfo=dt.timezone.utc)
FAKE_KEY = "gh" + "p_" + "A1b2C3d4E5f6G7h8I9j0K1l2M3n4O5p6Q7r8"  # pragma: allowlist secret


def run_of(rid, created, status="completed", conclusion="success", actor="tengoku-bot", name="pr-gate", attempt=1):
    return {
        "id": rid,
        "run_attempt": attempt,
        "name": name,
        "path": f".github/workflows/{name}.yml",
        "event": "pull_request_target",
        "status": status,
        "conclusion": conclusion if status == "completed" else None,
        "head_sha": f"{rid:040x}",
        "head_branch": "intake/lib-1",
        "actor": {"login": actor},
        "triggering_actor": {"login": actor},
        "created_at": created,
        "run_started_at": created,
        "updated_at": created[:-3] + "59Z" if created.endswith("00Z") else created,
        "repository": {"full_name": REPO},
    }


def job_of(jid, conclusion="success", name="classify"):
    step_fail = conclusion in ("failure", "timed_out")
    return {
        "id": jid,
        "name": name,
        "status": "completed",
        "conclusion": conclusion,
        "labels": ["ubuntu-latest"],
        "runner_name": "GitHub Actions 1",
        "created_at": "2026-10-09T10:00:00Z",
        "started_at": "2026-10-09T10:00:05Z",
        "completed_at": "2026-10-09T10:01:05Z",
        "steps": [
            {
                "number": 1,
                "name": "setup",
                "conclusion": "success",
                "started_at": "2026-10-09T10:00:05Z",
                "completed_at": "2026-10-09T10:00:10Z",
            },
            {
                "number": 2,
                "name": "build",
                "conclusion": "failure" if step_fail else "success",
                "started_at": "2026-10-09T10:00:10Z",
                "completed_at": "2026-10-09T10:01:00Z",
            },
        ],
    }


class FakeApi:
    """The slice of the platform the collector reads. `lie` is added to every total_count; `window_total(start, end)` can say there are far more runs."""

    def __init__(self, runs, jobs=None, logs=None, lie=0, window_total=None, fail_jobs_of=()):
        self.runs, self.jobs, self.logs, self.lie, self.window_total, self.fail_jobs_of = (
            runs,
            jobs or {},
            logs or {},
            lie,
            window_total,
            set(fail_jobs_of),
        )
        self.calls = 0
        self.paths = []

    def get(self, path):
        self.calls += 1
        self.paths.append(path)
        url = urllib.parse.urlparse(path)
        q = urllib.parse.parse_qs(url.query)
        if url.path.endswith("/actions/runs"):
            lo, hi = q["created"][0].split("..")
            inside = [r for r in self.runs if lo <= r["created_at"] <= hi]
            total = len(inside) + self.lie
            if self.window_total and self.window_total(lo, hi) is not None:
                total = self.window_total(lo, hi)
            per, page = int(q["per_page"][0]), int(q["page"][0])
            return json.dumps({"total_count": total, "workflow_runs": inside[(page - 1) * per : page * per]}).encode()
        m = re.search(r"/actions/runs/(\d+)/attempts/(\d+)/jobs", url.path)
        if m:
            if int(m.group(1)) in self.fail_jobs_of:
                raise cr.ApiError("HTTP 502")
            jobs = self.jobs.get(int(m.group(1)), [])
            return json.dumps({"total_count": len(jobs), "jobs": jobs}).encode()
        m = re.search(r"/actions/jobs/(\d+)/logs", url.path)
        if m:
            if int(m.group(1)) not in self.logs:
                raise cr.ApiError("HTTP 404")
            return self.logs[int(m.group(1))].encode()
        raise AssertionError(path)


def standard_runs():
    return [
        run_of(101, "2026-10-09T10:00:00Z"),
        run_of(102, "2026-10-09T10:30:00Z", conclusion="failure", actor="dependabot[bot]"),
        run_of(103, "2026-10-09T11:00:00Z", status="in_progress"),
    ]


def standard_jobs():
    return {101: [job_of(1, name="a"), job_of(2, name="b")], 102: [job_of(3, "failure", name="build")], 103: [job_of(4)]}


def collect(api, state=None, **kw):
    return cr.collect(api, REPO, state or cr.State(), NOW, **kw)


class Collect(unittest.TestCase):
    def test_finished_runs_are_recorded_and_an_unfinished_one_holds_the_watermark(self):
        doc = collect(FakeApi(standard_runs(), standard_jobs()))
        self.assertEqual(sorted(r["run_id"] for r in doc["records"]), [101, 102])
        wm = doc["watermark"]
        self.assertTrue(wm["advanced"])
        self.assertEqual(wm["to"], "2026-10-09T11:00:00Z")  # the run still going
        self.assertEqual(wm["held_by"], [103])
        self.assertEqual((wm["counted"], wm["api_total_count"]), (3, 3))
        cr.validate_batch(doc)

    def test_when_everything_is_recorded_the_watermark_moves_to_the_window_end(self):
        runs = [r for r in standard_runs() if r["status"] == "completed"]
        doc = collect(FakeApi(runs, standard_jobs()))
        self.assertEqual(doc["watermark"]["to"], "2026-10-09T11:45:00Z")  # now minus the lag
        self.assertEqual(doc["watermark"]["reasons"], [])

    def test_a_count_that_does_not_reconcile_refuses_to_move(self):
        doc = collect(FakeApi(standard_runs(), standard_jobs(), lie=1))  # the platform counts a run we never saw
        self.assertFalse(doc["watermark"]["advanced"])
        self.assertIn("count_mismatch", doc["watermark"]["reasons"])
        self.assertEqual(doc["watermark"]["to"], doc["watermark"]["from"])
        self.assertEqual(len(doc["records"]), 2)  # the records are still written: they are idempotent, the cursor is what must not skip

    def test_what_is_recorded_already_is_not_fetched_again_but_is_counted(self):
        api = FakeApi([r for r in standard_runs() if r["status"] == "completed"], standard_jobs())
        doc = collect(api, cr.State(index={(101, 1)}))
        self.assertEqual([r["run_id"] for r in doc["records"]], [102])
        self.assertFalse(any("/runs/101/" in p for p in api.paths))
        self.assertTrue(doc["watermark"]["advanced"])

    def test_the_call_budget_defers_the_newest_and_holds_the_watermark_at_the_oldest_of_them(self):
        runs = [run_of(100 + i, f"2026-10-09T0{i}:00:00Z") for i in range(1, 6)]
        jobs = {r["id"]: [job_of(r["id"])] for r in runs}
        doc = collect(FakeApi(runs, jobs), job_budget=2)
        self.assertEqual([r["run_id"] for r in doc["records"]], [101, 102])  # oldest first, so the recorded set stays contiguous
        self.assertEqual(doc["plan"]["deferred"], 3)
        self.assertEqual(doc["watermark"]["to"], "2026-10-09T03:00:00Z")
        self.assertEqual(doc["watermark"]["held_by"], [103, 104, 105])

    def test_a_run_whose_jobs_cannot_be_fetched_holds_the_watermark(self):
        doc = collect(FakeApi(standard_runs()[:2], standard_jobs(), fail_jobs_of=[101]))
        self.assertEqual([r["run_id"] for r in doc["records"]], [102])
        self.assertEqual(doc["watermark"]["to"], "2026-10-09T10:00:00Z")
        self.assertTrue(any("101" in n for n in doc["notes"]))

    def test_a_window_the_platform_cannot_list_in_full_is_cut(self):
        def total(lo, hi):  # a day or more holds "5000" runs; anything shorter is counted honestly
            span = dt.datetime.strptime(hi, "%Y-%m-%dT%H:%M:%SZ") - dt.datetime.strptime(lo, "%Y-%m-%dT%H:%M:%SZ")
            return 5000 if span.days >= 1 else None

        doc = collect(FakeApi([run_of(101, "2026-10-09T10:00:00Z")], {101: [job_of(1)]}, window_total=total))
        self.assertEqual(doc["window"][1], "2026-10-08T11:52:30Z")
        self.assertTrue(any("cut" in n for n in doc["notes"]))
        self.assertEqual(
            doc["watermark"]["to"], "2026-10-08T11:52:30Z"
        )  # the cursor moves to where the cut window ends, and the next hour goes on

    def test_a_window_that_cannot_be_cut_is_an_error(self):
        api = FakeApi([], window_total=lambda lo, hi: 5000)
        with self.assertRaises(cr.ApiError):
            collect(api)

    def test_a_second_collection_right_after_the_first_has_an_empty_window(self):
        doc = collect(FakeApi([]), cr.State(watermark="2026-10-09T11:50:00Z"))
        self.assertEqual(doc["records"], [])
        self.assertFalse(doc["watermark"]["advanced"])

    def test_a_job_that_is_not_a_failure_keeps_no_steps_and_a_failed_one_keeps_all(self):
        doc = collect(FakeApi(standard_runs()[:2], standard_jobs()))
        by = {r["run_id"]: r for r in doc["records"]}
        ok = by[101]["jobs"][0]
        self.assertEqual((ok["steps"], ok["steps_dropped"]), ([], 2))
        self.assertEqual(len(by[102]["jobs"][0]["steps"]), 2)
        self.assertEqual(by[101]["api_response_sha256"][:7], "sha256:")


class Failures(unittest.TestCase):
    def log(self, *lines):
        return "\n".join(f"2026-10-09T10:00:{20 + i:02d}.0000000Z {line}" for i, line in enumerate(lines)) + "\n"

    def one(self, text):
        runs = [run_of(102, "2026-10-09T10:30:00Z", conclusion="failure")]
        doc = collect(FakeApi(runs, {102: [job_of(3, "failure", name="build")]}, {3: text}))
        return doc["records"][0]

    def test_the_class_comes_from_an_anchored_rule_and_its_id_is_stored(self):
        rec = self.one(self.log("##[error]Process completed with exit code 124."))
        self.assertEqual((rec["failure_class"], rec["failure_rule"]), ("timeout", "timeout.coreutils_exit_124"))
        job = rec["jobs"][0]["failure"]
        self.assertEqual((job["class"], job["version"]), ("timeout", ciclean.VERSION))

    def test_the_word_killed_inside_a_module_name_is_not_a_kill(self):
        rec = self.one(
            self.log("error: Tengoku/Algebra/KilledByRank.lean:3:1: unknown identifier 'x'", "##[error]Process completed with exit code 1.")
        )
        self.assertEqual(rec["failure_class"], "build")
        self.assertNotEqual(rec["failure_class"], "killed")

    def test_a_secret_in_a_log_never_reaches_the_record(self):
        rec = self.one(self.log(f"error: the token is {FAKE_KEY} for the request", "##[error]Process completed with exit code 1."))
        text = json.dumps(rec)
        self.assertNotIn(FAKE_KEY, text)
        self.assertIn("[REDACTED:github_token]", text)

    def test_the_log_budget_and_a_missing_log_are_recorded_as_unknown_not_guessed(self):
        runs = [run_of(102, "2026-10-09T10:30:00Z", conclusion="failure")]
        api = FakeApi(runs, {102: [job_of(3, "failure"), job_of(4, "failure", name="b")]}, {})
        rec = collect(api, log_budget=1)["records"][0]
        self.assertEqual([j["failure"]["rule"] for j in rec["jobs"]], ["log_unavailable", "log_budget"])
        self.assertEqual(rec["failure_class"], "unknown")


class Validation(unittest.TestCase):
    def doc(self):
        return collect(FakeApi(standard_runs(), standard_jobs()))

    def test_a_collected_batch_is_valid_and_survives_json(self):
        cr.validate_batch(json.loads(json.dumps(self.doc())))

    def test_the_writer_refuses_anything_that_is_not_exactly_a_batch(self):
        base = self.doc()
        mutations = [
            lambda d: d.update(extra=1),
            lambda d: d.update(repo="not a repo"),
            lambda d: d["records"][0].update(repo="other/repo"),
            lambda d: d["records"][0].update(evil="x"),
            lambda d: d["records"][0].update(head_sha="main"),
            lambda d: d["records"][0].update(workflow="a\nb"),
            lambda d: d["records"].append(copy.deepcopy(d["records"][0])),
            lambda d: d["watermark"].update(to="yesterday"),
            lambda d: d["watermark"].update(counted=True),
            lambda d: d.update(records=[d["records"][0]] * 301),
            lambda d: d["records"][0]["jobs"].append({"x": "y" * 9000}),
        ]
        for mutate in mutations:
            bad = copy.deepcopy(base)
            mutate(bad)
            with self.assertRaises(ValueError, msg=str(mutate)):
                cr.validate_batch(bad)

    def test_the_chain_record_is_a_valid_audit_record_even_for_odd_runs(self):
        doc = self.doc()
        odd = copy.deepcopy(doc["records"][0])
        odd.update(actor=None, head_branch="b" * 400, workflow=None, conclusion=None, event=None, updated_at=None, duration_s=None)
        for rec in (*doc["records"], odd):
            self.assertEqual(audit.validate_record(cr.audit_record(rec, {"tengoku-bot": "factory"}, doc["collected_at"])), [])
        self.assertEqual(cr.audit_record(doc["records"][0], {"tengoku-bot": "factory"}, "2026-10-09T12:00:00Z")["agent"], "factory")
        self.assertNotIn("agent", cr.audit_record(doc["records"][0], {}, "2026-10-09T12:00:00Z"))


class DirRemote:
    """A branch as a dict, with the contents API's compare-and-swap: a write names the blob sha it replaces."""

    def __init__(self, files=None):
        self.files = dict(files or {})
        self.log = []
        self.after_chain_read = None  # a hook: another writer acts right after we have read the chain file

    def read(self, path):
        data = self.files.get(path)
        out = (data, cr.blob_sha(data)) if data is not None else (None, None)
        if path.startswith("chain/") and self.after_chain_read:
            hook, self.after_chain_read = self.after_chain_read, None
            hook(self)
        return out

    def write(self, path, data, sha, message):
        have, current = self.files.get(path), cr.blob_sha(self.files[path]) if path in self.files else None
        if (have is None and sha is not None) or (have is not None and sha != current):
            raise cr.Conflict(f"{path}: sha does not match")
        self.files[path] = data
        self.log.append(path)

    def chain(self):
        return {p.split("/", 1)[1]: d for p, d in self.files.items() if p.startswith("chain/")}


class Append(unittest.TestCase):
    def setUp(self):
        self.mapping = {"tengoku-bot": "factory"}

    def batch(self, now=NOW, runs=None, **kw):
        runs = runs if runs is not None else standard_runs()
        return cr.collect(FakeApi(runs, standard_jobs()), REPO, kw.pop("state", cr.State()), now, **kw)

    def state_of(self, remote):
        return cr.parse_state(remote.chain(), REPO)

    def test_the_first_append_writes_the_immutable_files_first_and_the_chain_last(self):
        remote, doc = DirRemote(), self.batch()
        with mock.patch.dict(os.environ, {"GITHUB_RUN_ID": "77"}):
            result = cr.append(doc, cr.State(), remote, self.mapping)
        self.assertEqual(result["appended"], 2)
        self.assertEqual(remote.log[-1], "chain/ci-2026-10-09.ndjson")
        self.assertEqual(remote.log[0], "runs/2026-10-09/120000-77-p1.ndjson")
        state = self.state_of(remote)
        self.assertEqual(state.index, {(101, 1), (102, 1)})
        self.assertEqual(state.watermark, "2026-10-09T11:00:00Z")
        self.assertEqual(audit.verify_dir(self.write_dir(remote), prefix="ci").entries, 3)  # two runs and one watermark

    def write_dir(self, remote):
        d = Path(tempfile.mkdtemp())
        for name, data in remote.chain().items():
            (d / name).write_bytes(data)
        return str(d)

    def test_every_chain_record_carries_the_hash_of_the_record_it_summarises(self):
        remote = DirRemote()
        cr.append(self.batch(), cr.State(), remote, self.mapping)
        (path,) = [p for p in remote.files if p.startswith("runs/2026")]
        stored = [json.loads(line) for line in remote.files[path].decode().splitlines()]
        entries = [json.loads(line)["body"] for line in remote.chain()["ci-2026-10-09.ndjson"].decode().splitlines()]
        digests = {e["evidence"] for e in entries if e["action"] == "ci.run"}
        self.assertEqual(digests, {"sha256:" + hashlib.sha256(ciclean.canonical_json(r).encode()).hexdigest() for r in stored})

    def test_appending_the_same_batch_twice_adds_nothing(self):
        remote, doc = DirRemote(), self.batch()
        cr.append(doc, cr.State(), remote, self.mapping)
        before = dict(remote.files)
        again = cr.append(doc, self.state_of(remote), remote, self.mapping)
        self.assertEqual(again["appended"], 0)
        self.assertEqual(remote.files, before)

    def test_a_later_day_starts_a_new_file_and_the_chain_runs_across_them(self):
        remote = DirRemote()
        cr.append(self.batch(), cr.State(), remote, self.mapping)
        later = NOW + dt.timedelta(days=1, hours=1)
        doc = self.batch(later, runs=[run_of(201, "2026-10-10T10:00:00Z")], state=self.state_of(remote))
        doc["records"] = [r for r in doc["records"] if r["run_id"] == 201] or doc["records"]
        cr.append(doc, self.state_of(remote), remote, self.mapping)
        self.assertEqual(sorted(remote.chain()), ["ci-2026-10-09.ndjson", "ci-2026-10-10.ndjson"])
        result = audit.verify_dir(self.write_dir(remote), prefix="ci")
        self.assertTrue(result.ok, result.errors)

    def test_an_edited_record_breaks_the_chain_and_the_writer_refuses_to_continue(self):
        remote = DirRemote()
        cr.append(self.batch(), cr.State(), remote, self.mapping)
        files = remote.chain()
        name = "ci-2026-10-09.ndjson"
        files[name] = files[name].replace(b'"conclusion": "success"', b'"conclusion": "failure"', 1)
        self.assertNotEqual(files[name], remote.chain()[name])
        with self.assertRaises(ValueError):
            cr.parse_state(files, REPO)
        files[name] = remote.chain()[name].replace(b"\n", b"\n\n", 1)  # even a blank line inserted is not a silent change of the bytes
        cr.parse_state(files, REPO)  # blank lines are not records; the hash chain is what matters

    def test_a_removed_record_is_found_by_the_chain(self):
        remote = DirRemote()
        cr.append(self.batch(), cr.State(), remote, self.mapping)
        lines = remote.chain()["ci-2026-10-09.ndjson"].splitlines(keepends=True)
        with self.assertRaises(ValueError):
            cr.parse_state({"ci-2026-10-09.ndjson": b"".join(lines[1:])}, REPO)

    def test_a_racing_writer_makes_this_one_stop_and_overwrites_nothing(self):
        remote, doc = DirRemote(), self.batch()

        def race(r):  # another writer gets its chain file in between our read and our write
            r.files["chain/ci-2026-10-09.ndjson"] = b'{"theirs": true}\n'

        remote.after_chain_read = race
        with self.assertRaises(cr.Conflict):
            cr.append(doc, cr.State(), remote, self.mapping)
        self.assertEqual(remote.files["chain/ci-2026-10-09.ndjson"], b'{"theirs": true}\n')

    def test_a_chain_that_changed_since_it_was_read_is_not_written_over(self):
        remote, doc = DirRemote(), self.batch()
        cr.append(doc, cr.State(), remote, self.mapping)
        stale = self.state_of(remote)
        other = self.batch(NOW + dt.timedelta(hours=1), runs=[run_of(900, "2026-10-09T09:00:00Z")], state=stale)
        cr.append(other, stale, remote, self.mapping)  # someone else appends after `stale` was read
        newer = self.batch(NOW + dt.timedelta(hours=2), runs=[run_of(901, "2026-10-09T09:30:00Z")], state=stale)
        before = dict(remote.files)
        with self.assertRaises(cr.Conflict):
            cr.append(newer, stale, remote, self.mapping)
        self.assertEqual(remote.chain(), {k.split("/", 1)[1]: v for k, v in before.items() if k.startswith("chain/")})

    def test_an_immutable_file_that_exists_is_never_replaced(self):
        remote, doc = DirRemote(), self.batch()
        with mock.patch.dict(os.environ, {"GITHUB_RUN_ID": "77"}):
            remote.files["runs/2026-10-09/120000-77-p1.ndjson"] = b"theirs\n"
            with self.assertRaises(cr.Conflict):
                cr.append(doc, cr.State(), remote, self.mapping)
        self.assertEqual(remote.files["runs/2026-10-09/120000-77-p1.ndjson"], b"theirs\n")
        self.assertFalse(remote.chain())

    def test_a_chain_file_too_big_for_the_contents_api_is_refused(self):
        remote, doc = DirRemote(), self.batch()
        with mock.patch.object(cr, "MAX_CHAIN_FILE", 100):
            with self.assertRaises(ValueError):
                cr.append(doc, cr.State(), remote, self.mapping)
        self.assertEqual(remote.files, {})

    def test_the_full_records_are_split_under_the_size_cap(self):
        remote, doc = DirRemote(), self.batch()
        with mock.patch.object(cr, "MAX_BATCH_FILE", 10), mock.patch.dict(os.environ, {"GITHUB_RUN_ID": "5"}):
            cr.append(doc, cr.State(), remote, self.mapping)
        self.assertEqual(
            sorted(p for p in remote.files if p.startswith("runs/")),
            ["runs/2026-10-09/120000-5-p1.ndjson", "runs/2026-10-09/120000-5-p2.ndjson"],
        )


class Report(unittest.TestCase):
    def test_failure_rates_are_per_actor_and_per_agent_and_nothing_is_dropped(self):
        runs = [
            run_of(1, "2026-10-09T09:00:00Z", actor="tengoku-bot"),
            run_of(2, "2026-10-09T09:10:00Z", conclusion="failure", actor="tengoku-bot"),
            run_of(3, "2026-10-09T09:20:00Z", conclusion="failure", actor="somebody"),
        ]
        jobs = {r["id"]: [job_of(r["id"])] for r in runs}
        doc = collect(FakeApi(runs, jobs))
        text = cr.render_summary(doc, [], {"tengoku-bot": "factory"})
        self.assertIn("agent `factory` | 2 | 1 | 50.0%", text)
        self.assertIn("agent `unattributed` | 1 | 1 | 100.0%", text)
        self.assertIn("actor `somebody`", text)
        self.assertIn("watermark: advanced", text)

    def test_history_is_read_from_the_last_days_only(self):
        d = Path(tempfile.mkdtemp())
        for day, rid in (("2026-10-08", 1), ("2026-09-01", 2)):
            (d / "runs" / day).mkdir(parents=True)
            (d / "runs" / day / "x-p1.ndjson").write_text(json.dumps({"run_id": rid}) + "\nnot json\n", encoding="utf-8")
        got = cr.load_history(d, NOW, 30)
        self.assertEqual([r["run_id"] for r in got], [1])

    def test_the_actor_map_is_a_closed_shape(self):
        self.assertIn("tengoku-bot", cr.load_actors())
        bad = Path(tempfile.mkdtemp()) / "a.json"
        bad.write_text('{"actors": {"x": 5}}')
        with self.assertRaises(ValueError):
            cr.load_actors(bad)


class Cli(unittest.TestCase):
    def test_collect_command_writes_the_batch_and_the_summary(self):
        out = Path(tempfile.mkdtemp())
        records = Path(tempfile.mkdtemp())
        api = FakeApi(standard_runs(), standard_jobs())
        with mock.patch.object(cr, "GhApi", lambda: api):
            code = cr.main(["collect", "--repo", REPO, "--records", str(records), "--out", str(out), "--now", "2026-10-09T12:00:00Z"])
        self.assertEqual(code, 0)
        cr.validate_batch(json.loads((out / "batch.json").read_text()))
        self.assertIn("CI records: 2 run(s) collected", (out / "summary.md").read_text())

    def test_append_command_refuses_a_batch_for_another_repository(self):
        d = Path(tempfile.mkdtemp())
        (d / "batch.json").write_text(json.dumps(collect(FakeApi(standard_runs(), standard_jobs()))))
        self.assertEqual(cr.main(["append", "--batch", str(d), "--records", str(d / "none"), "--repo", "x/y"]), 2)

    def test_bad_input_is_exit_2(self):
        self.assertEqual(cr.main(["collect", "--repo", "bad", "--records", "x", "--out", "y"]), 2)

    def test_init_branch_creates_an_orphan_through_the_git_data_api(self):
        log = Path(tempfile.mkdtemp()) / "log"
        shim_dir = Path(tempfile.mkdtemp())
        shim = shim_dir / "gh"
        shim.write_text(
            f'#!/bin/sh\necho "$@" >> "{log}"\ncat >> "{log}"\necho >> "{log}"\necho \'{{"sha": "{"a" * 40}"}}\'\n', encoding="utf-8"
        )
        shim.chmod(0o755)
        with mock.patch.dict(os.environ, {"PATH": f"{shim_dir}{os.pathsep}{os.environ['PATH']}"}):
            self.assertEqual(cr.init_branch(REPO, "ci-records"), 0)
        text = log.read_text()
        self.assertEqual(text.count("git/blobs"), 3)
        self.assertIn('"parents": []', text)
        self.assertIn('"ref": "refs/heads/ci-records"', text)
        self.assertNotIn("force", text)
        self.assertEqual(subprocess.run(["true"]).returncode, 0)


if __name__ == "__main__":
    unittest.main()
