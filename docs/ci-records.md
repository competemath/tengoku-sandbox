# CI records, the ledger guard and ruleset drift

Three read-mostly checks that keep the repository's own history honest. They belong to the agent-security work (`docs/agent-security.md`, from the agent-guard
pull request; the toolkit is [tengoku-warden](https://github.com/competemath/tengoku-warden), vendored in `scripts/ci/warden/`) and exist because the
[Tau Ceti project](https://github.com/TauCetiProject) published what its own records, archives and rulesets looked like in practice: records written by the
agents they describe, archives called append-only that were not, and a ruleset changed with no trace in the repository. The credit for the ideas is theirs;
this is independent code, and each script's docstring names the Tau Ceti feature, pull request or incident it comes from.
The comparison is in tengoku-warden's [`docs/TAU-CETI.md`](https://github.com/competemath/tengoku-warden/blob/8e78f4f1e2b204f7c81da3b155d54e7502086420/docs/TAU-CETI.md).

All of it is **advisory**: nothing here is a required check, nothing reads the records to decide anything yet, and a failure blocks no merge.

## 1. CI records (`ci-records.yml`, `scripts/ci/ci_records.py`)

Every hour the workflow records the workflow runs the platform finished since the last collection, on the append-only `ci-records` branch. The records come from the
platform, never from an agent that could shade them: timestamps, actors and conclusions are the API's, durations are derived from them, and each run keeps all its jobs and the
sha256 of the raw jobs response, so a record can be checked against a re-fetch.

Two jobs, as in the trust-shadow workflow. `collect` (`actions: read`, `contents: read`) reads the platform and the branch and uploads `batch.json`. `append` (`contents: write`,
one writer at a time) takes only that file, validates it again (a closed shape, bounded plain text), and writes it. A pull request that changes the collector runs `collect` alone, a dry
run on the real platform.

**What a collection does** (`warden.ciclean`):

- The window is `[watermark, now - 15 minutes)`. The first collection starts two days back. If the platform counts more than 900 runs in the window (it lists at most 1000), the window is cut in
  half until it fits, and the next hour goes on from there.
- `plan_collection` decides which completed, not yet recorded runs get their jobs fetched, oldest first, within a budget of 60 runs (so the recorded set stays contiguous); the rest are deferred.
- A failed job's log is fetched (at most 25 per collection), cut to the lines of the failing step, scrubbed (ANSI, control characters, `warden.secretscan`), and classified by an **anchored**
  rule: every rule matches one whole line, the rule's id is stored beside the class, and the classifier is versioned. A bare word in a line is never a rule: the module name
  `KilledByRank` is not a kill (Tau Ceti's classifier took it for one, which overstated its timeout share; there is a test for exactly that).
- `advance_watermark` moves the cursor only when the runs recorded, those still running and those deliberately held back **add up to the platform's own count** for the window.
  Otherwise it stays where it was and says `count_mismatch`; the records are still written (they are idempotent: a run already recorded is skipped), only the cursor must not skip.
  A run still going holds the cursor at its creation time; one running for more than 6 hours is reported as stuck and stops holding it.
- Steps of jobs that succeeded are dropped from the stored record (their count is kept): they are most of its size and say nothing a successful job does not. A failed job keeps all its steps.

**What the branch holds**, and only ever grows:

| Path | Content |
| --- | --- |
| `chain/ci-YYYY-MM-DD.ndjson` | one hash-chained `audit.record` per run (and per watermark move), written with `warden.audit.Chain`; the chain runs across the files; each record carries the sha256 of the full record |
| `runs/YYYY-MM-DD/<batch>.ndjson` | the full run records of one collection, one canonical JSON object per line, never edited |

The chain file of the day is the commit point: the immutable files are written first, the chain file last, through the contents API with the file's blob sha as the compare-and-swap.
A racing writer makes the append stop (`Conflict`) with nothing lost; the next hour starts again. A batch file with no chain record is harmless: the chain is the authority.

**The failure-rate report.** The run summary of every collection shows the failure share over the last 30 days with 95% Wilson intervals, per actor and per agent. The agent comes from
`scripts/ci/ci-actors.json`, a human-owned map from logins (`tengoku-bot` is `factory`, `dependabot[bot]` is `dependabot`, …); a login that is not in it is `unattributed`, never dropped.
An agent that works through a person's account cannot be told from the person and is counted under the account.

**Limits, written down on purpose.** A re-run of a run older than the watermark is not collected (the list is by creation time). The branch is as trustworthy as the ruleset on it (section 2):
the chain makes an edit visible, it does not make it impossible. Verifying the chain before every append reads all of it: at the sandbox's rate (about 110 runs a day) that is fine for years;
rotate the chain's prefix when it is not. A day's chain file must stay under 900 KB (the contents API reads files up to 1 MB); the writer refuses beyond that rather than truncate.

## 2. The ledger guard (`ledger-guard.yml`, `scripts/ci/ledger_guard.py`)

Two branches only ever grow: `trust-ledger` (the trust program's verdicts and labels, `ledger.jsonl`) and `ci-records`. The guard reads git objects only, over the last three days of each
branch's own history, and fails if:

- an existing record changed: `runs/**` is immutable (`warden.audit.ledger_guard`: modified, deleted or retyped paths, in the net diff and in every commit of the range, so a change that a later
  commit reverts cannot hide); `ledger.jsonl` and the chain files are append-only (`warden.scope`: the new bytes are the old bytes plus more, no deletion, mode 100644);
- a hash chain no longer verifies (`warden.audit.verify_dir`, which checks every record against a closed schema; `parse_chain` for the trust ledger, whose entries use the same hash);
- the head does not descend from the base (a rewritten history is an error, not a pass);
- the platform's activity feed shows a **force-push or a deletion** of the branch in the last three days. A fixed range cannot see a rewrite that also moved its own base, so the guard asks the platform
  what happened. Pushes by anybody but the Actions identity are named in the report as notices.

**Why it does not run `on: push` to those branches.** A push runs the workflow files of the pushed commit, and these branches hold none, so that trigger would never fire. The guard runs from main's
copy instead: after each workflow that writes to a branch (`workflow_run`), every night, and on demand.

It stands in for a ruleset with `non_fast_forward` and `deletion` on both branches, which the maintainer adds (tengoku-warden `docs/RUNBOOK.md`, item 3). The ruleset prevents; the guard notices.

## 3. Ruleset drift (`ruleset-drift.yml`, `scripts/ci/ruleset_drift.py`)

A ruleset is what actually enforces a required check, the merge queue, no force-push and no deletion. Changing one in the settings leaves no diff in the repository. `.github/rulesets/*.json`
holds the rulesets as they were reviewed (taken from the live API, with ids, timestamps and links dropped and every list sorted, so that order is not drift); every night, on demand, and in any pull
request that touches the checker or a snapshot, the workflow fetches the live ones and fails with a readable diff on any difference: a ruleset loosened, a new one, one deleted or renamed.

It also asserts, for the rules in force on the default branch (`GET /repos/{repo}/rules/branches/{branch}`), what Tau Ceti's Roadmap `auto-merge.yml` asserts since its incident of 2026-08-16 (an
unreviewed merge into an unprotected branch, 11 seconds after the PR was opened): a pull-request rule with required approvals, or the merge queue; at least one required status check;
`non_fast_forward` and `deletion`. It **warns, and does not fail,** about every required check that names no App (`integration_id`): such a check can be set by any identity with write access
(tengoku-warden `docs/RUNBOOK.md`, item 2). Today that is both `pr-gate` and `queue-gate`.

**Bypass actors are hidden from every token a workflow has.** The API returns them to administrators only, so the nightly check cannot compare them; the report says so each time. The snapshot is taken
without them. `snapshot --with-bypass`, run by an administrator, records them, and `check` with an administrator's token compares them. At the time of the snapshot, an administrator saw none for
the one ruleset (`main: PRs only, checks, queue, linear history`; no bypass actor, `current_user_can_bypass: never`). To change a ruleset on purpose: change it in the settings, run
`python3 scripts/ci/ruleset_drift.py snapshot --repo competemath/tengoku-sandbox`, and commit the diff in a pull request.

## 4. The `merge eligibility` check

Part of the trust program, in `docs/trust-shadow.md`: the third job of `trust-shadow.yml`.

## What the maintainer does

1. Add a ruleset with `non_fast_forward` and `deletion` on `trust-ledger` and `ci-records`, and let only the Actions identity (or the App that replaces it) push there. The `ci-records` branch was created, empty, with the git data API (as `trust-ledger` was); the first collection is the first scheduled run.
2. Let the first scheduled `ci-records` run (or `workflow_dispatch`) make the first collection; read its summary.
3. Decide whether `ledger-guard` and `ruleset-drift` become required, and give the required checks `integration_id`s (item 2 of the runbook).
4. Create the judge GitHub App (item 1) when `merge eligibility` should stop being made by the Actions identity.

Rehearsal: the collector and the writer were run against the real API on a scratch branch of this repository (`ci-records-rehearsal`) twice, 113 runs in all, the watermark reconciled
(99 counted of 99), and the guard verified the 115-entry chain. The workflows themselves only run from the default branch, so their first scheduled run is after the merge.
