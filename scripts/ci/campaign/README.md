# Scenario campaign

The tests of the tests. Each script opens real pull requests against a **sandbox**
copy of this repository (never the library: `lib.sh` refuses) and checks that the
gate and the merge queue decide what the design says they should. Read
[`docs/testing.md`](../../../docs/testing.md) first.

```
export TENGOKU_CAMPAIGN_REPO=competemath/tengoku-sandbox   # default
scripts/ci/campaign/gate.sh      # 66 gate scenarios, each with a precondition check and an expected failing job
scripts/ci/campaign/report.sh    # poll until every gate settles, print expectation vs outcome
scripts/ci/campaign/queue.sh     # merge-queue scenarios (ejection classes, twelve clean PRs at once, a broken PR between clean ones, re-queue, bulk promotion, a disguised hand edit)
scripts/ci/campaign/guard4.sh    # publish guard: a workflow file lands on main mid-build; the build must relaunch on the tip
scripts/ci/campaign/run-all.sh   # the overnight order: gate → report → queue → guard
```

Results land in `out/` (`gate-results.tsv`, `queue-results.tsv`, `campaign.log`).
`round2.sh`/`round3.sh` and `phase*.sh` are the re-runs and the chaining used
on 2026-09-15/16; they show how to add a round after a fix.

Adding a scenario is one line in `gate.sh`:

```
sc my-case fail data-rules/records yes gate "what it checks" "shell that edits the tree" 'regex that must appear in the diff'
```

The runner refuses a fixture that produced no change or whose diff lacks the
precondition — a scenario that does not do what it claims must never count.
