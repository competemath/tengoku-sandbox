#!/bin/bash
# T2 of the delta store (scripts/lake_cache.py, queue-gate.yml): real pull requests through the SANDBOX merge queue, each read back from the
# queue-build log, the gate's verdict and the release `lake-deltas-<cache tag>`. Run after the queue rewrite is on the sandbox's main.
#
#   scripts/ci/campaign/deltas.sh            # open the scenario PRs, queue them in the designed order, judge each (hours)
#   scripts/ci/campaign/deltas.sh --report   # print the results table again
#   DELTAS_FROM=3 scripts/ci/campaign/deltas.sh   # resume at scenario 3 (a PR of an earlier scenario that is still open or merged is picked up, not reopened)
#
# What each scenario proves (the invariants of docs/testing.md, "The delta store"):
#   dl-clean-1      a promotion PR: compiles ONLY its own modules (restores that missed = 0), publishes a delta NAMED BY ITS MERGE COMMIT on main
#   dl-clean-2      the next one: its queue build restores the first's delta (the check that the squash-merged commit and the delta name agree)
#   dl-broken       a broken promotion: ejected, publishes no delta
#   dl-clean-3      a clean one after the ejection: merges with a delta; no delta is applied for a commit that is not in main's history
#                   (orphans are listed, never used)
# The scenarios run ONE AT A TIME, each from the main the previous left: data files are append-only (the gate refuses any other edit), so two
# promotions open together conflict in the queue as soon as the first merges. Each promotion PR touches data/trusted/, which the code owner
# approves: the script opens the PR, says so in the log, and waits for the approval and the merge (up to 45 min per scenario).
#   dl-docs-only    a group that changes no build output merges with no delta and the gate green
#   dl-publish-fail (needs the repository variable TOPUP_TEST_FAIL = its PR number) the gate cannot publish: removed from the queue with
#                   the "not because of your change" comment, nothing merged, no delta
#   dl-over-budget  (needs TENGOKU_DELTA_BUDGET_MB = 0) a clean merge lands marked needs-nightly, publishes no delta, starts the nightly
#   real-tree       lake-cache-tests.yml with real_tree=true: a fresh runner seeds + restores every delta of main and builds with --no-build
# A knob the user has not set skips its scenario and says so: this script never changes repository variables.
source "$(dirname "$0")/lib.sh"
DR="$C/deltas-results.tsv"
FROM=${DELTAS_FROM:-1}
APPROVAL_AND_QUEUE_MIN=${DELTAS_WAIT_MIN:-300}   # the code owner approves each promotion: that wait is most of it, the queue build is ~45 min
step() { [ "$FROM" -le "$1" ]; }
MODE=${1:-run}
record() { printf "%s\t%s\t%s\t%s\t%s\n" "$1" "$2" "$3" "$4" "$5" >> "$DR"; log "deltas $1 (#$2): expected $3, got $4 | $5"; }

pr_of() { awk -F'\t' -v n="$1" '$1==n {print $5; exit}' "$EXPECT"; }
enqueue() { gh pr merge "$1" -R "$REPO" --squash --auto >/dev/null 2>&1; }
ejection() { gh api "repos/$REPO/issues/$1/comments" -q '[.[] | select(.body | test("Removed from the merge queue"))] | last | .body' 2>/dev/null; }
wait_pr() {  # N MAXMIN -> merged|ejected|timeout
  local n=$1 max=${2:-40} i st c
  for i in $(seq 1 $((max * 2))); do
    st=$(gh pr view "$n" -R "$REPO" --json state -q .state 2>/dev/null)
    [ "$st" = MERGED ] && { echo merged; return; }
    c=$(ejection "$n"); if [ -n "$c" ] && [ "$c" != null ]; then echo ejected; return; fi
    sleep 30
  done
  echo timeout
}
mg_run() {  # newest merge-group queue-gate run id for pr N
  gh run list -R "$REPO" --workflow queue-gate.yml --event merge_group --limit 20 --json databaseId,headBranch,createdAt -q "[.[] | select(.headBranch | contains(\"/pr-$1-\"))] | sort_by(.createdAt) | last | .databaseId" 2>/dev/null
}
qb_log() {  # the queue-build log of pr N's newest merge-group run
  local id jid; id=$(mg_run "$1"); [ -n "$id" ] && [ "$id" != null ] || return 1
  jid=$(gh api "repos/$REPO/actions/runs/$id/jobs" -q '.jobs[] | select(.name=="queue-build") | .id' 2>/dev/null); [ -n "$jid" ] || return 1
  gh api "repos/$REPO/actions/jobs/$jid/logs" 2>/dev/null | sed 's/^[^ ]*Z //'
}
json_field() { python3 -c 'import json,sys,re
key=sys.argv[1]; out=""
for ln in sys.stdin:
    ln=ln.strip()
    if ln.startswith("{") and key in ln:
        try: out=json.loads(ln).get(key, "");
        except Exception: pass
print(out)' "$1"; }
cache_tag() { curl -fsSL "https://github.com/$REPO/releases/download/cache-latest/cache-latest.json" | python3 -c 'import json,sys; print(json.load(sys.stdin)["tag"])'; }
assets() { gh release view "lake-deltas-$(cache_tag)" -R "$REPO" --json assets -q '.assets[].name' 2>/dev/null; }
merge_sha() { gh pr view "$1" -R "$REPO" --json mergeCommit -q .mergeCommit.oid 2>/dev/null; }
build_runs_after() { gh run list -R "$REPO" --workflow build.yml --limit 5 --json createdAt -q "[.[] | select(.createdAt > \"$1\")] | length"; }

# A promotion-class PR: fresh trusted records of equational-theories and the regenerated module (the bot's own PR class, author = TENGOKU_BOT).
corpus() {
  [ -d corpora/equational-theories/.git ] && return 0
  python3 - <<'PY'
import json, subprocess
s = json.load(open("schemas/sources.json"))
src = s["corpora"]["equational-theories"]
url, rev = src["repo"], src["commit"]
# the pinned commit is not on any branch of the upstream (a clone does not have it): fetched by its hash
subprocess.run(["git", "init", "-q", "corpora/equational-theories"], check=True)
subprocess.run(["git", "-C", "corpora/equational-theories", "fetch", "-q", "--depth", "1", url, rev], check=True)
subprocess.run(["git", "-C", "corpora/equational-theories", "checkout", "-q", "FETCH_HEAD"], check=True)
PY
}
# One promotion at a time, each opened from the main the previous one left. A promotion appends its records at the end of
# data/trusted/equational-theories.jsonl (the gate refuses any other edit of a data file), so two promotions open at once conflict in the queue
# the moment the first merges (reproduced with git merge), and the library is the only one the promotion class can promote.
promotion() {  # NAME NRECORDS [proof]  -> opens promote/deltas-NAME, records its PR number
  local name=$1 n=$2 proof=${3:-":= rfl"} i
  cd "$WORK" && git fetch -q origin main && git checkout -q -B "promote/deltas-$name" origin/main || return 1
  corpus || { log "FIXTURE-ERROR $name: the corpus could not be fetched"; return 1; }
  for i in $(seq 1 "$n"); do rec "D${name//-/_}_$i" "proof=$proof" "status=trusted" | python3 -c 'import json,sys,datetime; r=json.loads(sys.stdin.read()); r["promoted_at"]=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"); print(json.dumps(r, ensure_ascii=False))' >> data/trusted/equational-theories.jsonl; done
  # --only: the one module; the generator knows a single corpus here and would rewrite Tengoku/All.lean down to the libraries it sees (a real promotion never touches it)
  python3 scripts/generate.py --corpus corpora/equational-theories --libraries equational-theories --only "$SRC_PATH" >/dev/null 2>&1 || { log "FIXTURE-ERROR $name: generate.py failed"; return 1; }
  git checkout -q -- Tengoku/All.lean
  git add -A . && git commit -q -s -m "Promote equational-theories: deltas scenario $name" && git push -q -f origin "promote/deltas-$name"
  local num
  num=$(gh pr list -R "$REPO" --head "promote/deltas-$name" --state open --json number -q '.[0].number')
  [ -n "$num" ] || { gh pr create -R "$REPO" --head "promote/deltas-$name" --title "Promote equational-theories: deltas scenario $name" --body "T2 of the delta store (scripts/ci/campaign/deltas.sh): $n record(s). Needs the code owner's approval (data/trusted/)." >/dev/null 2>&1; num=$(gh pr list -R "$REPO" --head "promote/deltas-$name" --state open --json number -q '.[0].number'); }
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "dl-$name" pass - queue "$num" "deltas scenario $name" >> "$EXPECT"
  log "opened #$num dl-$name: needs the code owner's approval, then it is queued"; git checkout -q -f main
}
judge_merged() {  # NAME: merged, 0 misses, a delta published for its merge commit
  local name=$1 n got l misses dec sha v
  n=$(pr_of "dl-$name"); got=$(wait_pr "$n" "$APPROVAL_AND_QUEUE_MIN")
  l=$(qb_log "$n"); misses=$(json_field misses <<< "$l"); dec=$(json_field decision <<< "$l"); sha=$(merge_sha "$n")
  v=OK; [ "$got" = merged ] || v=WRONG; [ "$misses" = 0 ] || v="WRONG(misses=$misses)"; [ "$dec" = publish ] || v="$v(decision=$dec)"
  if [ -n "$sha" ] && ! assets | grep -qx "d-$sha.tar.zst"; then v="$v(no delta d-${sha:0:9})"; fi
  record "dl-$name" "$n" "merged+delta" "$got misses=$misses decision=$dec" "$v"
}

if [ "$MODE" = "--report" ]; then column -t -s $'\t' "$DR"; exit 0; fi
[ "$FROM" = 1 ] && : > "$DR"
log "=== deltas T2 on $REPO (cache $(cache_tag)); assets now: $(assets | wc -l)"
clean() {  # NAME NRECORDS: a promotion from the current main (an earlier run's PR, open or merged, is picked up), queued once approved, judged
  local n st=""
  n=$(pr_of "dl-$1"); [ -z "$n" ] || st=$(gh pr view "$n" -R "$REPO" --json state -q .state)
  if [ "$st" != OPEN ] && [ "$st" != MERGED ]; then promotion "$1" "$2" || exit 1; fi
  [ "$st" = MERGED ] || enqueue "$(pr_of "dl-$1")"
  judge_merged "$1"
}
step 1 && {
log "=== 1. a clean promotion: compiles only its own modules, publishes a delta named by its merge commit"
clean clean-1 3
}
step 2 && {
log "=== 2. a second one on top of it: restores the first's delta, compiles only its own modules"
clean clean-2 3
n=$(pr_of dl-clean-2); applied=$(qb_log "$n" | json_field applied); first=$(merge_sha "$(pr_of dl-clean-1)"); v=OK
[[ "$applied" == *"d-$first"* ]] || v="WRONG(restored: $applied)"
record dl-clean-2-restore "$n" "restored d-${first:0:9}" "$applied" "$v"
}
step 3 && {
log "=== 3. a broken promotion is ejected and publishes no delta"
promotion broken 1 ':= by\n  exact (by decide : (1 : Nat) + 1 = 3)' || exit 1; enqueue "$(pr_of dl-broken)"
n=$(pr_of dl-broken); got=$(wait_pr "$n" "$APPROVAL_AND_QUEUE_MIN"); sha=$(gh pr view "$n" -R "$REPO" --json headRefOid -q .headRefOid); v=OK; [ "$got" = ejected ] || v=WRONG
assets | grep -q "d-$sha" && v="$v(a delta for the ejected head?)"; record dl-broken "$n" ejected "$got" "$v"
}
step 4 && {
log "=== 4. a clean one after the ejection: merges with a delta, and no delta is applied for a commit that is not in main's history"
clean clean-3 2
orphans=0; for a in $(assets | grep -E '^d-[0-9a-f]{40}\.tar\.zst$'); do c=${a:2:40}; git -C "$WORK" fetch -q origin main; git -C "$WORK" merge-base --is-ancestor "$c" origin/main 2>/dev/null || orphans=$((orphans + 1)); done
log "orphan deltas in the release (published for commits not on main; never applied, collected with the nightly): $orphans"
}
step 5 && {
log "=== 5. a group that changes no build output"
cd "$WORK" && scenario dl-docs-only pass - yes queue "A docs line: no Lean target, no delta, green." 'printf "\n<!-- deltas scenario -->\n" >> docs/testing.md'
n=$(pr_of dl-docs-only); enqueue "$n"; got=$(wait_pr "$n" 30); l=$(qb_log "$n"); v=OK; [ "$got" = merged ] || v=WRONG
grep -q "no Lean targets in this group" <<< "$l" || v="$v(targets?)"; sha=$(merge_sha "$n"); assets | grep -q "d-$sha" && v="$v(a delta for a docs change?)"
record dl-docs-only "$n" "merged, no delta" "$got" "$v"
}
step 6 && {
log "=== 6. the gate cannot publish (knob: TOPUP_TEST_FAIL)"
knob=$(gh variable get TOPUP_TEST_FAIL -R "$REPO" 2>/dev/null || true)
if [ -z "$knob" ]; then
  record dl-publish-fail "-" "removed, nothing merged" "SKIPPED" "set the repository variable TOPUP_TEST_FAIL to the number of the PR this scenario opens (the next number in the repository), then re-run"
else
  promotion publish-fail 1 || exit 1; n=$(pr_of dl-publish-fail)
  [ "$knob" = "$n" ] || log "TOPUP_TEST_FAIL is $knob, this scenario's PR is #$n: the publish will not be made to fail"
  enqueue "$n"; got=$(wait_pr "$n" "$APPROVAL_AND_QUEUE_MIN"); v=OK; [ "$got" = ejected ] || v=WRONG
  gh api "repos/$REPO/issues/$n/comments" -q '.[].body' | grep -q "not because of your change" || v="$v(no comment)"
  record dl-publish-fail "$n" "removed, nothing merged" "$got" "$v"
fi
}
step 7 && {
log "=== 7. over the delta budget (knob: TENGOKU_DELTA_BUDGET_MB = 0)"
knob=$(gh variable get TENGOKU_DELTA_BUDGET_MB -R "$REPO" 2>/dev/null || true)
if [ "$knob" = 0 ]; then
  promotion over-budget 1 || exit 1; n=$(pr_of dl-over-budget); t0=$(date -u +%Y-%m-%dT%H:%M:%SZ); enqueue "$n"; got=$(wait_pr "$n" "$APPROVAL_AND_QUEUE_MIN")
  l=$(qb_log "$n"); dec=$(json_field decision <<< "$l"); v=OK; [ "$got" = merged ] || v=WRONG; [ "$dec" = "needs-nightly:over-budget" ] || v="$v(decision=$dec)"
  sha=$(merge_sha "$n"); assets | grep -q "d-$sha" && v="$v(a delta although over budget?)"; [ "$(build_runs_after "$t0")" -ge 1 ] || v="$v(no nightly started)"
  record dl-over-budget "$n" "merged, needs-nightly, nightly started" "$got decision=$dec" "$v"
else
  record dl-over-budget "-" "merged, needs-nightly, nightly started" "SKIPPED" "set the repository variable TENGOKU_DELTA_BUDGET_MB to 0 (and unset it afterwards), then re-run this scenario"
fi
}
step 8 && {
log "=== 8. the real tree: seed + restore every delta of main + lake build Tengoku.All --no-build"
gh workflow run lake-cache-tests.yml -R "$REPO" --ref main -f real_tree=true >/dev/null 2>&1 && sleep 20
rid=$(gh run list -R "$REPO" --workflow lake-cache-tests.yml --limit 1 --json databaseId -q '.[0].databaseId')
for i in $(seq 1 120); do st=$(gh run view "$rid" -R "$REPO" --json status,conclusion -q '.status + " " + (.conclusion // "")'); case "$st" in completed*) break;; esac; sleep 30; done
record real-tree "$rid" "restore + --no-build pass" "$st" "$( [ "$st" = "completed success" ] && echo OK || echo WRONG)"
}
log "=== done"; column -t -s $'\t' "$DR"
