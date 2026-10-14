#!/bin/bash
# T2 of the delta store (scripts/lake_cache.py, queue-gate.yml): real pull requests through the SANDBOX merge queue, each read back from the
# queue-build log, the gate's verdict and the release `lake-deltas-<cache tag>`. Run after the queue rewrite is on the sandbox's main.
#
#   scripts/ci/campaign/deltas.sh            # open the scenario PRs, queue them in the designed order, judge each (hours)
#   scripts/ci/campaign/deltas.sh --report   # print the results table again
#
# What each scenario proves (the invariants of docs/testing.md, "The delta store"):
#   dl-clean-1..3   three promotion PRs queued together: each compiles ONLY its own modules (restores that missed = 0), each publishes a delta
#   dl-a/broken/b   a broken PR between two clean ones: the clean ones merge with deltas, the broken one is ejected and publishes none,
#                   and no delta is applied for a commit that is not in main's history (orphans are listed, never used)
#   dl-docs-only    a group that changes no build output merges with no delta and the gate green
#   dl-publish-fail (needs the repository variable TOPUP_TEST_FAIL = its PR number) the gate cannot publish: removed from the queue with
#                   the "not because of your change" comment, nothing merged, no delta
#   dl-over-budget  (needs TENGOKU_DELTA_BUDGET_MB = 0) a clean merge lands marked needs-nightly, publishes no delta, starts the nightly
#   real-tree       lake-cache-tests.yml with real_tree=true: a fresh runner seeds + restores every delta of main and builds with --no-build
# A knob the user has not set skips its scenario and says so: this script never changes repository variables.
source "$(dirname "$0")/lib.sh"
DR="$C/deltas-results.tsv"
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
subprocess.run(["git", "clone", "-q", url, "corpora/equational-theories"], check=True)
subprocess.run(["git", "-C", "corpora/equational-theories", "checkout", "-q", rev], check=True)
PY
}
promotion() {  # NAME NRECORDS [proof]  -> opens promote/deltas-NAME, records its PR number
  local name=$1 n=$2 proof=${3:-":= rfl"} i
  cd "$WORK" && git fetch -q origin main && git checkout -q -B "promote/deltas-$name" origin/main || return 1
  corpus || { log "FIXTURE-ERROR $name: the corpus could not be fetched"; return 1; }
  for i in $(seq 1 "$n"); do rec "D${name//-/_}_$i" "proof=$proof" "status=trusted" | python3 -c 'import json,sys,datetime; r=json.loads(sys.stdin.read()); r["promoted_at"]=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"); print(json.dumps(r, ensure_ascii=False))' >> data/trusted/equational-theories.jsonl; done
  python3 scripts/generate.py --corpus corpora/equational-theories --libraries equational-theories >/dev/null 2>&1 || { log "FIXTURE-ERROR $name: generate.py failed"; return 1; }
  git add -A . && git commit -q -s -m "Promote equational-theories: deltas scenario $name" && git push -q -f origin "promote/deltas-$name"
  local num
  num=$(gh pr list -R "$REPO" --head "promote/deltas-$name" --state open --json number -q '.[0].number')
  [ -n "$num" ] || { gh pr create -R "$REPO" --head "promote/deltas-$name" --title "Promote equational-theories: deltas scenario $name" --body "T2 of the delta store (scripts/ci/campaign/deltas.sh): $n record(s)." >/dev/null 2>&1; num=$(gh pr list -R "$REPO" --head "promote/deltas-$name" --state open --json number -q '.[0].number'); }
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "dl-$name" pass - queue "$num" "deltas scenario $name" >> "$EXPECT"
  log "opened #$num dl-$name"; git checkout -q -f main
}
judge_merged() {  # NAME: merged, 0 misses, a delta published for its merge commit
  local name=$1 n got l misses dec sha v
  n=$(pr_of "dl-$name"); got=$(wait_pr "$n" 45)
  l=$(qb_log "$n"); misses=$(json_field misses <<< "$l"); dec=$(json_field decision <<< "$l"); sha=$(merge_sha "$n")
  v=OK; [ "$got" = merged ] || v=WRONG; [ "$misses" = 0 ] || v="WRONG(misses=$misses)"; [ "$dec" = publish ] || v="$v(decision=$dec)"
  if [ -n "$sha" ] && ! assets | grep -qx "d-$sha.tar.zst"; then v="$v(no delta d-${sha:0:9})"; fi
  record "dl-$name" "$n" "merged+delta" "$got misses=$misses decision=$dec" "$v"
}

if [ "$MODE" = "--report" ]; then column -t -s $'\t' "$DR"; exit 0; fi
: > "$DR"
log "=== deltas T2 on $REPO (cache $(cache_tag)); assets now: $(assets | wc -l)"
log "=== 1. three clean promotion PRs, queued together (stacked groups)"
promotion clean-1 3; promotion clean-2 3; promotion clean-3 3
for s in clean-1 clean-2 clean-3; do enqueue "$(pr_of dl-$s)"; done
for s in clean-1 clean-2 clean-3; do judge_merged "$s"; done
log "=== 2. a broken PR between two clean ones, queued in order"
promotion a 2; promotion broken 1 ':= by\n  exact (by decide : (1 : Nat) + 1 = 3)'; promotion b 2
for s in a broken b; do enqueue "$(pr_of dl-$s)"; sleep 20; done
judge_merged a
n=$(pr_of dl-broken); got=$(wait_pr "$n" 45); sha=$(gh pr view "$n" -R "$REPO" --json headRefOid -q .headRefOid); v=OK; [ "$got" = ejected ] || v=WRONG
assets | grep -q "d-$sha" && v="$v(a delta for the ejected head?)"; record dl-broken "$n" ejected "$got" "$v"
judge_merged b
orphans=0; for a in $(assets | grep -E '^d-[0-9a-f]{40}\.tar\.zst$'); do c=${a:2:40}; git -C "$WORK" fetch -q origin main; git -C "$WORK" merge-base --is-ancestor "$c" origin/main 2>/dev/null || orphans=$((orphans + 1)); done
log "orphan deltas in the release (published for commits not on main; never applied, collected with the nightly): $orphans"
log "=== 3. a group that changes no build output"
cd "$WORK" && scenario dl-docs-only pass - yes queue "A docs line: no Lean target, no delta, green." 'printf "\n<!-- deltas scenario -->\n" >> docs/testing.md'
n=$(pr_of dl-docs-only); enqueue "$n"; got=$(wait_pr "$n" 30); l=$(qb_log "$n"); v=OK; [ "$got" = merged ] || v=WRONG
grep -q "no Lean targets in this group" <<< "$l" || v="$v(targets?)"; sha=$(merge_sha "$n"); assets | grep -q "d-$sha" && v="$v(a delta for a docs change?)"
record dl-docs-only "$n" "merged, no delta" "$got" "$v"
log "=== 4. the gate cannot publish (knob: TOPUP_TEST_FAIL)"
promotion publish-fail 1; n=$(pr_of dl-publish-fail)
knob=$(gh variable get TOPUP_TEST_FAIL -R "$REPO" 2>/dev/null || true)
if [ "$knob" = "$n" ]; then
  enqueue "$n"; got=$(wait_pr "$n" 45); v=OK; [ "$got" = ejected ] || v=WRONG
  gh api "repos/$REPO/issues/$n/comments" -q '.[].body' | grep -q "not because of your change" || v="$v(no comment)"
  record dl-publish-fail "$n" "removed, nothing merged" "$got" "$v"
else
  record dl-publish-fail "$n" "removed, nothing merged" "SKIPPED" "set the repository variable TOPUP_TEST_FAIL to $n, then re-run this scenario"
fi
log "=== 5. over the delta budget (knob: TENGOKU_DELTA_BUDGET_MB = 0)"
knob=$(gh variable get TENGOKU_DELTA_BUDGET_MB -R "$REPO" 2>/dev/null || true)
if [ "$knob" = 0 ]; then
  promotion over-budget 1; n=$(pr_of dl-over-budget); t0=$(date -u +%Y-%m-%dT%H:%M:%SZ); enqueue "$n"; got=$(wait_pr "$n" 45)
  l=$(qb_log "$n"); dec=$(json_field decision <<< "$l"); v=OK; [ "$got" = merged ] || v=WRONG; [ "$dec" = "needs-nightly:over-budget" ] || v="$v(decision=$dec)"
  sha=$(merge_sha "$n"); assets | grep -q "d-$sha" && v="$v(a delta although over budget?)"; [ "$(build_runs_after "$t0")" -ge 1 ] || v="$v(no nightly started)"
  record dl-over-budget "$n" "merged, needs-nightly, nightly started" "$got decision=$dec" "$v"
else
  record dl-over-budget "-" "merged, needs-nightly, nightly started" "SKIPPED" "set the repository variable TENGOKU_DELTA_BUDGET_MB to 0 (and unset it afterwards), then re-run this scenario"
fi
log "=== 6. the real tree: seed + restore every delta of main + lake build Tengoku.All --no-build"
gh workflow run lake-cache-tests.yml -R "$REPO" --ref main -f real_tree=true >/dev/null 2>&1 && sleep 20
rid=$(gh run list -R "$REPO" --workflow lake-cache-tests.yml --limit 1 --json databaseId -q '.[0].databaseId')
for i in $(seq 1 120); do st=$(gh run view "$rid" -R "$REPO" --json status,conclusion -q '.status + " " + (.conclusion // "")'); case "$st" in completed*) break;; esac; sleep 30; done
record real-tree "$rid" "restore + --no-build pass" "$st" "$( [ "$st" = "completed success" ] && echo OK || echo WRONG)"
log "=== done"; column -t -s $'\t' "$DR"
