#!/bin/bash
# Promote every staging file that has gone quiet, forever.
#   scripts/promote-loop.sh <corpus checkout> [library] [interval s] [quiescent s]
# The banking hook only stages records as they arrive; this loop turns the
# files it has finished with into trusted modules, one build per file.
#
# Two modes:
#   default            commit and push straight to main (the pre-ruleset flow).
#   TENGOKU_VIA_PRS=1  never touch main: one promotion PR per source file, from a
#                      `promote/<library>/<file>-<stamp>` branch, signed off,
#                      auto-merged through the queue; the loop waits for each
#                      merge (promotions share data/trusted and All.lean, so two
#                      open at once would conflict in the queue). A PR the queue
#                      ejects puts its source file on a 24 h skip list
#                      (.promote-skip) and is left open for a maintainer.
set -u
CORPUS=$1; LIB=${2:-equational-theories}; INTERVAL=${3:-300}; QUIET=${4:-300}
ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT" || exit 1
LIB_NS=$(python3 -c "import sys; sys.path.insert(0,'scripts'); from generate import pascal; print(pascal('$LIB'))") || exit 1  # a reserved key exits non-zero: an empty LIB_NS would put all of Tengoku/ in PATHS
PATHS="data/staging data/trusted data/stats.json Tengoku/$LIB_NS Tengoku/$LIB_NS.lean Tengoku/All.lean"
SKIP=.promote-skip
skipped() { [ -f "$SKIP" ] && awk -v sp="$1" -v now="$(date +%s)" '$1==sp && now-$2 < 86400 {f=1} END {exit !f}' "$SKIP"; }
quiet_sources() {  # source paths with staging records, oldest first
  python3 - "$LIB" <<'PY'
import glob, json, sys
lib = sys.argv[1]; seen = {}
for f in [f"data/staging/{lib}.jsonl"] + sorted(glob.glob(f"data/staging/{lib}/*.jsonl")):
    try: lines = open(f, encoding="utf-8").read().splitlines()
    except FileNotFoundError: continue
    for l in lines:
        if not l.strip(): continue
        r = json.loads(l)
        if r.get("source_path") and r.get("context") is not None: seen.setdefault(r["source_path"], r.get("staged_at", ""))
for sp, _ in sorted(seen.items(), key=lambda kv: kv[1]): print(sp)
PY
}
direct_mode() {
  out=$(python3 scripts/promote.py --corpus "$CORPUS" --library "$LIB" --quiescent "$QUIET" 2>&1); rc=$?
  last=$(printf '%s\n' "$out" | tail -1)
  echo "[$(date +%T)] rc=$rc $last"
  printf '%s\n' "$out" | grep "^NOT promoted" | cut -c1-300
  if printf '%s\n' "$out" | grep -q "^promoted \|^NOT promoted"; then
    python3 scripts/stats.py >/dev/null 2>&1 || true   # data/stats.json feeds the site's stat pills
    for _ in 1 2 3 4 5; do
      git add -A -- $PATHS 2>/dev/null && git commit -q -m "Promote $LIB: $last" 2>/dev/null && break
      sleep 3
    done
    git push -q origin main 2>/dev/null || true
  fi
}
pr_mode() {
  git checkout -q main 2>/dev/null
  pull_err=$(git pull -q --ff-only origin main 2>&1) || echo "[$(date +%T)] pull failed; working on what is here: $(printf '%s' "$pull_err" | tail -1)"
  local repo; repo=$(git remote get-url origin | sed -E 's#.*github.com[:/]##; s#\.git$##')
  quiet_sources | while read -r sp; do
    skipped "$sp" && continue
    out=$(python3 scripts/promote.py --corpus "$CORPUS" --library "$LIB" --only "$sp" --quiescent "$QUIET" 2>&1); rc=$?
    last=$(printf '%s\n' "$out" | tail -1)
    if ! printf '%s\n' "$out" | grep -q "^promoted "; then
      printf '%s\n' "$out" | grep "^NOT promoted" | cut -c1-300
      git checkout -q -- data/staging 2>/dev/null   # promote.py wrote build_error into the record; main is read-only in this mode
      printf '%s\n' "$out" | grep -q "^NOT promoted" && echo "$sp $(date +%s)" >> "$SKIP"
      continue
    fi
    python3 scripts/stats.py >/dev/null 2>&1 || true
    local slug branch n
    slug=$(printf '%s' "$sp" | sed -E 's#\.lean$##; s#[^A-Za-z0-9]+#-#g' | cut -c1-60)
    branch="promote/$LIB/$slug-$(date -u +%Y%m%dT%H%M%SZ)"
    git checkout -q -B "$branch" && git add -A -- $PATHS && git commit -q -s -m "Promote $LIB: $last" && git push -q -u origin "$branch" || { echo "[$(date +%T)] could not push $branch"; git checkout -q -f main; continue; }
    n=$(gh pr create -R "$repo" --head "$branch" --title "Promote $LIB: $sp" --body "Promotion by the banking pipeline: $last" 2>/dev/null | grep -oE '[0-9]+$')
    gh pr merge "$n" -R "$repo" --squash --auto >/dev/null 2>&1
    git checkout -q main
    echo "[$(date +%T)] PR #$n for $sp: $last"
    local i st
    for i in $(seq 1 60); do
      st=$(gh pr view "$n" -R "$repo" --json state -q .state 2>/dev/null)
      [ "$st" = MERGED ] && break
      if [ "$(gh api "repos/$repo/issues/$n/comments" -q '[.[] | select(.body | test("Removed from the merge queue"))] | length' 2>/dev/null)" != 0 ]; then st=EJECTED; break; fi
      sleep 30
    done
    if [ "$st" = MERGED ]; then git pull -q --ff-only origin main; echo "[$(date +%T)] PR #$n merged"
    else echo "[$(date +%T)] PR #$n $st — left open for a maintainer; $sp skipped for 24 h"; echo "$sp $(date +%s)" >> "$SKIP"; fi
  done
}
while true; do
  if [ "${TENGOKU_VIA_PRS:-0}" = 1 ]; then pr_mode; else direct_mode; fi
  sleep "$INTERVAL"
done
