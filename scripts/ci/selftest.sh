#!/bin/bash
# selftest.sh <owner/repo> — test the tests: open one PR per scenario and report what the gate decided.
#   scripts/ci/selftest.sh competemath/tengoku-sandbox           # open the PRs
#   scripts/ci/selftest.sh competemath/tengoku-sandbox --report  # poll pr-gate and print PASS/FAIL per scenario against the expectation
set -u
REPO=$1; MODE=${2:-open}
REMOTE=$(git remote -v | awk -v r="$REPO" '$2 ~ r {print $1; exit}')
[ -n "$REMOTE" ] || { echo "no git remote for $REPO"; exit 2; }
git fetch -q "$REMOTE" main
GOOD='{"name": "Selftest.NAME", "statement": "theorem Selftest.NAME : (1 : Nat) + 1 = 2", "proof": ":= rfl", "status": "staging", "library": "equational-theories", "source_url": "https://github.com/teorth/equational_theories/blob/selftest", "toolchain": "leanprover/lean4:v4.34.0-rc2"}'
rec() { echo "$GOOD" | sed "s/NAME/$1/g"; }
scenario() {  # name expect(pass|fail) signoff(yes|no) body -- shell that edits the tree
  local name=$1 expect=$2 signoff=$3 body=$4; shift 4
  git checkout -q -B "selftest/$name" "$REMOTE/main"
  eval "$@"
  git add -A
  if [ "$signoff" = yes ]; then git commit -q -s -m "selftest: $name"; else git commit -q -m "selftest: $name"; fi
  git push -q -f "$REMOTE" "selftest/$name"
  gh pr create -R "$REPO" --head "selftest/$name" --title "selftest: $name (expect $expect)" --body "$body" >/dev/null 2>&1 && echo "opened $name (expect $expect)"
  echo "$name $expect" >> /tmp/selftest-expect.txt
}
if [ "$MODE" = "open" ]; then
  : > /tmp/selftest-expect.txt
  scenario clean-append pass yes "One good record appended to staging." 'rec good1 >> data/staging/equational-theories.jsonl'
  scenario two-purposes fail yes "Content and tooling in one PR." 'rec good2 >> data/staging/equational-theories.jsonl; echo "# touched" >> scripts/stats.py'
  scenario delete-in-staging fail yes "Deletes a staging line." 'sed -i "" -e "1d" data/staging/equational-theories.jsonl 2>/dev/null || sed -i -e "1d" data/staging/equational-theories.jsonl'
  scenario eval-in-record fail yes "Record whose context runs code." 'rec bad3 | python3 -c "import sys,json; r=json.loads(sys.stdin.read()); r[\"context\"]=\"#eval IO.println 1\"; print(json.dumps(r))" >> data/staging/equational-theories.jsonl'
  scenario credit-removed fail yes "Removes an Authors line from a seeded module." 'f=$(grep -rl "^Authors:" Tengoku/Logic | head -1); sed -i "" -e "/^Authors:/d" "$f" 2>/dev/null || sed -i -e "/^Authors:/d" "$f"'
  scenario fake-secret fail yes "Contains a credential-shaped string." 'printf "AWS_KEY=AKIAIOSFODNN7EXAMPLE\nAWS_SECRET=wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY\n" > docs-secret.txt'
  scenario unsigned fail no "Commit without Signed-off-by." 'rec good4 >> data/staging/equational-theories.jsonl'
  scenario derived-edit fail yes "Hand edit of a generated module." 'f=$(ls Tengoku/EquationalTheories/*.lean | head -1); echo "-- hand edit" >> "$f"'
  scenario bad-source fail yes "Record from a repository not on the allowlist." 'rec bad5 | sed "s|https://github.com/teorth/equational_theories/blob/selftest|https://example.com/x|" >> data/staging/equational-theories.jsonl'
  scenario broken-proof pass yes "Passes the PR gate (no Lean there); the merge queue must eject it." 'rec broken | python3 -c "import sys,json; r=json.loads(sys.stdin.read()); r[\"proof\"]=\":= by\\n  exact (by decide : (1 : Nat) + 1 = 3)\"; print(json.dumps(r))" >> data/staging/equational-theories.jsonl'
  scenario tooling-change pass yes "A comment in a script: lint + tooling tests must run and pass." 'printf "\n# selftest touch\n" >> scripts/ci/_git.py'
  git checkout -q main
else
  printf "%-18s %-8s %-8s %s\n" scenario expect got verdict
  while read -r name expect; do
    n=$(gh pr list -R "$REPO" --head "selftest/$name" --json number -q '.[0].number')
    st=$(gh pr checks "$n" -R "$REPO" --json name,state -q '.[] | select(.name=="pr-gate") | .state' 2>/dev/null)
    case "$st" in SUCCESS) got=pass;; FAILURE|ERROR|CANCELLED) got=fail;; *) got=pending;; esac
    if [ "$got" = pending ]; then v="…"; elif [ "$got" = "$expect" ]; then v="OK"; else v="WRONG"; fi
    printf "%-18s %-8s %-8s %s  #%s\n" "$name" "$expect" "$got" "$v" "$n"
  done < /tmp/selftest-expect.txt
fi
