#!/usr/bin/env bash
# studied_approval.sh <pr-number> — gather who reviewed a STUDIED PR and decide (scripts/ci/studied_approval.py: one code owner, or two independent
# contributors with write access). Reads the PR through the API with GH_TOKEN (read-only: pull requests, collaborator permissions) and runs main's
# script; it checks out nothing of the PR. Run from a checkout of main (the code owners come from its .github/CODEOWNERS `*` line).
set -euo pipefail
pr="${1:?usage: studied_approval.sh <pr-number>}"
repo="${GITHUB_REPOSITORY:?}"
info="$(gh api "repos/$repo/pulls/$pr" --jq '{author: .user.login, head: .head.sha}')"
author="$(jq -r .author <<<"$info")"
head="$(jq -r .head <<<"$info")"
reviews="$(gh api --paginate "repos/$repo/pulls/$pr/reviews" --jq '[.[] | {user: .user.login, state: .state, commit_id: .commit_id, type: .user.type}]' | jq -s 'add // []')"
committers="$(gh api --paginate "repos/$repo/pulls/$pr/commits" --jq '[.[] | (.author.login // empty), (.committer.login // empty)]' | jq -s 'add // [] | unique')"
owners="$(sed -n 's/^\*[[:space:]]\{1,\}//p' .github/CODEOWNERS | head -n1 | tr -s ' \t' '\n' | sed 's/^@//' | sed '/^$/d' | jq -R . | jq -s .)"
perms='{}'
for u in $(jq -r '[.[] | select(.state == "APPROVED") | .user] | unique | .[]' <<<"$reviews"); do
  p="$(gh api "repos/$repo/collaborators/$u/permission" --jq .permission 2>/dev/null || echo none)"
  perms="$(jq --arg u "$u" --arg p "$p" '.[$u] = $p' <<<"$perms")"
done
out="${RUNNER_TEMP:-/tmp}/studied-approval.json"
jq -n --arg author "$author" --arg head "$head" --argjson owners "$owners" --argjson committers "$committers" --argjson permissions "$perms" --argjson reviews "$reviews" \
  '{author: $author, head: $head, owners: $owners, committers: $committers, permissions: $permissions, reviews: $reviews}' >"$out"
python3 scripts/ci/studied_approval.py <"$out"
