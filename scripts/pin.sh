#!/usr/bin/env bash
# Pin this checkout of the tree to the newest PUBLISHED build cache. Nothing
# is ever compiled here: the replay check runs with `--no-build`, so Lake can
# only confirm the cache covers the tree, or fail.
#
#   scripts/pin.sh            # fetch → newest cache commit → check it out → unpack its cache → replay-build
#   scripts/pin.sh --check    # change nothing: print "current <sha>" (exit 0) or "newer <sha>" (exit 3)
#
# TENGOKU_TOPUPS=1 follows the per-merge top-ups as well: the newest commit on
# main whose small difference from the nightly cache has been published. The
# nightly cache is downloaded once per day; a refresh in between fetches only
# the top-up. If a top-up does not replay, the checkout returns to the state it
# came from (exit 4: nothing changed, keep serving), or failing that to the
# nightly cache's own commit — never a half-right build.
#
# The Leak services run this at image build, at container start, from their
# `tengoku_sync` tool and on POST /refresh (which the nightly cache workflow
# calls right after it publishes). Safe to run repeatedly: a tree already at
# the newest cache commit with its build present is a no-op.
set -euo pipefail
cd "$(dirname "$0")/.."

git fetch -q origin main
# Ask with the newest cache.sh: an older pinned copy may list caches in the
# wrong order. (Restored by the checkout below; harmless if we stop early.)
newest_scripts() {  # topup.py is absent from older commits, so each file is fetched on its own
  for f in scripts/cache.sh scripts/topup.py "$@"; do git checkout -q origin/main -- "$f" 2>/dev/null || true; done
}
export TENGOKU_TOPUPS="${TENGOKU_TOPUPS:-0}"
newest_scripts
latest="$(scripts/cache.sh latest)"
tag="$(scripts/cache.sh latest-tag)"
head="$(git rev-parse HEAD)"
built=""
was="$(python3 scripts/topup.py status 2>/dev/null | python3 -c 'import json,sys; print(json.load(sys.stdin).get("tip") or "")' 2>/dev/null || true)"   # the top-up in place now
[ -n "$(find .lake/build/lib -name All.olean -path '*Tengoku/All.olean' 2>/dev/null | head -n 1)" ] && built=1

if [ "${1:-}" = "--check" ]; then
  git checkout -q -- scripts/cache.sh scripts/topup.py 2>/dev/null || true
  if [ "$latest" = "$head" ] && [ -n "$built" ]; then echo "current $latest"; exit 0; fi
  echo "newer $latest"; exit 3
fi
if [ "$latest" = "$head" ] && [ -n "$built" ] && [ "${TENGOKU_FORCE:-0}" != "1" ]; then
  git checkout -q -- scripts/cache.sh scripts/topup.py 2>/dev/null || true
  echo "already pinned to $latest (build present)"; exit 0
fi

echo "pinning the tree to $tag (commit $latest, was ${head:0:12})"
git checkout -q -f "$latest"
newest_scripts
scripts/cache.sh get
# Verify the replay WITHOUT letting Lake compile anything: if the cache did not
# cover the tree exactly, this fails loudly instead of building.
if ! lake build Tengoku.All --no-build; then
  [ "$TENGOKU_TOPUPS" = 1 ] || exit 1
  # 1. Back to the state we came from, when there was one: same commit, same top-up (kept on disk).
  if [ -n "$built" ]; then
    git checkout -q -f "$head"
    newest_scripts
    if { if [ -n "$was" ]; then scripts/cache.sh topup-reapply "$was"; else scripts/cache.sh topup-rollback; fi; } >/dev/null 2>&1 \
       && lake build Tengoku.All --no-build >/dev/null 2>&1; then
      newest_scripts scripts/pin.sh
      echo "kept ${head:0:12}: the build for $latest did not replay"; exit 4
    fi
  fi
  # 2. The nightly cache on its own commit.
  base="$(TENGOKU_TOPUPS=0 scripts/cache.sh latest)"
  echo "the top-up did not replay on $latest; taking it off and going back to the nightly cache at $base" >&2
  scripts/cache.sh topup-rollback
  git checkout -q -f "$base"
  newest_scripts
  TENGOKU_TOPUPS=0 scripts/cache.sh get
  lake build Tengoku.All --no-build
  latest="$base"
fi
[ "$TENGOKU_TOPUPS" != 1 ] || scripts/cache.sh topup-prune "$(python3 scripts/topup.py status 2>/dev/null | python3 -c 'import json,sys; print(json.load(sys.stdin).get("tip") or "none")' 2>/dev/null || echo none)"
echo "pinned to $latest"
# The pinned commit may predate these helper scripts: keep the newest copies
# from main so the next run (and the services' /refresh) can find them. Done
# last, in one compound command, so bash never reads past it.
{ newest_scripts scripts/pin.sh; exit 0; }
