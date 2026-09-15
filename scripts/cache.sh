#!/usr/bin/env bash
# Tengoku build cache — stored on the repository as GitHub Release assets, so
# nobody has to build the tree from scratch.
#
#   scripts/cache.sh get [<commit>]   # download + unpack the newest cache whose commit is an ancestor of HEAD (or <commit>)
#   scripts/cache.sh latest           # print the commit of the newest published cache (what scripts/pin.sh checks out)
#   scripts/cache.sh latest-tag       # print its tag, e.g. cache-20260915T0300Z
#   scripts/cache.sh put              # pack .lake/build and publish it for HEAD (needs `gh` logged in)
#
# A cache is a release tagged `cache-<UTC stamp>` (cache-20260915T0300Z); the
# commit it was built from is the first line of its notes (`commit=<sha>`).
# Older releases tagged `cache-<sha>` are still understood. `get` picks the
# newest cache whose commit is an ancestor of the wanted one — an older cache
# is a valid starting point, Lake rebuilds only what changed since. Assets are
# zstd tarballs split into <2GB parts (GitHub's limit). Reading needs no
# account: the repository is public (anonymous API + asset downloads); `gh`
# is used when it is installed and logged in.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO="${TENGOKU_REPO:-competemath/tengoku}"          # where `put` publishes
SRC="${TENGOKU_CACHE_SOURCE:-$REPO}"                  # where `get`/`latest` read (a sandbox reads the library's caches)
cmd="${1:-}"

need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1" >&2; exit 1; }; }
need zstd; need tar; need git; need python3

have_gh() { command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; }

api() {  # GET a GitHub API path, anonymously or with whatever token exists
  if have_gh; then gh api "$1"
  else need curl; curl -fsSL -H 'Accept: application/vnd.github+json' ${GH_TOKEN:+-H "Authorization: Bearer $GH_TOKEN"} "https://api.github.com/$1"; fi
}

# The newest cache, from the fixed-tag pointer the nightly updates (a plain
# download, no API call, no rate limit): "<published_at> 1 <tag> <commit>".
pointer() {
  need curl
  curl -fsSL "https://github.com/$SRC/releases/download/cache-latest/cache-latest.json" 2>/dev/null | python3 -c '
import json, sys
try: d = json.load(sys.stdin); print(d["published_at"], "1", d["tag"], d["commit"])
except Exception: pass' 2>/dev/null || true
}

# Every asset of a cache release must carry a build-provenance attestation from
# this repository's build workflow (docs/tengoku-security-plan.md §6). With gh
# present the check is enforced; without it a warning is printed for now.
verify_parts() {
  local dir="$1" mode="${TENGOKU_VERIFY:-warn}"   # warn until every published cache carries an attestation, then require
  if ! command -v gh >/dev/null 2>&1; then
    echo "warning: gh not installed, cache attestation not verified" >&2
    [ "$mode" = "require" ] && return 1 || return 0
  fi
  for f in "$dir"/tengoku-cache.tar.zst.part-*; do
    if ! gh attestation verify "$f" -R "$SRC" --signer-workflow "$SRC/.github/workflows/build.yml" >/dev/null 2>&1; then
      if [ "$mode" = "require" ]; then echo "REFUSED: $(basename "$f") has no valid build attestation from $SRC — not unpacking" >&2; return 1; fi
      echo "warning: $(basename "$f") has no build attestation (TENGOKU_VERIFY=warn)" >&2; return 0
    fi
  done
  echo "attestations verified"
}

# Every published cache, newest first: "<published_at> <stamped?> <tag> <commit>" per line.
list_caches() {
  local page=1 out
  while :; do
    out="$(api "repos/$SRC/releases?per_page=100&page=$page")"
    printf '%s' "$out" | python3 -c '
import json, re, sys
for r in json.load(sys.stdin):
    tag = r.get("tag_name", "")
    if not tag.startswith("cache-"): continue
    m = re.search(r"^commit=([0-9a-f]{40})", r.get("body") or "", re.M)
    commit = m.group(1) if m else (tag[6:] if re.fullmatch(r"cache-[0-9a-f]{40}", tag) else "")
    # GitHub sets created_at to the COMMIT date, so two caches of one
    # commit tie; order by publish time, and a timestamp tag beats a sha tag.
    when = r.get("published_at") or r.get("created_at")
    if commit: print(when, "1" if re.fullmatch(r"cache-[0-9]{8}T[0-9]{4}Z", tag) else "0", tag, commit)'
    printf '%s' "$out" | grep -q '"tag_name"' || break
    page=$((page + 1))
    [ "$page" -le 10 ] || break
  done | sort -r
}

# Download every part of one cache release into $2.
download_cache() {
  local tag="$1" dir="$2"
  if have_gh; then
    gh release download "$tag" -R "$SRC" -D "$dir" -p 'tengoku-cache.tar.zst.part-*'
  else
    need curl
    local urls
    urls="$(api "repos/$SRC/releases/tags/$tag" | python3 -c '
import json, sys
for a in json.load(sys.stdin).get("assets", []):
    if a["name"].startswith("tengoku-cache.tar.zst.part-"): print(a["browser_download_url"])')"
    [ -n "$urls" ] || { echo "no cache parts on $tag" >&2; exit 1; }
    for u in $urls; do
      echo "  $u"
      curl -fL --retry 3 -o "$dir/$(basename "$u")" "$u"
    done
  fi
}

case "$cmd" in
  put)
    need gh
    # Caches are packed by CI on Linux only. A macOS pack once broke the replay
    # for Linux consumers (case-insensitive filesystem, bsdtar); never again.
    if [ "$(uname -s)" = "Darwin" ] && [ "${TENGOKU_ALLOW_MAC_PUT:-0}" != "1" ]; then
      echo "refusing to pack a cache on macOS — let the nightly build (or workflow_dispatch) publish it" >&2; exit 1
    fi
    sha="$(git rev-parse HEAD)"
    stamp="${TENGOKU_CACHE_STAMP:-$(date -u +%Y%m%dT%H%MZ)}"
    tag="cache-$stamp"
    [ -d .lake/build ] || { echo "nothing to publish: .lake/build missing" >&2; exit 1; }
    tmp="$(mktemp -d)"
    echo "packing .lake/build for $sha as $tag …"
    tar -C .lake -cf - build | zstd -T0 -3 -q | split -b 1900m - "$tmp/tengoku-cache.tar.zst.part-"
    ls -la "$tmp"
    if gh release view "$tag" -R "$REPO" >/dev/null 2>&1; then
      gh release delete "$tag" -R "$REPO" --yes --cleanup-tag
    fi
    gh release create "$tag" -R "$REPO" --target "$sha" --title "build cache $(echo "$stamp" | sed -E 's/([0-9]{4})([0-9]{2})([0-9]{2})T([0-9]{2})([0-9]{2})Z/\1-\2-\3 \4:\5 UTC/')" \
      --notes "$(printf 'commit=%s\ntoolchain=%s\n\nCompiled .lake/build for %s. Fetch with scripts/cache.sh get, or pin a checkout to it with scripts/pin.sh.' "$sha" "$(cat lean-toolchain)" "$sha")" \
      "$tmp"/tengoku-cache.tar.zst.part-*
    echo "published $tag (commit $sha)"
    # Fixed-tag pointer to the newest cache, for consumers that must not call the API.
    printf '{"tag": "%s", "commit": "%s", "published_at": "%s", "parts": [%s]}\n' "$tag" "$sha" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      "$(for f in "$tmp"/tengoku-cache.tar.zst.part-*; do printf '{"name": "%s", "sha256": "%s"},' "$(basename "$f")" "$(sha256sum "$f" | cut -d' ' -f1)"; done | sed 's/,$//')" > "$tmp/cache-latest.json"
    gh release view cache-latest -R "$REPO" >/dev/null 2>&1 || gh release create cache-latest -R "$REPO" --title "newest cache (pointer)" --notes "cache-latest.json names the newest cache release. Updated by every publish." >/dev/null
    gh release upload cache-latest "$tmp/cache-latest.json" -R "$REPO" --clobber >/dev/null && echo "pointer cache-latest.json → $tag"
    rm -rf "$tmp"
    # Keep the newest KEEP caches; each is gigabytes and `get` only ever needs
    # a recent one (Lake rebuilds the difference).
    KEEP="${TENGOKU_CACHE_KEEP:-5}"
    list_caches | tail -n +"$((KEEP + 1))" | awk '{print $3}' \
      | while read -r old; do [ -n "$old" ] && gh release delete "$old" -R "$REPO" --yes --cleanup-tag && echo "pruned $old"; done || true
    ;;
  latest)
    commit="$(pointer | awk '{print $4}')"
    [ -n "$commit" ] || commit="$(list_caches | head -n 1 | awk '{print $4}')"
    [ -n "$commit" ] || { echo "no published cache" >&2; exit 1; }
    echo "$commit"
    ;;
  latest-tag)
    tag="$(pointer | awk '{print $3}')"
    [ -n "$tag" ] || tag="$(list_caches | head -n 1 | awk '{print $3}')"
    [ -n "$tag" ] || { echo "no published cache" >&2; exit 1; }
    echo "$tag"
    ;;
  get)
    want="$(git rev-parse "${2:-HEAD}")"
    tmp="$(mktemp -d)"
    found=""
    # Newest cache first; the first one whose commit is an ancestor of what we
    # want is the best starting point. (A shallow clone cannot answer
    # ancestry — clone with --filter=blob:none or enough depth.)
    while read -r _ _ tag commit; do
      if git merge-base --is-ancestor "$commit" "$want" 2>/dev/null; then found="$tag"; break; fi
    done < <(list_caches)
    [ -n "$found" ] || { echo "no published cache is an ancestor of $want (are the caches published? is this clone deep enough for ancestry?)" >&2; exit 1; }
    echo "fetching $found …"
    download_cache "$found" "$tmp"
    verify_parts "$tmp" || { rm -rf "$tmp"; exit 1; }
    mkdir -p .lake
    cat "$tmp"/tengoku-cache.tar.zst.part-* | zstd -d -q | tar -C .lake -xf -
    rm -rf "$tmp"
    echo "unpacked $found into .lake/build (Lake rebuilds only what differs from $want)"
    ;;
  *)
    echo "usage: $0 get [<commit>] | latest | latest-tag | put" >&2; exit 2 ;;
esac
