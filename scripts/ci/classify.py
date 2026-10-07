#!/usr/bin/env python3
"""classify.py <base> <head> — one purpose per PR.
Assigns the PR a class from the paths it touches: content, tombstone, tooling,
docs. `docs` may ride along with any other class. Two other classes, or any
derived file (generated modules, stats, cache pointer) → fail."""

from __future__ import annotations

import os
import re
import sys

from _git import changed_files, fail, gh_output, pascal, run, tier_of
from native_check import is_native
from restructure_check import is_restructure
from tag_check import is_tag

base, head = sys.argv[1], sys.argv[2]
files = changed_files(base, head)
if not files:
    fail("empty diff")
# An INTAKE PR is a factory bundle (competemath/emissary-archangel scripts/bump): the Lean modules of ONE library, cut down to what the
# factory verified, with a manifest. The library is named by its manifest in the same diff, and its modules are then that PR's own
# (a library that is not in the tree yet has no data/*.jsonl for `derived_prefixes` to learn it from).
intake_libs = {m.group(1) for _, p in files if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))}


def tier(p: str) -> str:
    for lib in intake_libs:
        ns = pascal(lib)
        if p == f"Tengoku/{ns}.lean" or p.startswith(f"Tengoku/{ns}/") or p.startswith(f"data/intake/{lib}/"):
            return "intake"
    if intake_libs and p == "Tengoku/All.lean":
        return "intake"
    return tier_of(p)


# A TAG PR writes isnad tags into modules that are already in the tree and changes nothing else (scripts/ci/tag_check.py judges it: after the tags are taken out, code and
# docstring words are the base's). Asked before the scope-fix shape, which is also "existing modules modified in place", because only the content tells them apart.
if is_tag(base, head):
    bot_ = os.environ.get("TENGOKU_BOT", "tengoku-bot")
    if not (os.environ.get("PR_ACTOR", "") == bot_ or os.environ.get("TENGOKU_ACTOR_CHECKED") == "1"):
        fail(f"a tag PR comes from the factory's account ({bot_}), not from {os.environ.get('PR_ACTOR') or 'nobody'}")
    print(f"class=tag ({len(files)} modules)")
    gh_output("class", "tag")
    gh_output("files", " ".join(p for _, p in files))
    sys.exit(0)
# A NATIVE PR adds or edits modules of Tengoku/Native/ (novel content: scripts/ci/native_check.py judges it) and nothing else.
if is_native(base, head):
    bot_ = os.environ.get("TENGOKU_BOT", "tengoku-bot")
    if not (os.environ.get("PR_ACTOR", "") == bot_ or os.environ.get("TENGOKU_ACTOR_CHECKED") == "1"):
        fail(f"a native PR comes from the factory's account ({bot_}), not from {os.environ.get('PR_ACTOR') or 'nobody'}")
    print(f"class=native ({len(files)} files)")
    gh_output("class", "native")
    gh_output("files", " ".join(p for _, p in files))
    sys.exit(0)
# A SCOPE-FIX PR makes what a merged intake library registered for the whole tree local to its modules (scripts/ci/scope_fix_check.py judges the
# diff line by line): existing modules `Tengoku/<Library>/….lean` of a library that arrived as an intake bundle, modified in place, nothing else.
intake_at_base = {
    pascal(m.group(1))
    for p in run("ls-tree", "-r", "--name-only", base, "data/intake").split("\n")
    if (m := re.fullmatch(r"data/intake/([^/]+)/manifest\.jsonl", p))
}
if files and all(st == "M" and (m := re.fullmatch(r"Tengoku/([^/]+)/.+\.lean", p)) and m.group(1) in intake_at_base for st, p in files):
    bot_ = os.environ.get("TENGOKU_BOT", "tengoku-bot")
    if not (os.environ.get("PR_ACTOR", "") == bot_ or os.environ.get("TENGOKU_ACTOR_CHECKED") == "1"):
        fail(f"a scope-fix PR comes from the factory's account ({bot_}), not from {os.environ.get('PR_ACTOR') or 'nobody'}")
    print(f"class=scope-fix ({len(files)} modules)")
    gh_output("class", "scope-fix")
    gh_output("files", " ".join(p for _, p in files))
    sys.exit(0)
# A RESTRUCTURE PR moves the seed into Tengoku/Seed/ (scripts/restructure.py). scripts/ci/restructure_check.py recomputes it from the base commit and
# accepts only exactly that, so the PR may touch what the script owns although derived and tooling paths are mixed in it.
if is_restructure(base, head):
    bot_ = os.environ.get("TENGOKU_BOT", "tengoku-bot")
    if not (os.environ.get("PR_ACTOR", "") == bot_ or os.environ.get("TENGOKU_ACTOR_CHECKED") == "1"):
        fail(f"a restructure PR comes from the factory's account ({bot_}), not from {os.environ.get('PR_ACTOR') or 'nobody'}")
    print(f"class=restructure ({len(files)} files)")
    gh_output("class", "restructure")
    sys.exit(0)
by = {}
for st, p in files:
    by.setdefault(tier(p), []).append(p)
derived = by.get("derived")
bot = os.environ.get("TENGOKU_BOT", "tengoku-bot")
actor = os.environ.get("PR_ACTOR", "")
# On a merge group there is no pull-request actor; the queue only holds PRs whose own gate already checked it.
actor_ok = actor == bot or os.environ.get("TENGOKU_ACTOR_CHECKED") == "1"
# The promote bot's PRs move staging records to trusted and regenerate modules: derived + content + tombstone paths, nothing else.
if set(by) <= {"derived", "content", "tombstone"} and (derived or by.get("tombstone")) and actor_ok:
    print(f"class=promotion ({len(files)} files, by {actor or 'the merge group'})")
    gh_output("class", "promotion")
    gh_output("files", " ".join(p for _, p in files))
    sys.exit(0)
if "intake" in by:
    others = [c for c in by if c not in ("intake", "docs")]
    if others or len(intake_libs) != 1:
        fail(f"an intake PR is one library's bundle and nothing else (libraries: {sorted(intake_libs)}; also touches: {others})")
    if not actor_ok:
        fail(f"an intake PR comes from the factory's account ({bot}), not from {actor or 'nobody'}")
    # the next part of a library that arrived in parts (scripts/bump/bundle_layers.py in the factory): the part's report is a new file data/intake/<library>/parts/NNN.json
    lib = sorted(intake_libs)[0]
    cls = "extend" if any(re.fullmatch(rf"data/intake/{re.escape(lib)}/parts/\d{{3}}\.json", p) for _, p in files) else "intake"
    print(f"class={cls} ({len(files)} files, library {lib})")
    gh_output("class", cls)
    gh_output("files", " ".join(p for _, p in files))
    sys.exit(0)
if derived:
    fail("derived files are regenerated by the promote bot, never edited in a PR: " + ", ".join(derived[:5]))
classes = [c for c in by if c != "docs"] or ["docs"]
if len(classes) > 1:
    detail = "; ".join(f"{c}: {', '.join(by[c][:3])}" for c in classes)
    fail(f"multi-purpose PR ({' + '.join(classes)}). One purpose per PR. {detail}")
cls = classes[0]
print(f"class={cls} ({len(files)} files)")
gh_output("class", cls)
gh_output("files", " ".join(p for _, p in files))
