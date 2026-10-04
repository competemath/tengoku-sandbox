# Top-ups: following main merge by merge

The nightly build publishes one big cache of the compiled library (several GB).
That is enough for a person who clones the tree once a day. It is not enough
for the proof services, which must know about a theorem minutes after it is
merged, cannot compile anything themselves, and cannot download several GB
every few minutes.

So every merge also publishes a **top-up**: the compiled files that differ
from the nightly cache at that commit, and nothing else. For a promotion that
is a handful of files and a few hundred KB. A service that already holds the
nightly cache fetches the top-up, lays it over the cache, and is on main's tip
without compiling and without re-downloading the cache.

## The rule

1. **A merge waits for its top-up.** The merge queue builds the library exactly
   as main will have it, packs the difference, signs it and uploads it. Only
   then does the required check turn green.
2. **No top-up, no merge.** If the upload fails, the check fails and the PR
   leaves the queue with a comment saying it was not the author's fault. The
   PRs behind it are rebuilt without it, as for any other ejection.
3. **A top-up is followed only once its commit is on main.** Uploading does not
   make a top-up visible. `topup-promote.yml` runs on every push to main and
   writes the top-up of the newest commit *that is on main* into
   `cache-latest.json`, the one file the services read. A group that was built
   but never merged (a PR ahead of it failed, so GitHub rebuilt the group)
   leaves an orphan that nobody is ever pointed at.
4. **Orphans are collected.** The same workflow deletes top-ups whose commit
   never reached main and ones a newer top-up replaced, after a two-hour grace
   (longer than any group can stay in the queue).

## Where it happens

`.github/workflows/queue-gate.yml` has two jobs:

| job | token | what it does |
| --- | --- | --- |
| `queue-build` | read-only | everything the queue did before (candidates, axioms, regeneration diff), then restores the tree to the group's commit, runs `lake build Tengoku.All`, and packs the files that differ from the nightly cache |
| `queue-gate` | `contents`, `attestations`, `id-token`, `pull-requests`: write | the required check: downloads what `queue-build` packed, attests it, uploads it to the `cache-topups` release, and is green only when the build passed and the upload succeeded. It runs no code from the group. |

The job that runs the group's Lean code never holds a write token; the job
that holds one never runs the group's code.

`scripts/topup.py` makes and applies top-ups; `scripts/cache.sh` has the
commands around it (`topup-make`, `topup-put`, `topup-promote`, `topup-gc`,
`topup-rollback`, `topup-reapply`, `topup-prune`).

## What is inside one

`topup-<commit>.tar.zst` holds files under `.lake/build/lib/lean/Tengoku…` and
`.lake/build/ir/Tengoku…` only: never a candidate module, never a tool binary.
`topup-<commit>.json` lists them with the archive's SHA-256, the nightly cache
it was built over and that cache's commit.

A top-up is **cumulative**: it holds every file that differs from the nightly
cache, not only what the last merge changed. So a service needs exactly one
top-up (the newest), in any order, and a top-up built over yesterday's cache
is still right over today's (it is a superset of what is needed). The queue
itself starts from the nightly cache plus the newest promoted top-up, so each
group compiles only what is new since the previous merge.

## Following top-ups

```bash
TENGOKU_TOPUPS=1 scripts/pin.sh
```

Without the variable nothing changes: `pin.sh` pins to the nightly cache as
before. With it, `pin.sh`:

1. reads `cache-latest.json` (a plain download, no API call);
2. checks out the top-up's commit;
3. downloads the nightly cache only if it is not already unpacked;
4. fetches the top-up, checks it against the digest in `cache-latest.json` and
   (with `gh` present) against its build attestation, and lays it over the cache;
5. replays `lake build Tengoku.All --no-build`. Nothing is ever compiled.

If the replay fails, `pin.sh` puts back the state it came from (same commit,
same top-up, kept on disk) and exits **4**: nothing changed, keep serving. If
that is impossible it removes the top-up and pins to the nightly cache's own
commit. It never leaves a half-right build.

Every file a top-up touches is replaced by a rename, never written in place.
A running Lean process that has the old file mapped keeps it; a process
started afterwards sees the new one. The services rely on this to stay up
during a refresh.

## When the nightly cache rolls over

The nightly build publishes a new cache for the commit it built. If the
promoted top-up belongs to a commit *ahead* of that one (merges landed during
the build), it is kept in `cache-latest.json`, because it is still exactly
right on top of the new cache. Otherwise it is dropped: the cache alone is
newer.

## A change too big for the queue

The library build inside the queue has a 20-minute budget. A change to a core
module that rebuilds more than that still merges, but its top-up is marked
*incomplete* (`topup-<commit>.incomplete`). The services stay on the last
complete top-up, and `topup-promote.yml` starts a cache build as soon as the
commit is on main. Promotions and new records never come near the budget.

## The services

`topup-promote.yml` then asks each service named in the repository variable
`TENGOKU_SPACES` to refresh (`POST /refresh`). Requests are folded, never
dropped: however many merges land, a service runs one refresh at a time and
always ends on the newest published state.

| service | during a refresh |
| --- | --- |
| Leak IV (verifier) | a verification waits behind the refresh, then runs; none fails |
| Leak I (search) | the new index is loaded beside the old one, which keeps answering; they are swapped when the new one answers |
| Leak II (proof states) | a worker with live proofs is retired, not restarted: it finishes its proofs on the library they started with while a fresh worker takes new proofs |

Leak II's choice has a price: while proofs are live it refreshes at most once per
drain (`TENGOKU_DRAIN_MAX`, 45 minutes), so under constant use it can trail main by
that long while the verifier trails by two or three minutes.

## If main itself does not build

The whole-library build is part of the queue, so a main that does not build would
fail every group behind it. A group that changes no Lean file under `Tengoku/`
cannot be the cause: it still merges, marked incomplete, with an error annotation
naming the first error, and the cache build that follows fails loudly. A group that
does change Lean files is held responsible and leaves the queue.

## How this was tested

On `competemath/tengoku-sandbox`, 2026-09-19, with the three real Leak services
pointed at the sandbox and called every 30 seconds for about four hours
(1,475 calls in the first phase, 900+ in the second) while the scenarios ran:

| scenario | result |
| --- | --- |
| content merge | waited for its (empty, 22-byte) top-up; the pointer named it |
| promotion | 24 files, 1.2 MB; verifier on the commit 3 minutes after the merge, proof-state service 2, search 6; a proof using the new lemma verified |
| publish made to fail for one PR, another queued behind | that PR ejected with the "not your change" comment; the one behind merged; the top-up of the group that had contained the ejected PR was never named by the pointer, and was collected; the PR merged on re-queue |
| clean, broken, clean | the broken one ejected with file and line; both clean ones merged with top-ups |
| four at once | all merged, each with its top-up |
| second promotion | merge to a verified proof using the new lemma: 2 minutes 20 seconds, nothing compiled |
| nightly cache rebuilt while a merge landed | that merge's top-up (built over the old cache) stayed in the pointer; all three services re-based onto the new cache and applied it |
| promoted top-up replaced by random bytes | refused by digest; the services returned to the state they came from (exit 4), restarted nothing, failed no call, and advanced within 8 minutes of the genuine file returning |
| a merge promoted while the nightly was still building | the nightly published its new cache AFTER that promotion and kept the top-up that was ahead of it (first attempt found `put` reading the wrong repository's pointer; fixed, re-run passed) |
| main made to look broken | a content merge landed marked incomplete, the pointer did not move, a cache build started by itself and published 6 minutes later; a promotion was ejected with a located error |
| pointer sampled every 20 s throughout | never named a commit that was not on main |

Merge-group checks took a median of 3.5 minutes (maximum 8) over 37 runs.

The soak also found four faults, fixed and re-tested under the same traffic: a race
in the verifier's refresh (three failed verifications, none after the fix), a cold
start that loaded the tree while it was being unpacked, an "already unpacked" check
fooled by a service image that trims the cache, and services asked to refresh
seconds before the new pointer was visible to them. `scripts/tests/test_topup.py`
(8 tests) and `scripts/tests/test_pin.py` (7 tests, `pin.sh` driven with shims)
cover the scripts; the scenario scripts and the traffic generator are in the site
repository under `tests/tengoku-security/topups/`.
