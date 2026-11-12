# What is in the compiled tree, and what the cache leaves out

The nightly cache is `.lake/build` of the whole tree, packed. On 2026-10-14 it unpacked to **102 GB** on a runner whose disk is 145 GB with about 20 GB used by the
image after the usual clean-up, and the merge queue failed every group with "No space left on device" (the isnad tag PR #555). Where the 102 GB were
(runner measurement, `cache-20261014T0523Z`):

| directory | size | what |
|---|---|---|
| `build/ir` | 80.6 GB | the C file of every module (1.4 GB in all) and **one `<Module>.setup.json` per module** (33,654 files, 1-2 MB each, the rest) |
| `build/lib` | 21.3 GB | `.olean`, `.ilean`, `.olean.private`, `.olean.server`, traces and hashes |

The same breakdown on the sandbox tree (19,476 modules): `.setup.json` 18.8 GB of 34 GB; `.olean.private` 7.5 GB; `.olean` 3.8 GB; `.c` 0.9 GB; `.ilean` 0.6 GB.

## `*.setup.json`

Lake writes it as the input of compiling a module (its header, imports and options) and never reads it for a module that is up to date. Measured on a seeded copy of the
sandbox tree (sandbox run 38533106714): deleting every one (19 of 34 GB)

- `lake build Tengoku.All --no-build` still passes (7 s),
- a normal `lake build Tengoku.All` compiles nothing (4 s) and writes none back.

So the cache leaves them out, and a module that must compile writes its own again:

- `scripts/cache.sh pack` does not pack them; `scripts/cache.sh unpack` (what `get` calls) does not write them, so a cache published before this change, which still holds them, costs no disk;
- `scripts/topup.py make` does not ship them; `apply` skips them in a top-up published before this change.

A seed is about 22 GB instead of 102, which also puts it back within what the Leak services' Spaces (50 GB of container disk) can hold.

## The budget

A hosted runner has one 150 GB disk (`/mnt` is a directory on it, not a second disk): about 125 GB free after the clean-up in the queue's *Free disk* step. The tree grows by
about 4 GB per 500 modules (with the setup files; about 1 GB without).
