# Contributing to Tengoku

**One purpose per PR.** The first check reads which paths you touched and
assigns one class: content, tombstone, tooling, docs. Two classes fail.

**Add, don't edit.** Records go at the end of `data/staging/<library>.jsonl`,
one JSON object per line (`schemas/record.schema.json`). Data files are
append-only, byte for byte. To retract, append a tombstone line:
`{"tombstone": "<name>", "reason": "…", "by": "<you>", "at": "<ISO date>"}`.
Generated modules under `Tengoku/<Library>/` are never edited by hand.

**Build locally first.** The PR checks run no Lean. The merge queue does:
```
scripts/cache.sh get            # newest published cache, nothing compiles
python3 scripts/generate.py --candidate data/staging/<library>.jsonl
lake build Tengoku.<Library>._candidate_<file>
```
**Sign off.** `git commit -s` on every commit (Developer Certificate of Origin).

**Install the hooks.** `pipx install pre-commit && pre-commit install`. CI runs
the same `.pre-commit-config.yaml`, so what passes here passes there.

**What the queue does.** Seeds the nightly cache, builds only your modules,
checks axioms, regenerates derived files and diffs them. If it fails, the PR
leaves the queue and a comment names the file, line, source line, record and
what to do. Fix, push, re-queue.

**Depends on another PR?** Put `Depends-On: #123` in the description. Your PR
waits until #123 is merged or queued ahead of it.
