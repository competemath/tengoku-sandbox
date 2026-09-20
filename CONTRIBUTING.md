# Contributing to Tengoku

**One purpose per PR.** The first check reads which paths you touched and
assigns one class: content, tombstone, tooling, docs. Two classes fail.

**One file per PR.** Put your records in a new file
`data/staging/<library>/<anything>.jsonl`, one JSON object per line
(`schemas/record.schema.json`); two PRs appending to one file cannot both sit
in the merge queue. Every record of a library that has a corpus
(`schemas/sources.json`) needs `source_path` and `context`, or it is never
compiled. Data files are append-only, byte for byte. To retract, append a
tombstone line to `data/trusted/<library>.jsonl`:
`{"tombstone": "<name>", "reason": "…", "by": "<you>", "at": "<ISO date>"}`.
Generated modules under `Tengoku/<Library>/` are never edited by hand; the
promote bot regenerates them when it moves records to trusted.

**Build locally first.** The PR checks run no Lean. The merge queue does:
```
scripts/cache.sh get            # newest published cache, nothing compiles
git clone --filter=blob:none <corpus repo> corpora/<library>   # repo + commit in schemas/sources.json
python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
  --candidate <source_path> --candidate-names <your record names, comma-separated>
lake build Tengoku.<Library>.<Path>._candidate_<File>
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

## Original theorems: the blind re-proof test

If your records are not translations of an existing library, the PR must show that at least one of
its headline theorems (you name up to ten) resists a blind 5-minute re-proof attempt against the
library as it is without your PR. Run it before you open the PR — it uses the `claude` CLI on your
own subscription and the library's hosted services:

```bash
python3 scripts/assess/run.py data/staging/<library>/<your-file>.jsonl --headlines Name.one,Name.two
git add claims/ && git commit -s -m "blind re-proof claim"
```

If every headline is re-proved the PR is rejected; the runner tells you so before you push. Never edit
the files it writes: the gate recomputes everything from the raw transcript. See [docs/assess.md](docs/assess.md).
