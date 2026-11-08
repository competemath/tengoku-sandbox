# Contributing to Tengoku as an agent

You can add theorems to this repository on your own: read this file, then act.
Everything lands through a pull request that automated checks gate, and a
maintainer approves each one before it merges.

## What this repository is

One self-contained Lean 4 library on `leanprover/lean4:v4.34.0-rc2` (see
`lean-toolchain`), seeded from Mathlib. `data/trusted/*.jsonl` are theorems the
tree compiles; `data/staging/<library>/*.jsonl` are verified translations waiting
to be built in; `data/tentative/*.jsonl` are real proofs harvested from other
libraries, not yet re-verified here. A record is one JSON object per line
(`schemas/record.schema.json`). `README.md` is the quick start and
`CONTRIBUTING.md` the human version of this page.

## Set up (once)

```bash
git clone https://github.com/competemath/tengoku && cd tengoku
scripts/cache.sh get        # the compiled tree; never build it from scratch
pipx install pre-commit && pre-commit install
```

Set `git config user.name` and `user.email` to the human you act for. Every
commit needs their sign-off (`git commit -s`), and the tree records who added
what; a PR from an account with no identifiable owner is not merged.

## Add theorems (the common case)

1. Write records into a **new** file `data/staging/<library>/<anything>.jsonl`,
   one JSON object per line: `name`, `statement`, `proof`, `status`
   (`"staging"`), `library`, `source_url`, `toolchain`; for a library with a
   corpus in `schemas/sources.json` also `source_path` and `context`. One file
   per PR.
2. Put the credit as a docstring at the top of `statement`:
   ```lean
   /-- One sentence on what it says.

   Author: Full Name (https://github.com/handle), with <AI system>. -/
   theorem ...
   ```
   `Author:` is the word the checks key on; nobody can remove that line later.
   For a whole project, `tools/attribute/attribute.py <dir> --credit "Author: …"`
   writes it into every declaration.
3. Check it builds before pushing (compiles only your records):
   ```bash
   git clone --filter=blob:none <corpus repo> corpora/<library>   # repo + commit in schemas/sources.json
   python3 scripts/generate.py --corpus corpora/<library> --libraries <library> \
     --candidate <source_path> --candidate-names <your record names, comma-separated>
   lake build Tengoku.<Library>.<Path>._candidate_<File>
   ```
4. Optional: mark up to ten of your records as headline theorems (`"headline": true`); each must credit its
   author with an `Author:` line in its docstring.
5. `git commit -s`, push, open the PR, and turn on *Merge when ready*
   (`gh pr merge --squash --auto`). The gate comments on the PR with anything it
   found; fix and push, the comment updates.

## Harvest a library into tentative

```bash
python3 tools/harvest.py --repo <git url> --library <name> --toolchain <its lean-toolchain> \
  --out data/tentative/<name>.jsonl
```
The source must first be registered in `schemas/sources.json` (its URL prefix
under `allowed`, its licence, and a `corpora` entry with repo, commit and module
roots) in a separate tooling PR; records come in a second PR. Files over 40 MB:
`tools/split_jsonl.py`. Every record keeps `source_url` pointing at the exact
line in the source at its commit.

## Rules the gate enforces

- Records: required fields, a source on the allowlist, the statement declares
  the name, no duplicate name in the PR, no name already trusted.
- Content: no `sorry`, `axiom`, `native_decide`, `import`, macros, notation,
  or anything that runs code inside a record.
- Data files are append-only. Retract with a tombstone line, never a deletion.
- No authorship or provenance line is ever removed or changed.
- One purpose per PR: content, or tooling, or docs; docs may ride along.
- Signed-off commits. `Depends-On: #N` in the description if a PR needs another.

If a check fails, its comment on the PR names the step, quotes the error and
says what to do. A check you believe is wrong: use the *Report a gate bug* link
in that comment.

## Don't

- Don't edit `Tengoku/**` by hand (the promote bot generates it from records; an
  intake PR adds a library's verified bundle from the factory and extend PRs its
  later parts — docs/pr-classes.md) or `data/trusted/**` (promotion moves records
  there; only tombstones are added by hand).
- Don't touch `scripts/ci/` or workflows unless the change was proven in the
  sandbox (`scripts/ci/campaign/README.md`).
- Don't strip, rewrite or move anyone's credit.
