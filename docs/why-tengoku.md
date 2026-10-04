# Tengoku: what it is, what it guarantees, how to use it

## What it is

Tengoku is one Lean 4 library assembled from many formal mathematics projects. It starts from Mathlib and its
dependencies, and adds registered libraries, translated onto a single pinned toolchain
(`leanprover/lean4:v4.34.0-rc2` at the time of writing) so that they build together and import together.

At the time of writing, 198,172 theorems are trusted: 188,989 from Mathlib and its dependencies, 8,921 from
Equational Theories and 262 of CompeteMath's own. A further 5,404 theorems, translated from 45 research libraries
(Carleson, PrimeNumberTheoremAnd, Brownian motion, the IMO Shortlist and others), are in staging on their way to
trusted. 106 libraries are registered, and a pipeline keeps translating them.

## What it guarantees

Each guarantee is enforced by code in this repository, named below.

**A trusted theorem is machine-checked against the whole library.** A record reaches `data/trusted/` only after
promotion ([scripts/promote.py](../scripts/promote.py)) has built its module from scratch against the compiled
tree. The merge queue ([queue-gate.yml](../.github/workflows/queue-gate.yml)) had already built it and checked that
every named declaration of the new modules uses no `sorry` and no axiom beyond `propext`, `Classical.choice` and
`Quot.sound`.

**A trusted theorem is not vacuous.** Its assumptions are checked for contradiction
([tools/vacuity](../tools/vacuity)), at the pull request and again before promotion. A theorem whose assumptions
cannot all hold is refused unless a person acknowledges it in the pull request.

**Every theorem carries its provenance.** Each record names its source file at a fixed commit (`source_url`), and
its licence follows from the registry ([schemas/sources.json](../schemas/sources.json)). A contributed theorem
carries an `Author:` line naming the human and any AI system used; no change may remove or alter it
([scripts/ci/credits.py](../scripts/ci/credits.py)).

**Nothing is deleted.** The data files are append-only ([scripts/ci/append_only.py](../scripts/ci/append_only.py)).
A mistake is retracted by a tombstone with a fixed category (duplicate, incorrect, superseded, licence, other) and a
note on where to look instead, which is updated as the library changes. Credit changes only on evidence of
plagiarism, recorded with that evidence.

**Builds are attested.** The compiled library is published as releases carrying build provenance
([build.yml](../.github/workflows/build.yml)), and each release published since October 2026 also carries it as a file
(`*.intoto.jsonl`); anyone can verify a download with `gh attestation verify`. An
independent re-check of every declaration with a second kernel is in progress (competemath/tengoku#64).

## Where it fits

- **Mathlib** is a curated library with human review of every contribution. Tengoku builds on Mathlib and does not
  replace it: it adds material Mathlib does not hold (research projects, competition solutions, applied libraries),
  checked by machine rather than reviewed line by line.
- **Other formal libraries** each pin their own toolchain and dependencies, so combining them is costly. Tengoku
  translates them onto one toolchain and one dependency set, keeping a link to every original.
- **AI-generated proofs** enter through the same gates as any other contribution, with the AI named in the credit.
  The vacuity check guards against a class of theorems automated provers are prone to produce: ones whose
  assumptions contradict each other.

## How to use it

- **Search.** At [competemath.com/tengoku](https://competemath.com/tengoku); over HTTP
  ([docs/api.md](api.md)); or from an agent through Leak I, a free MCP service
  (`https://barkingtree-leak-i.hf.space/sse`, no authentication).
- **Build against it.** `scripts/cache.sh get` downloads the verified compiled tree; `import Tengoku.All` imports
  everything.
- **Take the dataset.** Numbered releases `vX.Y.Z`, one for each month with changes, each with a DOI from Zenodo
  ([all versions](https://doi.org/10.5281/zenodo.23050400)): every trusted theorem with its statement, proof,
  source, licence and credit, and a manifest naming the commit, the toolchain, the counts and the dataset's
  checksum, all with build provenance. A new toolchain is a new major version, added theorems a minor one,
  corrections a patch.
- **Contribute.** [How a theorem gets into Tengoku](how-a-pr-flows.md). Open goals are listed in
  [GOALS.md](../GOALS.md).

## How to cite

Cite the version you used (its tag, or its DOI) and the commit its manifest names. The all-versions DOI is
[10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400); [CITATION.cff](../CITATION.cff) and the
README's *How to cite* give the reference and a BibTeX entry.

## Limits

- **Trusted means machine-checked, not reviewed by a mathematician.** A statement means what its definitions say.
  Definitions come from the source libraries, and a translated statement is the original's.
- **Coverage is partial.** Most registered libraries are still being translated.
- **Only the trusted tier is checked.** Records in `data/tentative/` and `data/staging/` are not yet trusted.
