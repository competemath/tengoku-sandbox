# Tengoku: what it is, what it checks, how to use it

## What it is

Tengoku is one Lean 4 library assembled from many formal mathematics projects. It starts from Mathlib and its
dependencies, and adds registered sources, translated onto a single pinned toolchain
(`leanprover/lean4:v4.34.0-rc2` at the time of writing) so that they build together and import together.

Tengoku has `trusted`, `tentative` and `staging` tiers. The current counts are shown by the badge in the README;
they are not repeated here so that this page does not become a second source of truth.

## What it checks

Each check is enforced by code in this repository, named below.

**A theorem promoted to the trusted tier has passed the library's checks.** Promotion
([scripts/promote.py](../scripts/promote.py)) builds the relevant module from scratch against the compiled library.
The merge queue ([queue-gate.yml](../.github/workflows/queue-gate.yml)) also checks that the named declarations use no
`sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`. The trusted records that are not built into
the current library are not described by this claim.

**A trusted theorem is not vacuous.** Its assumptions are checked for contradiction
([tools/vacuity](../tools/vacuity)), at the pull request and again before promotion. A theorem whose assumptions
cannot all hold is refused unless a person acknowledges it in the pull request.

**Every record carries its provenance.** Each record names its source file at a fixed commit (`source_url`), and
its licence follows from the registry ([schemas/sources.json](../schemas/sources.json)). A contributed theorem
carries an `Author:` line naming the human and any AI system used; no change may remove or alter it
([scripts/ci/credits.py](../scripts/ci/credits.py)).

**Nothing is deleted.** The data files are append-only ([scripts/ci/append_only.py](../scripts/ci/append_only.py)).
A mistake is retracted by a tombstone with a fixed category (duplicate, incorrect, superseded, licence, other) and a
note on where to look instead, which is updated as the library changes. Credit changes only on evidence of plagiarism, recorded with that evidence.

**Builds are attested.** The compiled library is published as releases carrying build provenance
([build.yml](../.github/workflows/build.yml)), and each release published since October 2026 also carries it as a file
(`*.intoto.jsonl`); anyone can verify a download with `gh attestation verify`. A second, independent kernel,
[nanoda](https://github.com/ammkrn/nanoda_lib), re-checks every declaration of the compiled library daily
([independent-check.yml](../.github/workflows/independent-check.yml)).

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

- **From an agent, through [Leak](https://competemath.com/about/leak), the intended interface.** Leak is the
  MCP tooling and harness for agent-driven proving: its services provide search, proof-state interaction and
  verification over MCP. Any MCP-capable system can use it; Leak is not the prover.
- **On the web.** [competemath.com/tengoku](https://competemath.com/tengoku).
- **Over HTTP.** [docs/api.md](api.md).
- **Build against it.** `scripts/cache.sh get` downloads the compiled library; `import Tengoku.All` imports
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
[10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400) (it resolves to the newest version; each release
also has its own DOI, on its release page). GitHub's *Cite this repository* button gives the same reference, from
[CITATION.cff](../CITATION.cff).

```bibtex
@misc{tengoku,
  author       = {{Tengoku contributors} and Bashir, Mikael},
  title        = {Tengoku: one verified Lean 4 tree of formal mathematics, with provenance},
  publisher    = {Zenodo},
  year         = {2026},
  doi          = {10.5281/zenodo.23050400},
  url          = {https://doi.org/10.5281/zenodo.23050400}
}
```

## Limits

Just because a theorem has passed Tengoku's checks, it doesn't mean it is trusted by a mathematician. Please make use of
Tengoku responsibly, being vigilant with theorems that don't say what they look like they should.
