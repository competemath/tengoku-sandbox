# Questions people ask (draft)

**What is Tengoku?**
A Lean 4 library of formal mathematics from many projects, ported onto one Lean version and machine-checked, with every theorem's source, licence and credit kept. ([README](readme-draft.md))

**Why not just use Mathlib?**
Tengoku contains Mathlib. Mathlib is the curated centre, shaped for people writing proofs, so it renames and refactors as better statements are found. Provers are fragile to that. Tengoku keeps what was proved, leaves a note on retracted theorems saying how to prove the same idea, and adds the projects around Mathlib that run on their own Lean versions. ([comparison](comparison-draft.md), [vision](vision-draft.md#mathlib-and-tengoku))

**What does "translated" mean, and can I trust a translation?**
Partly. A project written for one Lean version is rewritten to compile on Tengoku's, by an automated pipeline that is partly driven by an AI agent. Each translation is checked twice: it compiles with no errors, warnings or `sorry`, and the kernel accepts the translated statement as implying the original (the entailment check). That shows the translation proves at least what the original proved, not that it means the same, so each theorem keeps a link to its original. The two hard parts are the entailment check, which fails whenever definitions differ in ways the kernel cannot see through, and self-containment, since a project's theorems depend on its own definitions, tactics, options, generated files and pinned dependencies, which all have to come along, be reconciled with Mathlib's names, and build together. ([why it is hard](vision-draft.md#why-translation-is-hard), [trust](trust-draft.md))

**What is the difference between tentative, staging and trusted?**
Tentative: a real proof from a real source, searchable, not yet translated or checked here. Staging: translated and accepted by the translation checks, not yet built into the library. Trusted: built into the library and checked. ([trust](trust-draft.md), [coverage](coverage-draft.md))

**Does "trusted" mean a theorem is correct, or means what its source says?**
It means Lean's kernel accepted the proof of exactly that Lean statement, with no `sorry`, only the three standard axioms, and, for promoted records, its assumptions searched for inconsistency, apart from the [known gaps](trust-draft.md#known-gaps). It does not mean the statement says what its source says, or that a person reviewed it; benchmarks have the same gap. ([trust](trust-draft.md#what-trusted-does-not-mean))

**Is it AI-generated?**
Most theorems come from people's projects. Some sources and contributions include AI-written proofs, and the translation pipeline is partly AI-driven; a contribution's `Author:` line names any AI used. What decides whether anything is trusted is deterministic: the checks, not the AI.

**Can I train a model on the data?**
The dataset is Apache-2.0 and every record keeps its upstream licence, with attribution terms; all 109 registered sources are permissively licensed (97 Apache-2.0, 10 MIT, 2 BSD-3-Clause), and copyleft sources are refused. Practically, read the [data card](data-draft.md) first: 95% of v1.0.0 is Mathlib at one commit, it includes Mathlib's IMO and Wiedijk-100 files, and it has known problems (262 records that should not be labelled trusted; names cut at a subscript).

**How do I get my project added, corrected, or removed?**
Open an issue or a pull request on the repository. Registered sources are listed with their licences in `schemas/sources.json`; copyleft licences are not accepted; the originals stay canonical, so please cite your project, not Tengoku. ([for authors](readme-draft.md))

**How do I cite it?**
The release by its DOI, [10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400) (it resolves to the newest version, and each release has its own). For a result, cite the project it came from.

**What are Leak, Emissary-Archangel and CompeteMath?**
Three separate projects, founded by the same independent developer and open to contributors. [Leak](https://competemath.com/about/leak) is the set of search, verification and proof-state services (and the prover agents) that run over Tengoku. [Emissary-Archangel](https://github.com/competemath/emissary-archangel) is the pipeline that translates projects onto Tengoku's Lean version. [CompeteMath](https://competemath.com) is a weekly mathematics competition site that uses Leak to check problems and answers.

**Is it free, and will it stay open?**
What stays fixed whoever runs the project: the library, its data and its checks are open under Apache-2.0 and every record keeps its upstream licence; releases already published stay open and archived with their DOIs; data files are append-only. ([vision](vision-draft.md#what-stays-fixed))

**Who runs it, and what if the founder steps away?**
Tengoku is a community-maintained project, founded by an independent developer. The library, the data and the checks are in the open repository, and every release is archived with a DOI, so a fork can keep running the same checks. ([vision](vision-draft.md#what-stays-fixed))

**How is it different from Loogle, Moogle and LeanSearch?**
Those search Mathlib. Tengoku's search is built on Loogle and Moogle and runs over the whole library, with the tier of each result.

**What does the name mean?**
天国 (Tengoku) is Japanese for "heaven".

**Why a release candidate of Lean?**
The library pins one Lean version at a time. When the tree was created, Mathlib's `master` was on `v4.34.0-rc2` and the largest live projects (FLT, Carleson, PFR) matched it, so the most theorems are reachable without translation ([why](https://competemath.com/about/tengoku)). Moving the library to each new release is one of the aims in the [vision](vision-draft.md).
