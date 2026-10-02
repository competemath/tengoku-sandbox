# Questions people ask (draft)

Short, honest answers, with the longer ones one click away.

**What is Tengoku, in one sentence?**
A Lean 4 library of formal mathematics from many projects, ported onto one Lean version and machine-checked, with every theorem's source, licence and credit kept. ([README](readme-draft.md))

**Why not just use Mathlib?**
Use it: Tengoku contains it. Mathlib is the curated centre, reviewed line by line. Tengoku adds the projects around it that Mathlib does not hold, which each work with their own Lean version, and checks them by machine instead of by review. ([comparison](comparison-draft.md))

**What does "translated" mean, and can I trust a translation?**
A project written for one Lean version is rewritten to compile on Tengoku's, by an automated pipeline that is partly driven by an AI agent. Each translation is checked twice (it compiles with no errors, warnings or `sorry`; and the kernel accepts the translated statement as implying the original). That shows the translation proves what the original proved, not that it means the same: each theorem keeps a link to its original for that reason. ([trust](trust-draft.md))

**What is the difference between tentative, staging and trusted?**
Tentative: a real proof from a real source, searchable, not yet translated or checked here. Staging: translated and accepted by the translation checks, not yet built into the library. Trusted: built into the library and checked. ([trust](trust-draft.md), [coverage](coverage-draft.md))

**Does "trusted" mean a theorem is correct, or means what its source says?**
It means Lean's kernel accepted the proof of exactly that Lean statement, with no `sorry`, only the three standard axioms, and its assumptions searched for inconsistency. It does not mean the statement says what its source says, or that a person reviewed it; benchmarks have the same gap. ([trust](trust-draft.md#what-trusted-does-not-mean))

**Is it AI-generated?**
The theorems are not: they come from people's projects. The translation pipeline is partly AI-driven, and contributions may be made with AI help, which a permanent `Author:` line names. What decides whether anything is trusted is deterministic: the checks, not the AI.

**Can I train a model on the data?**
Legally, yes: the dataset is Apache-2.0 and every record keeps its upstream licence. Practically, read the [data card](data-draft.md) first: 95% of v1.0.0 is Mathlib at one commit, it includes Mathlib's IMO and Wiedijk-100 files, and it has known problems (262 records that should not be labelled trusted; names cut at a subscript).

**How do I get my project added, corrected, or removed?**
Open an issue on the repository. Registered projects are listed with their licences in `schemas/sources.json`; copyleft licences are not accepted; the originals stay canonical, so please cite your project, not Tengoku. ([for authors](readme-draft.md))

**How do I cite it?**
The release by its DOI, [10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400) (it resolves to the newest version, and each release has its own). For a result, cite the project it came from.

**What are Leak, Emissary-Archangel and CompeteMath?**
Three separate projects by the same developer. [Leak](https://competemath.com/about/leak) is the set of search, verification and proof-state services (and the prover agents) that run over Tengoku. [Emissary-Archangel](https://github.com/competemath/emissary-archangel) is the pipeline that translates projects onto Tengoku's Lean version. [CompeteMath](https://competemath.com) is a weekly mathematics competition site that uses Leak to check problems and answers.

**Is it free, and will it stay free?**
The library, its data and its checks are open under Apache-2.0, and there is no plan to charge for them. The Leak provers and CompeteMath are separate projects.

**Why one developer, and what if you stop?**
Because it was built that way; it is why the checks are automatic and public, and why the project says plainly what is not done. The library, the data and the checks are in the open repository, the services' code is public, and every release is archived with a DOI, so a fork can keep running the same checks. ([vision](vision-draft.md#if-the-maintainer-stops))

**How is it different from Loogle, Moogle and LeanSearch?**
Those search Mathlib. Tengoku's search is built on Loogle and Moogle and runs over the whole library, with the tier of each result.

**What does the name mean?**
天国 (Tengoku) is Japanese for "heaven".

**Why a release candidate of Lean?**
The library pins one Lean version at a time, and today that is `v4.34.0-rc2`. Which version, and why, is explained on [competemath.com/about/tengoku](https://competemath.com/about/tengoku); moving the library to each new release is one of the aims in the [vision](vision-draft.md).
