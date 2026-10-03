<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Formal mathematics from many Lean projects, translated onto one Lean version and machine-checked.</b><br>
Today: Mathlib and Equational Theories; more on the way. Search it, import it, or hand it to an agent.<br>
Every theorem keeps its source and licence; authors' credit stays in the file headers.</p>
<p align="center">
<a href="lean-toolchain"><img src="https://img.shields.io/badge/dynamic/regex?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Flean-toolchain&search=v%5B0-9.%5D%2B%28-rc%5B0-9%5D%2B%29%3F&label=Lean%204&color=blue" alt="Lean 4 toolchain"></a>
<a href="https://competemath.com/tengoku"><img src="https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Fdata%2Fstats.json&query=%24.totals.trusted&label=trusted%20theorems&color=2e7d32" alt="Trusted theorems"></a>
</p>

[Lean](https://lean-lang.org) writes mathematics a computer can check, and [Mathlib](https://github.com/leanprover-community/mathlib4) is its main library. Other formal mathematics lives in separate Lean projects, each tied to its own Lean version, so projects on different versions cannot be imported together and a prover cannot see them all. Tengoku ports (translates) them onto one **toolchain** (a single Lean version) so they import together. The payoff: a theorem from one project can sit next to one from another in the same file. Translation is hard for two reasons: the translated statement must still imply the original (the *entailment* check), and each project must first be made *self-contained*, with everything its theorems depend on built together ([why](vision-draft.md#why-translation-is-hard)). Translations of dozens of further projects await promotion ([coverage](coverage-draft.md)).

Tengoku aims to be the shared, always-current memory of formal mathematics: a library that absorbs each Lean release's churn once, for everyone downstream, and in which every theorem records its source and licence and says how far it has been checked. Mathlib stays the curated centre, shaped for people writing proofs and so free to rename and refactor; Tengoku keeps what was proved, and a retracted theorem leaves a note on how to prove the same idea. So far it holds one toolchain. Tengoku is a community-maintained project, founded by an independent developer; [CompeteMath](https://competemath.com) and the [Leak](https://competemath.com/about/leak) theorem-proving agents use it ([vision](vision-draft.md)).

<p align="center"><img src="docs/img/try-it.svg" alt="Three commands: search Tengoku from a shell, give an AI agent the search tool, import the library into Lean." width="780"></p>

## Try it

New to Lean? Start with the web search: it finds theorems from a plain-English description, and each result shows its statement, its source and its credit.

```bash
# browse: competemath.com/tengoku (try "continuous image of compact")

# search from code (JSON: name, statement, status, library, source link)
curl -s 'https://competemath.com/api/tengoku/search?q=IsCompact.image' | head -c 230
# {"results":[{"id":3916779000,"name":"IsCompact.image","statement":"∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set X} {f : X → Y}, IsCompact s → Continuous f → IsCompact (f ''

# give an AI agent the search tool (Claude Code; no sign-up)
claude mcp add --transport sse tengoku-search \
  https://barkingtree-leak-i.hf.space/sse

# import it into Lean: one large download (needs git, zstd and elan, Lean's version manager)
git clone --filter=blob:none https://github.com/competemath/tengoku
cd tengoku && scripts/cache.sh get
```

Then, in one Lean file, the natural numbers (Lean's own) and a theorem translated from the Equational Theories project, which says what any magma satisfying law 1723 must be:

```lean
import Tengoku.All
open EquationalTheories

instance : Magma ℕ := ⟨fun a b => a + b⟩

-- addition on ℕ does not satisfy law 1723: it would make ℕ trivial
example : ¬ Equation1723 ℕ := fun h => by
  have h2 := Equation1723_implies_Equation2 ℕ h
  have := h2 0 1
  omega
```

## What "trusted" means

**Trusted** means the library builds with the theorem, with no `sorry` (Lean's placeholder for an unproved step), and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Records promoted from staging also pass a check that their assumptions are not contradictory (a search that can miss some); Mathlib's seeded records were trusted on the build alone. A second, independent kernel ([nanoda](https://github.com/ammkrn/nanoda_lib)) re-checks the compiled library every night. It does **not** mean the statement says what its source says, that a translation equals its original, or that anyone reviewed it ([benchmarks share this gap](https://arxiv.org/abs/2606.29493)). Public checks decide what is trusted, and anyone can read and re-run them; the known gaps, such as 262 CompeteMath problems labelled trusted without a build, are counted on the [trust page](trust-draft.md#known-gaps).

**For the authors of the projects Tengoku draws on:** the originals stay canonical, so cite the project, not Tengoku. Each theorem records its source, seeded files keep their authors' headers, and copyleft sources are refused. Corrections and removals: open an issue or a pull request ([how](CONTRIBUTING.md)). Mathlib's content is an Apache-licensed copy pinned to the commit in [SEED.md](SEED.md), keeping Mathlib's declaration names; Tengoku is independent of Mathlib and not endorsed by its maintainers.

## More

[Data card](data-draft.md) (download, fields, problems) · [trust](trust-draft.md) (stages, gaps) · [coverage](coverage-draft.md) · [evidence](evidence-draft.md) · [comparison](comparison-draft.md) · [vision](vision-draft.md) · [FAQ](faq-draft.md)

Anyone can contribute, by hand or with AI: a theorem, a project, or a goal ([CONTRIBUTING.md](CONTRIBUTING.md), [GOALS.md](GOALS.md)). Cite [DOI 10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400). Apache-2.0; each theorem keeps its upstream licence.

## Dedication

This project is founded for the sake of God (فِي سَبِيلِ ٱللَّٰهِ) - the prophet PBUH said:

> "Whoever takes a path in which he seeks knowledge, Allah will make easy for him, by it, a path to Paradise."
>
> «ومن سلك طريقا يلتمس فيه علما سهل الله له به طريقا إلى الجنة»
>
> — Ṣaḥīḥ Muslim, no. 2699 (narrated by Abū Hurayrah), Kitāb al-Dhikr wa-l-Duʿāʾ. Manuscript copy of 1164 CE: [Princeton University Library, Garrett MS 104Y, fol. 167a](https://dpul.princeton.edu/islamicmss/catalog/cr56n359w), [exact page](https://iiif-cloud.princeton.edu/iiif/2/4b%2F29%2F26%2F4b2926c452bf475ba690d038a6577e8b%2Fintermediate_file/full/full/0/default.jpg).

## Badges

<p align="center">
<a href="https://doi.org/10.5281/zenodo.23050400"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.23050400.svg" alt="DOI"></a>
<a href="https://scorecard.dev/viewer/?uri=github.com/competemath/tengoku"><img src="https://api.scorecard.dev/projects/github.com/competemath/tengoku/badge" alt="OpenSSF Scorecard"></a>
<a href="https://www.bestpractices.dev/projects/15102"><img src="https://www.bestpractices.dev/projects/15102/badge" alt="OpenSSF Best Practices"></a>
<a href="LICENSE"><img src="https://img.shields.io/badge/licence-Apache--2.0-blue" alt="Licence: Apache-2.0"></a>
<a href="https://app.fossa.com/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku?ref=badge_small"><img src="https://app.fossa.com/api/projects/git%2Bgithub.com%2Fcompetemath%2Ftengoku.svg?type=small" alt="FOSSA Status"></a>
<a href="https://sonarcloud.io/summary/new_code?id=competemath_tengoku"><img src="https://sonarcloud.io/api/project_badges/measure?project=competemath_tengoku&amp;metric=alert_status" alt="SonarQube Cloud quality gate"></a>
<a href="https://codecov.io/gh/competemath/tengoku"><img src="https://codecov.io/gh/competemath/tengoku/graph/badge.svg" alt="Codecov"></a>
</p>
