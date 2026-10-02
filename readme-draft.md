<p align="center"><img src="logo.png" alt="Tengoku" width="150"></p>
<h1 align="center">Tengoku (天国)</h1>
<p align="center"><b>Formal mathematics from many Lean projects, translated onto one Lean version and machine-checked.</b><br>
Today: Mathlib and Equational Theories; more on the way. Search it, import it, or hand it to an agent.<br>
Every theorem keeps its source, licence and authors' credit.</p>
<p align="center">
<a href="lean-toolchain"><img src="https://img.shields.io/badge/dynamic/regex?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Flean-toolchain&search=v%5B0-9.%5D%2B%28-rc%5B0-9%5D%2B%29%3F&label=Lean%204&color=blue" alt="Lean 4 toolchain"></a>
<a href="https://competemath.com/tengoku"><img src="https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcompetemath%2Ftengoku%2Fmain%2Fdata%2Fstats.json&query=%24.totals.trusted&label=trusted%20theorems&color=2e7d32" alt="Trusted theorems"></a>
</p>

[Lean](https://lean-lang.org) writes mathematics a computer can check, and [Mathlib](https://github.com/leanprover-community/mathlib4) is its main library. Other formal mathematics lives in separate Lean projects, each tied to its own Lean version, so projects on different versions cannot be imported together and a prover cannot see them all. Tengoku ports (translates) them onto one **toolchain** (a single Lean version) so they import together. The rest is under way: translations of dozens of further projects await promotion ([coverage](coverage-draft.md)).

Tengoku wants to be the shared, always-current memory of formal mathematics: a library that absorbs each Lean release's churn once, for everyone downstream, and in which every theorem says where it came from and how it was checked. It is built by one independent developer, alongside [CompeteMath](https://competemath.com) and the [Leak](https://competemath.com/about/leak) theorem-proving agents; the checks, not the author, decide what is trusted ([vision](vision-draft.md)).

## Try it

New to Lean? Start with the web search: it finds theorems from a plain-English description, and each result shows its statement, its source and its credit.

```bash
# browse: competemath.com/tengoku (try "continuous image of compact")

# search from code
curl -s 'https://competemath.com/api/tengoku/search?q=IsCompact.image' | jq -r '.results[0] | "\(.status) \(.library) \(.name): \(.statement)"'
# trusted mathlib IsCompact.image: ∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set X} {f : X → Y}, IsCompact s → Continuous f → IsCompact (f '' s)

# give an AI agent the search tool (Claude Code; no sign-up)
claude mcp add --transport sse tengoku-search \
  https://barkingtree-leak-i.hf.space/sse

# import it into Lean: a few minutes, mostly one download (needs git, zstd and elan, Lean's version manager)
git clone --filter=blob:none https://github.com/competemath/tengoku
cd tengoku && scripts/cache.sh get
```

Then, in one Lean file, the natural numbers (Lean's own) and a theorem translated from the Equational Theories project, which says what any magma satisfying law 1723 must be:

```lean
import Tengoku.All
open EquationalTheories

instance : Magma ℕ := ⟨fun a b => a + b⟩

-- addition on ℕ does not satisfy law 1723: the law would make ℕ trivial
example : ¬ Equation1723 ℕ := fun h => by
  have h2 := Equation1723_implies_Equation2 ℕ h
  have := h2 0 1
  omega
```

## What "trusted" means

**Trusted** means the library builds with the theorem, with no `sorry` (Lean's placeholder for an unproved step), only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and its assumptions checked for inconsistency (a search that can miss some). A second, independent kernel ([nanoda](https://github.com/ammkrn/nanoda_lib)) re-checks the compiled library every night. It does **not** mean the statement says what its source says, that a translation equals its original, or that anyone reviewed it ([benchmarks share this gap](https://arxiv.org/abs/2606.29493)). Two exceptions are known and counted in [TRUST.md](trust-draft.md#known-gaps): 262 CompeteMath problems carry the label without a build, and the nightly check does not match about 25,000 trusted names, mostly Mathlib index entries.

**For the authors of the projects Tengoku draws on:** the originals stay canonical, so cite the project, not Tengoku. Each theorem links to its source at a fixed commit. Translations are labelled, seeded files keep their authors' headers, copyleft sources are refused, and corrections or removal start with an issue ([how](CONTRIBUTING.md)). Mathlib's content is an Apache-licensed copy pinned to a named commit, in `Tengoku.*` modules with Mathlib's own declaration names; it is independent of, and not endorsed by, Mathlib's maintainers, whose line-by-line review Tengoku does not claim to match.

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
