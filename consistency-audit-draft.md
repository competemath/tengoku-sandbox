# Consistency audit of how Tengoku is described (draft)

Read on 2026-10-02: the `competemath/tengoku`, `competemath/tengoku-sandbox` and `competemath/emissary-archangel` repositories (descriptions, READMEs, docs, citation files) and competemath.com (`/about`, `/about/tengoku`, `/tengoku`, `/faq`, `/about/leak`). The two private repositories were not read. The wording to converge on is in [messaging-draft.md](messaging-draft.md).

## 1. It is called several different things

| Where | Calls it |
|---|---|
| GitHub description of `tengoku` | "one verified Lean 4 **tree**" |
| `tengoku` README tagline | "an AI-first formal mathematics **library**" |
| competemath.com `/tengoku` | "an open-source Lean 4 formal **knowledge tree**" |
| competemath.com `/about/tengoku` | "one self-contained Lean 4 **library**" |
| `CITATION.cff`, Zenodo | "one verified Lean 4 tree" (a **dataset**) |
| Emissary-Archangel README | "the Tengoku **tree**" |

**Fix:** "library" in prose everywhere ("tree" stays for the directory in technical docs; "dataset" only for the snapshot release).

## 2. The purpose differs from page to page

| Where | Says Tengoku is for |
|---|---|
| `tengoku` README, `/about/tengoku` | "continuously improving, reliable context for automated theorem provers" |
| competemath.com `/about` and `/faq` | checking CompeteMath's problems and answers ("guaranteeing the mathematics is airtight") |
| GitHub description | a unified source of theorems with credit (no audience) |
| Zenodo / `CITATION.cff` | a citable dataset |
| competemath.com `/tengoku` | a searchable tree that grows with Leak |

A visitor from the site's About page expects a problem-checking tool, one from GitHub expects an AI-training resource, one from Zenodo a dataset. All are true, none is the first sentence.
**Fix:** the one answer in [messaging-draft.md](messaging-draft.md) ("what is it for"), with CompeteMath named as one user of Tengoku.

## 3. The numbers disagree, and one of them hides a real inconsistency

| Claim | Where |
|---|---|
| "hundreds of different sources" | `tengoku` README, About |
| 106 registered libraries | `docs/why-tengoku.md` (this is the count of sources that have a corpus the library can compile) |
| 109 registered sources | `schemas/sources.json` (`licences`); 106 of them have a corpus |
| 116 upstream libraries | `NOTICE` |
| 238 libraries | `data/stats.json` (`library_count`: it also counts the Mathlib topic files of the seed) |
| 5,404 theorems in staging from 45 libraries | `docs/why-tengoku.md` |
| 79 in staging | `data/stats.json`, generated 2026-09-21 and not refreshed since |
| 8,969 in staging from 60 libraries | counted from `data/staging/` on 2026-10-02 |

Most of these are different things with the same name, so one definition each is the fix ("registered source"; "library with a corpus"; "seed topic file"), published from one generated file. The stale `stats.json` also feeds the README badge and the site's counters.

**A real inconsistency:** the 262 CompeteMath records in `data/trusted/competemath.jsonl` are marked *trusted* and are in the v1.0.0 dataset, but the library has no module for them, so they are not built into it; they were verified by the Leak IV verifier on Lean v4.29.1 and v4.32.0, not on the library's v4.34.0-rc2; and 103 of the 262 use `native_decide`, which trusts the compiler. That contradicts "a trusted theorem is machine-checked against the whole library" and "only the standard axioms" for 0.13% of the trusted records. Two ways out: move them to *tentative* until they are translated and built (a data change, and a corrected dataset release), or translate them. Until then the README should not say that every trusted theorem is built into the library.

**Two more things the counting found** (details in [data-draft.md](data-draft.md)):

- In 4,004 records the `name` is cut at a Unicode subscript (`A₂_mem_circumsphere` is stored as `A`). A hypothesis, not yet tested: this is part of why the nightly check cannot match about 25,000 trusted names to declarations (the rest being the 1,798 records from Mathlib's `Archive`, `MathlibTest` and `Counterexamples`, which the library does not compile, and declarations whose recorded name is not their full name). Fixing the extraction of names may close much of that gap.
- `docs/why-tengoku.md` is stale: it gives 5,404 theorems in staging from 45 libraries (now 8,969 from 60) and says the second-kernel check is in progress (it has run nightly for days).

## 4. No immediate way to use it on the README's first screen

Today the README opens with a tagline and two badges, then "About" and "Developers". The ways to try Tengoku (the browser search, the MCP endpoint, the HTTP API, `scripts/cache.sh get`) are scattered over README, `docs/api.md`, `docs/why-tengoku.md` and the site. There is no table of the problems it solves, no picture of how a theorem becomes trusted, and no demo.
[readme-draft.md](readme-draft.md) opens with the problem, an animated terminal of three commands, and the Lean example.

## 5. Smaller items

| Where | Issue | Fix |
|---|---|---|
| README, `/about/tengoku` | the name is glossed ("天国, heaven") only on `/tengoku` | gloss once in each |
| `/about/tengoku` | the meta description says "AI-first", the README says "AI-first", the GitHub description does not | one tagline everywhere |
| `/about`, `/faq` | "seeded from Mathlib and other open libraries" suggests Tengoku is only a Mathlib derivative | "assembled from many projects, starting from Mathlib" |
| `tengoku-sandbox` README | still the long README of an earlier phase, now under a warning | replaced by a short sandbox page (separate PR) |
| Emissary-Archangel README | begins with the mechanism, never says why Tengoku needs translations | first sentence in [messaging-draft.md](messaging-draft.md) |
| `/about/leak` | "Lemma search over Tengoku" is right, but the first mention never says what Tengoku is | a link to `/about/tengoku` on first use |

## Proposed order

1. Judge [readme-draft.md](readme-draft.md) and [messaging-draft.md](messaging-draft.md) (rendered on the branch).
2. Apply the wording to the library README, then the site pages (a compete-math PR), the Emissary README and the repository descriptions.
3. Add a check that fails when a count is typed into prose (the stats come from one file).
