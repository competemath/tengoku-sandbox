# Consistency audit of how Tengoku is described (draft)

Read on 2026-10-02: the `competemath/tengoku`, `competemath/tengoku-sandbox` and `competemath/emissary-archangel` repositories (descriptions, READMEs, docs, citation files) and competemath.com (`/about`, `/about/tengoku`, `/tengoku`, `/faq`, `/about/leak`). The two private repositories were not read. The wording to converge on is in [messaging-draft.md](messaging-draft.md).

## 1. It is called five different things

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

## 3. The numbers disagree

| Claim | Where |
|---|---|
| "hundreds of different sources" | `tengoku` README, About |
| 106 registered libraries | `docs/why-tengoku.md` |
| 238 libraries | `data/stats.json` (`library_count`, generated 2026-09-21) |
| 109 sources with a licence | `schemas/sources.json` |
| 116 upstream libraries | `NOTICE` |
| 198,172 trusted theorems typed into prose | `docs/why-tengoku.md` (stale the moment the pipeline promotes one) |

**Fix:** define "registered source" once (an entry of `schemas/sources.json`), publish the count in `stats.json`, and never type a count into prose.

## 4. No immediate way to use it on the README's first screen

Today the README opens with a tagline and two badges, then "About" and "Developers". The ways to try Tengoku (the browser search, the MCP endpoint, the HTTP API, `scripts/cache.sh get`) are scattered over README, `docs/api.md`, `docs/why-tengoku.md` and the site. There is no table of the problems it solves, no picture of how a theorem becomes trusted, and no demo.
**Fix:** [readme-draft.md](readme-draft.md): a four-row "Try it now" table, the problem table, one diagram, a video slot with its storyboard.

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
