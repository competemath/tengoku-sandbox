# Data card: the trusted dataset, v1.0.0 (draft)

What the downloadable dataset is, field by field, what is in it, and what is wrong with it. Counted from the release file on 2026-10-02 by [`scripts/dataset_audit.py`](scripts/dataset_audit.py), which anyone can rerun on the file (`python3 scripts/dataset_audit.py tengoku-dataset.jsonl.gz`).

## Get it, check it

```bash
curl -LO https://github.com/competemath/tengoku/releases/download/v1.0.0/tengoku-dataset.jsonl.gz   # 17,955,623 bytes
gh attestation verify tengoku-dataset.jsonl.gz -R competemath/tengoku                                # build provenance
```

The release also holds `snapshot.json` (the commit, the toolchain, the counts, the file's sha256) and `CITATION.cff`. Cite the release by its DOI ([10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400) resolves to the newest version). A new toolchain or a removed field is a new major version, added theorems a minor one, corrections a patch.

## What is in it

One JSON object per line; **only trusted records**. Tentative and staging records are not in the file.

| Source | Records | Notes |
|---|---:|---|
| Mathlib and its dependencies | 188,989 | one pinned commit (`217ba069`), 95% of the file |
| Equational Theories | 8,921 | the one research project promoted so far |
| CompeteMath's problems | 262 | marked trusted, [not built into the library](trust-draft.md#known-gaps) |
| **Total** | **198,172** | 161,646 distinct names |

All records are Apache-2.0 (Mathlib and Equational Theories are Apache-2.0 upstream). Of the statements, 78,554 + 8,875 begin `theorem`, 36,692 + 40 begin `lemma`; the rest (73,749) are written as a bare type, as the search service shows them.

## Fields

| Field | What it holds |
|---|---|
| `name` | the declaration's name (see the problems below: not unique, and sometimes cut short) |
| `statement` | the Lean statement; for Mathlib and Equational Theories **without** `import`, `open`, `namespace` or `variable` context, so it does not compile on its own |
| `proof` | the proof text; empty in 1,040 records (all Mathlib), where the proof is part of the statement text (equation-compiler or pattern-matching definitions) |
| `library` | `mathlib`, `equational-theories` or `competemath` |
| `source_url` | the source file at a fixed commit (for Mathlib content, the file in Tengoku's own tree, whose upstream commit is in `SEED.md`) |
| `licence` | the record's licence |
| `toolchain` | the Lean version the record was built or verified on |
| `promoted_at` | when it became trusted (empty in the records of the first release) |
| `credit`, `upstream`, `credit_corrected_evidence`, `headline` | reserved: **empty in every record of v1.0.0**. Authors of seeded content are in the headers of the source files, not in the data. |

There is no tier field (every record is trusted by definition, including the 262 that should not be) and no stable id. The key to use is (`name`, `source_url`).

## Problems you should know about

- **The 262 CompeteMath records** were verified by the Leak IV verifier on Lean v4.29.1 (232) and v4.32.0 (30), not on the library's toolchain; 103 use `native_decide` and one (`quadratic_echo`) contains `sorry`.
- **Names are cut short at a subscript.** In 4,004 theorem and lemma records the `name` field differs from the name in the statement (3,081 involve a Unicode subscript): the theorem `A₂_mem_circumsphere` has the name `A`. Together with name clashes across files, 14,122 names map to more than one statement. Use the name in the statement, not the `name` field, until this is fixed.
- **Duplicates:** 198,172 rows, 161,646 distinct names.
- **Toolchain:** 197,910 records say `v4.34.0-rc2`, a release candidate; the next version will change some statements' meaning or compile status.
- **Overlap with benchmarks is not excluded.** The file contains no miniF2F, PutnamBench or FATE-X files, but it does contain Mathlib's `Archive` (906 records, including 508 from the IMO problems and 164 from Wiedijk's list of 100 theorems with proofs), `MathlibTest` (477) and `Counterexamples` (415). Names and paths were compared; statement text was not. Run your own overlap check before using it to evaluate a prover.
- **Not a training set as it stands:** 95% is Mathlib at one commit, which most models have seen; the part that is new is 9,183 records.

## What is planned

A tier field and an id; the reserved fields filled where they apply; names taken from the declaration, not cut at a subscript; the 262 moved out until they are built; a statement context (imports and opens) per record so it compiles alone; a next release that says what changed.
