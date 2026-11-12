# Training on Tengoku

For labs, and anyone building a model or dataset from Tengoku.

Tengoku is Apache-2.0, and every registered source stays under its own licence; all of them permit training. This page says what those licences require, what we ask on top, and how commitments are recorded.

## Required

These are conditions of the licences and of using CompeteMath's names.

1. **Keep the notices.** Keep the copyright and attribution notices of everything you reproduce, and ship [NOTICE](../NOTICE) and the licence texts alongside (Apache-2.0 section 4).
2. **Say what you changed.** A modified copy states its changes (section 4(b)).
3. **Do not imply endorsement.** The name "CompeteMath", and the names of its sub-services, are not to be used in any way to suggest they back or endorse whatever you use data from this repository for.

For the hosted services (the search API, the MCP tools, Leak): they are for interactive use. Bulk data comes from the repository and its releases, not from crawling the services, which may be blocked.

## Asked of every lab that trains on Tengoku

1. **Name it.** Cite Tengoku ([10.5281/zenodo.23050400](https://doi.org/10.5281/zenodo.23050400)) and give the release or commit you used in your training-data summary and model card. Providers of general-purpose AI models on the EU market must publish such a summary (AI Act, Article 53(1)(d)): from 2 August 2025, and by 2 August 2027 for models already on the market before then.
2. **Keep provenance with each example.** A record's `library` and `source_url` (where its notices live) and its `Author:` line travel with it into any dataset you build or publish.
3. **Honour retractions.** A retracted record (a tombstone line in `data/trusted/`) or a library removed from [the allowlist](../schemas/sources.json) is dropped from your next training run and from any data you publish. Re-sync at each release.
4. **Keep evaluations clean.** Tengoku includes public formalisations of competition problems (Compfiles, IMO shortlist) and other solutions. Decontaminate before reporting results on miniF2F, PutnamBench or similar, and publish your method and hit counts.
5. **Describe our labels accurately.** `trusted` means the relevant library checks have passed. It does not mean a mathematician has read the statement.
6. **Report errors.** A wrong or misleading statement goes to [Issues](https://github.com/competemath/tengoku/issues/new).
7. **Give back.** Proofs your models find for open statements, once verified, come in through [the usual route](how-a-pr-flows.md) with an `Author:` line.

## Commitments

A lab that publicly commits to the section above is listed here, with the date and a link to its statement. To be listed, open a pull request adding a row.

| Lab | Date | Statement |
| --- | --- | --- |
| None yet | | |
