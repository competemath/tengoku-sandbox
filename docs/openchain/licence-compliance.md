# Licence compliance: recording, inquiries, remediation

The procedure for ISO/IEC 5230 (licence compliance). Roles are in [program.md](program.md).

## Responsibilities

The maintainer owns licence compliance, including every decision to register or remove a source. A contributor is
responsible for the licence of what they submit: each commit is signed off (Developer Certificate of Origin) and a
record's `source_url` and credit are required; the gate refuses a record whose source is not on the allow-list.

## How licences are recorded and enforced

- **Per source:** `schemas/sources.json` lists every accepted source with its licence. A source is added, with its licence,
  in the same tooling pull request as the first record from it. A copyleft licence is not accepted.
- **Per record:** each record names its origin in `source_url` and its credit; a record and the module generated from it
  stay under that licence (`LICENSE-THIRD-PARTY.md` sections 1-3).
- **Gate checks:** the credit check and the secrets scans run on every pull request. The allow-list of sources and the
  content lint run on `content`, `tombstone` and `promotion` pull requests ([How Tengoku is tested](../testing.md)).
- **Notices:** `LICENSE-THIRD-PARTY.md` and `NOTICE` reproduce what the upstream licences require. They are attached to every dataset release (the
  snapshots), to each nightly cache release and to the standing `cache-topups` release, which the nightly build adds
  them to: a `cache-topups` release created between nightlies can lack them until the next one, and releases published
  before 2026-10-02 do not carry them.

## Inquiries

Anyone may ask a licence or attribution question by opening an issue titled "Licence inquiry" on
`competemath/tengoku`; if the matter should not be public, use the private reporting form on the Security tab and say it is
a licence matter. The maintainer aims to reply within seven days, and records any change it leads to.

## Reviewing and remediating a non-compliant case

When a licence problem is reported or found (a source's licence differs from the record, a file without the right to be
here, a copyleft licence in the mix):

1. **Withdraw first.** Stop the affected source: deregister it in `schemas/sources.json` (a tooling pull request), and remove its
   records and generated modules; the gate allows deleting a deregistered source's data.
2. **Decide.** Read the licence and the upstream statement. If the licence is permissive and compatible, restore the source
   with the correct licence recorded. If it is not, it stays out.
3. **Record.** Add the source, the licence and the reason to `LICENSE-THIRD-PARTY.md` section 4 (Removed sources), and a row
   to the review log.
4. **Tell the person who raised it.** Earlier commits stay in git history under their upstream licence; section 4 says so.

Past cases: `lean-wasm` (GPL-3.0) and `software-foundations-lean` (AGPL-3.0) were removed this way.
