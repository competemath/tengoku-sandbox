# The blind re-proof test

Every other check asks whether a contribution is correct and safe. This one
asks whether it is **worth having**: does the PR add something the library
could not already reach in a few minutes?

## Who it applies to

A PR that adds **original** theorems to staging. A record is original unless
its `source_url` starts with one of the `translations` in
`schemas/sources.json` (existing formal libraries: a translation of a library
is never new mathematics, so it is exempt). Promotions are exempt too: their
records were assessed when they entered staging.

## The test

You name up to **ten headline theorems**, the ones that carry the contribution.
For each, a fresh agent that sees **only the statement** gets about
**5 minutes, hard stop at 7**, and the library's hosted services: search, proof
states, verification. Those services hold the library as it is on main, so
without your PR.

- If **every** headline is re-proved, the PR is **rejected**: the library
  already reaches all of it in minutes.
- If **at least one** resists, the PR passes this test.

A proof only counts as re-proving if the verification service accepted a script
containing the theorem exactly as stated, without `sorry`, `admit`,
`native_decide`, new axioms or `unsafe` (the library would not accept those
either).

## Running it

```bash
python3 scripts/assess/run.py data/staging/<library>/<your-file>.jsonl --headlines Name.one,Name.two
git add claims/ && git commit -s -m "blind re-proof claim"
```

It needs the `claude` CLI, logged in: the attempt runs on **your** subscription
(a few minutes of agent time per headline). It prints each call as it happens
and ends with the verdict the gate will reach. It writes:

| file | what it is |
| --- | --- |
| `claims/<your-file>/claim.json` | outcome, seconds and call counts per headline, the commit each service was on, and digests of the two files below |
| `claims/<your-file>/<n>-<Name>.working.md` | the attempt, readable: what the agent said it would try, every search, tactic and verification with its answer, in order, with times |
| `claims/<your-file>/<n>-<Name>.transcript.jsonl.gz` | the attempt, raw: every event of the agent's session with the second it arrived (machine paths and session ids removed) |

## What makes the record hard to fake

Nothing in `claim.json` is taken on trust. The gate (`scripts/ci/assess.py`,
job `assess`, step `blind-reproof`):

- recomputes outcome, duration and call counts **from the raw transcript** and
  compares them with the claim;
- **renders the working log again** from the transcript and compares it byte
  for byte, so the text a reviewer reads is exactly what happened;
- checks the agent was given **the test's own instructions**, word for word,
  for the statement that is in the PR;
- checks the agent had **only the library's services** as tools (no file
  access, no shell, no web): it could not have seen your proof;
- checks the services were on **a commit of main** throughout;
- checks the claim is attested by someone who **signed off** a commit of the PR;
- refuses a "resisted" that is not a full attempt: at least 290 seconds, run to
  the budget, 3 verifications and 10 calls, no silence longer than 150 seconds
  (a laptop asleep is not an attempt);
- scans the transcript for credentials.

## What a reviewer, human or bot, should look for in a working log

The numbers are checked by the gate. Judgement is not. Read the log and ask:

1. **Did it try the obvious things?** A search for the statement's key terms;
   the standard closing tactics for the domain (`simp`, `omega`, `nlinarith`,
   `aesop`, `decide`, `exact?`-style searches); a direct induction or case
   split where the statement invites one.
2. **Did failures change its course?** A credible attempt reacts to error
   messages: new lemmas searched, the goal restated, a different decomposition.
   Twenty near-identical calls are not an attempt.
3. **Is the commentary about this theorem?** It should mention the statement's
   own objects and the errors it actually got.
4. **Does the difficulty look real?** If the log shows the agent one lemma away
   when time ran out, say so: the headline is weak even though it passed.

Anyone may also refute a claim after the fact: a PR or issue with a short proof
of a "resisted" headline that verifies against the library as it was is
evidence the headline should not have counted.

## What this test cannot do

It shows that one capable agent, with the library's own tools, did not close
the theorem in seven minutes. It does not show the theorem is deep, new to
mathematics, or useful; and a determined contributor who controls their own
machine can still stage a weak attempt. The defences are the ones above: the
record is verbose enough to read, everything checkable is checked, reviewers
and bots read the logs, and maintainers re-run a sample of claims themselves.
A claim that does not survive a maintainer's re-run is grounds to revert.
