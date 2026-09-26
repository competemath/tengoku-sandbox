# Security policy

Tengoku is a library other projects build and depend on, so a flaw in what it accepts or ships can reach
them. Please report anything that could let content, code or a build output that should have been refused
get through.

## How to report

Use GitHub's private vulnerability reporting: open the **Security** tab of this repository and choose
**Report a vulnerability**. The report stays private between you and the maintainers until a fix is out.

Please do not open a public issue or pull request for a vulnerability, and do not test an attack against
the repository itself: the [sandbox](https://github.com/competemath/tengoku-sandbox) runs the same gate for
that purpose.

A useful report says what you did, what you expected the gate or build to do, and what it did instead. A
branch, a PR in the sandbox or a record that shows it is the fastest way to a fix.

## What is in scope

- **The PR gate and the merge queue**: a PR that passes checks it should fail, a check that runs code from
  a PR, a way to spoof a required check, or to change the rules that judge a PR.
- **Records**: a record that runs code when the tree is built, uses an axiom or `sorry` without being
  caught, or states something other than what the gate verified.
- **Build outputs**: a cache or release that can be tampered with without its attestation failing.
- **Credentials**: a token or secret exposed by a workflow, a log or the repository.
- **The hosted services** (Leak I, II and IV) where they serve this library.

Mathematical mistakes in a record, a wrong statement or a poor formalisation, are not vulnerabilities:
open a normal issue or PR for those.

## What happens next

We aim to reply within seven days, keep you informed while a fix is prepared, and credit you when it is
published, unless you ask us not to.
