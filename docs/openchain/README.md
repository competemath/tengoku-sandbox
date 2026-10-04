# OpenChain programme documents

Tengoku keeps the documents an [OpenChain](https://openchainproject.org) self-certification asks for in this folder, so
each claim names the file, workflow or setting that backs it. Two specifications are covered:

| Specification | What it covers | Where |
|---|---|---|
| ISO/IEC 18974:2023 (security assurance) | how vulnerabilities in what Tengoku ships and uses are found, handled and communicated | [program.md](program.md), [vulnerabilities.md](vulnerabilities.md), [threat-model.md](threat-model.md) |
| ISO/IEC 5230:2020 (licence compliance) | how the licences of what Tengoku contains are recorded, obeyed and enforced | [program.md](program.md), [licence-compliance.md](licence-compliance.md) |

Tengoku is a one-maintainer project with no funding. The programme is sized to that: most of it is automated checks
that run on every pull request and on a schedule, and the documents say plainly where a person is the only safeguard.
These pages describe what exists today. They do not claim anything the repository does not do, and
[the known gaps](#known-gaps) are listed rather than hidden.

## Known gaps

| Gap | State |
|---|---|
| Triage of the SonarQube Cloud findings | the first baseline is in; its vulnerabilities (mostly "CLI argument reaches a path or command" in CI scripts that only workflows call) are not yet individually accepted or fixed |
| Funding and staffing | none: one volunteer maintainer; see [program.md](program.md#staffing-and-funding) |
| Independent legal or security adviser | none identified |
| A certification | not yet submitted; this folder is the evidence it would rest on |
