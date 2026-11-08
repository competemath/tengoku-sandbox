import Tengoku.All

/-!
# Known open: the same kind of failure as Canary.lean, in libraries that are not fixed yet.

Not a gate: scripts/ci/canary/leak_canary.py and the queue step report these and do not fail on them. Empty since 2026-10-18: the six words of equational-theories (a generated library whose global `elab` and `macro` commands reserved them for the whole tree) compile on
Leak IV since the generator scopes its notation (tengoku#615, #618) and moved into Canary.lean. A line goes in here when a library is found to leak and is not fixed yet,
and into Canary.lean the day its example compiles.
-/

set_option Elab.async false
set_option linter.unusedVariables false
