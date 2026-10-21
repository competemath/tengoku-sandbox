# The canary: `import Tengoku.All` must stay usable

`Canary.lean` is ordinary Lean and Mathlib, written the way a person or a prover writes it: `-(3 * x)` on a real number, a variable named `v`, `ω` or `na`, `∘`, `⁻¹`, `∈`, `l[0]`,
`≃`, `⟶`, and `omega`, `positivity`, `linarith`, `nlinarith`, `ring`, `field_simp`, `norm_num`, `gcongr`, `fun_prop`, `interval_cases`, `decide`, `simp`. It must elaborate under
`import Tengoku.All`, whatever any library of the tree declares globally. A failure means a library leaks into everybody else:

| symptom | cause |
|---|---|
| `positivity`, `linarith`, `omega`, `ring` fail | a global instance or simp lemma (`attribute [instance]`, `HMul R G (FreeModule R G)`, `Torsor.toHDiv`) |
| `Ambiguous term -(3 * x)` | a global notation with the token of a core notation (`prefix:80 "-"`) |
| `unexpected token 'v'; expected ')'` | a global notation, `syntax`, `macro` or `elab` whose atom looks like an identifier: that word is reserved in every file |

(2026-10-17: lean-pool's `prefix:80 "-"` and its reserved words were on Leak IV for days; `TengokuLeak.lean` did not look at notation.)

Where it runs
- **the merge queue** (`queue-gate.yml`, step "Canary"), on a group that changes Lean, after the library is built as main will have it. Mode `report` (a warning and a summary) or `enforce`
  (the group leaves the queue): the repository variable `TENGOKU_CANARY`, else the word in `mode`. The mode and the probes (`Canary.lean`) are the BASE's copies: a group cannot lower its gate
  or delete the probe that would catch it (its own `Canary.lean` is used only when the base has none, on the first PR).
- **the Leak space** (`leak-canary.yml`): `leak_canary.py` asks the space the provers use (`verify_full_script` over MCP/SSE) to compile the same file, after each promotion and every six hours.
  Exit 0 compiled, 1 did not compile (lines and messages printed), 2 the space could not be asked.
  The space is chosen by name (`--space leak-iv`, a constant of the script; the workflow input is a choice), never by address. After a promotion the run first waits
  (`--settle 90 --wait-refresh 2400`) until the space reports `refreshing: false`, `status: current` and a pinned tree equal to the base of the published cache pointer, and exits 2
  when it never does. Limit: the space reports the base commit it pinned, not the top-up commit it loaded on top, so a promotion that only moves the top-up cannot be told apart from
  the one before it; the six-hourly run catches it, and the merge queue judges every group with the same file before it merges. The workflow reads the three files from main
  through the API (no checkout in a `workflow_run` workflow).

`CanaryKnown.lean` holds the same kind of failure in libraries that are not fixed yet. It is reported, never a gate. It is empty today: the six words of equational-theories (a generated
library) moved into `Canary.lean` on 2026-10-18, when the generator began to scope what it writes. A line moves into `Canary.lean` the day its example compiles.

Adding a probe: write the `example`, run `python3 scripts/ci/canary/leak_canary.py` (it needs nothing but the network), and add the probe to the list in `tests/test_canary.py`.
