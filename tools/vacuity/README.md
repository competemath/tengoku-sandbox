# Vacuity check

A theorem whose assumptions can never all hold is vacuously true: it proves
nothing about anything, and Lean cannot tell, because it is still correct.
This script finds such theorems: for every theorem of the modules you name, it
tries to prove `False` from the theorem's hypotheses alone, with a handful of
decision procedures under a fixed budget (`omega`, `simp_all`, `decide`, and,
where the project imports Mathlib, `linarith`, `positivity`, `grind`, `aesop`).
If one succeeds, the theorem is reported with the hypotheses that clash.

## Use

Run it inside the built Lake project the modules belong to:

```
lake env lean --run tools/vacuity/vacuity.lean Zeta23.Main Zeta23.XiPrime.Final
```

Output, one block per vacuous theorem, then a summary:

```
VACUOUS vac_two_bounds VacTest omega
  its assumptions can never all hold; `omega` derives a contradiction from:
    h₁ : 5 < n
    h₂ : n < 3
checked 6 theorems in 1 modules: 3 vacuous
```

It is a warning, never a verdict: the exit code is 0 either way. Loading the
environment costs most of the time (about a minute for a Mathlib project);
each theorem then takes a fraction of a second.

## What it does and does not catch

- Caught: hypotheses that contradict each other or themselves, as far as the
  listed tactics can see (`n < 0` on a natural number, `5 < n` with `n < 3`,
  `p` with `¬p`, linear arithmetic, decidable facts).
- Not reported: a theorem whose conclusion is `False`, or a negation `¬ P`
  (that is `P → False`): deriving `False` is its content, not a defect.
- Not caught: contradictions the tactics cannot find, and a statement that is
  merely trivial, or true of the empty set for reasons that need a proof.
- Nothing here says a statement means what its author intended.

`example.lean` is the test module: the three `vac_*` theorems are reported,
the other three are not.
