/-
Jinshi fixture for `mutants` (docs/jinshi.md, head K): a few small theorems whose proofs seed the differential kernel fuzzing.
Every mutant of these proofs is judged by Lean's kernel in the examination's own process (Mutants.expected.tsv names the verdicts),
written as a module of its own, and judged again by leanchecker and lean4lean (scripts/jinshi/selftest.py, the appended block):
the kernels must agree on every mutant, refuse at least one and accept at least one. Lean core only, no tree.
-/
-- jinshi: only mutants
/-! jinshi: mutants — this module opts in to the `mutants` examination in the all-examinations run (the examination is otherwise
off unless `--check` names it: it writes files and runs kernels) -/
namespace JinshiFixtures

/-- an `Eq.refl` proof: `Eq.refl (2 + 2)` is a mutant the kernels accept (definitional); the proof without its argument, one they refuse -/
theorem refl_four : 2 + 2 = 4 := Eq.refl 4

/-- an application of `Nat.add_comm`: swapping its arguments, dropping one, replacing `a` by `b` are all refused -/
theorem comm_app (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- a literal in the statement: `6 ≤ 7` with the proof of `5 ≤ 7` is refused (the `decide` proof names the instance at 5) -/
theorem five_le_seven : 5 ≤ 7 := by decide

/-- two proofs of different propositions in one term: exchanging them is refused -/
theorem trans_app (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂

end JinshiFixtures
