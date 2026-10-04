/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2008, Problem 2
(a) Prove that
          ```
          x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1
          ```
for all real numbers `x`,`y`, `z`, each different from 1, and satisfying `xyz = 1`.

(b) Prove that equality holds above for infinitely many triples of rational numbers `x`, `y`, `z`,
each different from 1, and satisfying `xyz = 1`.
-/

namespace Imo2008P2

/-
# Solution
(a) Since `xyz = 1`, we can apply the substitution `x = a/b`, `y = b/c`, `z = c/a`.
Then we define `m = c-b`, `n = b-a` and rewrite the inequality as `LHS - 1 ≥ 0`
using `c`, `m` and `n`. We factor `LHS - 1` as a square, which finishes the proof.

(b) We present a set `W` of rational triples. We prove that `W` is a subset of the
set of rational solutions to the equation, and that `W` is infinite.
-/

theorem subst_abc {x y z : ℝ} (h : x * y * z = 1) :
    ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x = a / b ∧ y = b / c ∧ z = c / a := by
  use x, 1, 1 / y
  obtain ⟨⟨hx, hy⟩, _⟩ : (x ≠ 0 ∧ y ≠ 0) ∧ z ≠ 0 := by
    have := h.symm ▸ one_ne_zero
    simpa [not_or] using this
  have : z * (y * x) = 1 := by rw [← h]; ac_rfl
  simp [field, mul_assoc, *]

def rationalSolutions :=
  {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y * z = 1 ∧
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 = 1}

end Imo2008P2
