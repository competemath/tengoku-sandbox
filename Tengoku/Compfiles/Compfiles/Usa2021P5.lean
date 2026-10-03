/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2021, Problem 5

Let n ≥ 4 be an integer. Find all positive real solutions to the following
system of 2n equations:

  a₁ = 1/a₂ₙ + 1/a₂,
  a₂ = a₁ + a₃,
  a₃ = 1/a₂ + 1/a₄,
  a₄ = a₃ + a₅,
  a₅ = 1/a₄ + 1/a₆,
  a₆ = a₅ + a₇,
  ⋮
  a₂ₙ₋₁ = 1/a₂ₙ₋₂ + 1/a₂ₙ,
  a₂ₙ = a₂ₙ₋₁ + a₁.
-/

namespace Usa2021P5

/-- Eliminating the odd-indexed variables from the system yields a relation
among the even-indexed variables alone:
`a k = 1 / a (k - 1) + 2 / a k + 1 / a (k + 1)`. -/
lemma even_relation {n : ℕ} {a b : ZMod n → ℝ}
    (h1 : ∀ k, a k = b k + b (k + 1))
    (h2 : ∀ k, b k = 1 / a (k - 1) + 1 / a k) (k : ZMod n) :
    a k = 1 / a (k - 1) + 2 / a k + 1 / a (k + 1) := by
  have e2 := h2 (k + 1)
  rw [add_sub_cancel_right] at e2
  conv_lhs => rw [h1 k, h2 k, e2]
  ring

/-- The unique solution of the system: the even-indexed terms equal `2` and the
odd-indexed terms equal `1`, i.e. `(a₁, a₂, a₃, a₄, …) = (1, 2, 1, 2, …)`.
The first component is the sequence of even-indexed terms and the second
component is the sequence of odd-indexed terms. -/
abbrev solution (n : ℕ) : (ZMod n → ℝ) × (ZMod n → ℝ) :=
  (fun _ => 2, fun _ => 1)

end Usa2021P5
