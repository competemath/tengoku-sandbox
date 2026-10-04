/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1980, Problem 1

A balance has unequal arms and pans of unequal weight. It is used to weigh
two objects of unequal weight. The first object balances against a weight A,
when placed in the left pan and against a weight a, when placed in the right
pan. The corresponding weights for the second object are B and b. A third
object balances against a weight C, when placed in the left pan. What is its
true weight?
-/

namespace Usa1980P1

open Real

noncomputable abbrev solution (A a B b C : ℝ) : ℝ :=
  C * sqrt ((a - b) / (A - B)) +
    (b * A - a * B) / ((A - B) * (sqrt ((a - b) / (A - B)) + 1))

/-
The effect of the unequal arms and the pans of unequal weight is that there
are fixed constants `h` and `k` with `0 < h` such that an object of true
weight `x` placed in the left pan balances a weight `y` placed in the right
pan if and only if `x = h * y + k`. The solution determines `h` and `k` from
the data of the first two objects and then reads off the true weight
`x₃ = h * C + k` of the third object.
-/

/-- The two objects have unequal weights, so the weights `A` and `B` that
balance them from the left pan must differ. -/
lemma ne_of_balance {A B h k x₁ x₂ : ℝ}
    (h1 : x₁ = h * A + k) (h3 : x₂ = h * B + k) (hne : x₁ ≠ x₂) :
    A ≠ B := by
  intro hAB
  exact hne (by rw [h1, h3, hAB])

/-- Eliminating the true weights `x₁` and `x₂` gives `a - b = h ^ 2 * (A - B)`. -/
lemma h_sq {A a B b h k x₁ x₂ : ℝ}
    (h1 : x₁ = h * A + k) (h2 : a = h * x₁ + k)
    (h3 : x₂ = h * B + k) (h4 : b = h * x₂ + k) :
    h ^ 2 * (A - B) = a - b := by
  rw [h1] at h2
  rw [h3] at h4
  linear_combination h4 - h2

/-- The offset `k` is determined by `(h + 1) * k = a - h ^ 2 * A`. -/
lemma offset_eq {A a h k x₁ : ℝ}
    (h1 : x₁ = h * A + k) (h2 : a = h * x₁ + k) :
    (h + 1) * k = a - h ^ 2 * A := by
  rw [h1] at h2
  linear_combination -h2

end Usa1980P1
