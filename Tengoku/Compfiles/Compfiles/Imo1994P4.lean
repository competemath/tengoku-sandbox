/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benpigchu
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1994, Problem 4

Determine all ordered pairs of positive integers (m, n) such that

            (n³ + 1) / (mn - 1)

is an integer.
-/

namespace Imo1994P4

lemma nonneg_mul_eq_two {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hab: a * b = 2) : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  have ha_pos : 0 < a := by lia
  have hb' : b ≤ 2 := by
    rw [← hab]
    calc b
        = 1 * b := by rw [one_mul]
      _ ≤ a * b := by apply mul_le_mul <;> lia
  interval_cases b <;> lia

lemma aux₁ {a b c d : ℤ}
  (hc : 0 < c) (hd : 0 < d)
  (h₁ : a * b = c + d) (h₂ : a + b = c * d) (ha': a = 1) :
  (a = 1 ∧ b = 5 ∧ c = 3 ∧ d = 2) ∨ (a = 1 ∧ b = 5 ∧ c = 2 ∧ d = 3) := by
  rw [ha'] at h₁ h₂
  rw [one_mul] at h₁
  rw [h₁] at h₂
  have hcd : (c - 1) * (d - 1) = 2 := by grind
  have hcd' := by apply nonneg_mul_eq_two _ _ hcd <;> lia
  lia

lemma aux₂ {a b c d : ℤ}
  (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
  (h₁ : a * b = c + d) (h₂ : a + b = c * d) (ha' : a ≠ 2): False := by
  rw [← lt_self_iff_false (a * b)]
  calc a * b
      = c + d := h₁
    _ ≤ c + d + ((c - 1) * (d - 1) - 1) := by
      apply le_add_of_nonneg_right
      rw [sub_nonneg]
      nth_rw 1 [← one_mul 1]
      apply mul_le_mul <;> lia
    _ = c * d := by ring
    _ = a + b := h₂.symm
    _ < a + b + ((a - 1) * (b - 1) - 1) := by
      apply lt_add_of_pos_right
      apply Int.lt_of_le_sub_one
      rw [sub_nonneg, le_sub_iff_add_le, ← mul_one (1 + 1)]
      apply mul_le_mul <;> lia
    _ = a * b := by ring

abbrev SolutionSet : Set (ℤ × ℤ) := {
  (2, 2), (5, 3), (5, 2), (1, 3), (1, 2),
  (3, 5), (2, 5), (3, 1), (2, 1)
}

end Imo1994P4
