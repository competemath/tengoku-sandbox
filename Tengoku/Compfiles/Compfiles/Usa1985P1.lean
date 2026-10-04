/-
Copyright (c) 2024 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1985, Problem 1

Determine whether or not there are any positive integral solutions of
the simultaneous equations

          x₁² + x₂² + ⋯ + x₁₉₈₅² = y³
          x₁³ + x₂³ + ⋯ + x₁₉₈₅³ = z²

with distinct integers x₁, x₂, ⋯, x₁₉₈₅.
-/

namespace Usa1985P1

lemma nicomachus (n : ℕ) :
    ∑ i ∈ Finset.range n, i^3 = (∑ i ∈ Finset.range n, i)^2 := by
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
  have h1 : ((∑ x ∈ Finset.range n, x) + n) ^ 2 =
      ((∑ x ∈ Finset.range n, x))^2 +
         (2 * (∑ x ∈ Finset.range n, x) * n +
           n ^ 2) := by ring
  rw [h1]
  have h2 : n ^ 3 = 2 * (∑ x ∈ Finset.range n, x) * n + n ^ 2 := by
    have h5 : 2 * ∑ x ∈ Finset.range n, x =
               (∑ x ∈ Finset.range n, x) * 2 := mul_comm _ _
    rw [h5, Finset.sum_range_id_mul_two]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      ring
  lia

lemma nicomachus' (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i:ℤ) + 1)^3 =
    (∑ i ∈ Finset.range n, ((i:ℤ) + 1))^2 := by
  norm_cast
  have h1 := nicomachus (n + 1)
  simp only [Finset.sum_range_succ', add_zero] at h1
  exact h1

abbrev does_exist : Bool := true

abbrev is_valid (x : ℕ → ℤ) (y z : ℤ) : Prop :=
    (∀ i ∈ Finset.range 1985, 0 < x i) ∧
    0 < y ∧ 0 < z ∧
    ∑ i ∈ Finset.range 1985, x i ^ 2 = y ^ 3 ∧
    ∑ i ∈ Finset.range 1985, x i ^ 3 = z ^ 2 ∧
    ∀ i ∈ Finset.range 1985, ∀ j ∈ Finset.range 1985, i ≠ j → x i ≠ x j

end Usa1985P1
