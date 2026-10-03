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
# International Mathematical Olympiad 2003, Problem 5

Given n > 2 and reals x₁ ≤ x₂ ≤ ... ≤ xₙ, show that

  (∑ᵢⱼ |xᵢ - xⱼ|)² ≤ (2/3)(n² - 1) ∑ᵢⱼ (xᵢ - xⱼ)².

Show that we have equality iff the sequence is an arithmetic progression.
-/

namespace Imo2003P5

open Finset

/-
## Solution

Since the inequality only involves differences of the `xᵢ`, we may replace `xᵢ` by
`xᵢ - m` where `m` is the mean of the `xᵢ`, i.e. we may assume `∑ xᵢ = 0`.
Using that the sequence is nondecreasing, the sum of absolute differences is

  ∑ᵢⱼ |xᵢ - xⱼ| = 2 ∑ᵢ (2i + 1 - n) xᵢ          (0 ≤ i < n)

(proved below by induction on `n`), while

  ∑ᵢⱼ (xᵢ - xⱼ)² = 2n ∑ᵢ xᵢ² - 2 (∑ᵢ xᵢ)² = 2n ∑ᵢ xᵢ².

Cauchy-Schwarz gives

  (∑ᵢ (2i + 1 - n) xᵢ)² ≤ (∑ᵢ (2i + 1 - n)²) (∑ᵢ xᵢ²) = (n(n² - 1)/3) ∑ᵢ xᵢ²,

and the claim follows.
-/

theorem sum_range_id_real (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_sq_range (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The coefficients `2i + 1 - n` are centered: their sum vanishes. -/
theorem sum_coeff (n : ℕ) : ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) = 0 := by
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
    sum_range_id_real]
  ring

/-- The sum of the coefficients times the index. -/
theorem sum_coeff_mul (n : ℕ) :
    ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * (i : ℝ) = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 6 := by
  have exp : ∀ i : ℕ, (2 * (i : ℝ) + 1 - (n : ℝ)) * (i : ℝ)
      = 2 * (i : ℝ) ^ 2 + (1 - (n : ℝ)) * (i : ℝ) := fun i => by ring
  rw [sum_congr rfl fun i _ => exp i]
  simp only [sum_add_distrib, ← mul_sum, sum_sq_range, sum_range_id_real]
  ring

/-- The sum of the squared coefficients. -/
theorem sum_sq_coeff (n : ℕ) :
    ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  have exp : ∀ i : ℕ, (2 * (i : ℝ) + 1 - (n : ℝ)) ^ 2
      = 4 * (i : ℝ) ^ 2 + (4 - 4 * (n : ℝ)) * (i : ℝ) + (1 - (n : ℝ)) ^ 2 := fun i => by ring
  rw [sum_congr rfl fun i _ => exp i]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
    sum_sq_range, sum_range_id_real]
  ring

/-- The key identity for the sum of absolute differences of a nondecreasing sequence. -/
theorem sum_abs_diff : ∀ (n : ℕ) {x : ℕ → ℝ}, MonotoneOn x (range n) →
    ∑ i ∈ range n, ∑ j ∈ range n, |x i - x j| =
      2 * ∑ i ∈ range n, (2 * (i : ℝ) + 1 - (n : ℝ)) * x i := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have hsub : range k ⊆ range (k + 1) := fun a ha =>
      mem_range.mpr ((mem_range.mp ha).trans (Nat.lt_succ_self k))
    have hxk : MonotoneOn x (range k) := hx.mono hsub
    have habs : ∀ i ∈ range k, |x i - x k| = x k - x i := fun i hi => by
      have hle : x i ≤ x k := hx (mem_range.mpr ((mem_range.mp hi).trans (Nat.lt_succ_self k)))
        (mem_range.mpr (Nat.lt_succ_self k)) (mem_range.mp hi).le
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    have habs' : ∀ j ∈ range k, |x k - x j| = x k - x j := fun j hj =>
      abs_of_nonneg (sub_nonneg.mpr (hx (mem_range.mpr ((mem_range.mp hj).trans
        (Nat.lt_succ_self k))) (mem_range.mpr (Nat.lt_succ_self k)) (mem_range.mp hj).le))
    have split : ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), |x i - x j|
        = ∑ i ∈ range k, ∑ j ∈ range k, |x i - x j|
          + ∑ i ∈ range k, (x k - x i) + ∑ j ∈ range k, (x k - x j) := by
      calc ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1), |x i - x j|
          = (∑ i ∈ range k, (∑ j ∈ range k, |x i - x j| + |x i - x k|))
              + (∑ j ∈ range k, |x k - x j| + |x k - x k|) := by
            rw [sum_range_succ]
            congr 1
            · exact sum_congr rfl fun i _ => sum_range_succ _ _
            · exact sum_range_succ _ _
        _ = ∑ i ∈ range k, ∑ j ∈ range k, |x i - x j|
            + ∑ i ∈ range k, (x k - x i) + ∑ j ∈ range k, (x k - x j) := by
          rw [sum_add_distrib]
          have e3 : |x k - x k| = (0 : ℝ) := by rw [sub_self, abs_zero]
          rw [e3, add_zero, sum_congr rfl habs, sum_congr rfl habs', add_assoc]
    have rsplit : 2 * ∑ i ∈ range (k + 1), (2 * (i : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) * x i
        = 2 * (∑ i ∈ range k, (2 * (i : ℝ) + 1 - (k : ℝ)) * x i - ∑ i ∈ range k, x i
            + (k : ℝ) * x k) := by
      rw [sum_range_succ]
      have pt : ∀ i ∈ range k, (2 * (i : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) * x i
          = (2 * (i : ℝ) + 1 - (k : ℝ)) * x i - x i := fun i _ => by push_cast; ring
      rw [sum_congr rfl pt, sum_sub_distrib]
      push_cast
      ring
    have esum : ∑ i ∈ range k, (x k - x i) = (k : ℝ) * x k - ∑ i ∈ range k, x i := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [split, rsplit, esum, ih hxk]
    ring

/-- Expansion of the sum of squared differences. -/
theorem sum_sq_diff (n : ℕ) (x : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2
      = 2 * (n : ℝ) * ∑ i ∈ range n, x i ^ 2 - 2 * (∑ i ∈ range n, x i) ^ 2 := by
  have exp : ∀ i j : ℕ, (x i - x j) ^ 2 = x i ^ 2 - 2 * x i * x j + x j ^ 2 := fun i j => by ring
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => exp i j]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
    ← mul_sum, ← sum_mul]
  ring

end Imo2003P5
