/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 2012, Problem 2

Let a₂, a₃, ..., aₙ be positive reals with product 1, where n ≥ 3.
Show that
  (1 + a₂)²(1 + a₃)³...(1 + aₙ)ⁿ > nⁿ.
-/

namespace Imo2012P2

universe u v

lemma Finset.prod_eq_prod_iff_of_pos_of_le {ι : Type u} {R : Type v}
    [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]
    [PosMulStrictMono R] [MulPosStrictMono R] [Nontrivial R]
    [DecidableEq ι] {f g : ι → R} {s : Finset ι}
    (h₀ : ∀ i ∈ s, 0 < f i) (h₁ : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i = ∏ i ∈ s, g i ↔ ∀ i ∈ s, f i = g i := by
  constructor
  · intro h i hi
    rw [← Finset.insert_erase hi] at h
    repeat rw [Finset.prod_insert (Finset.notMem_erase i s)] at h
    have h' : ∏ x ∈ s.erase i, f x ≤ ∏ x ∈ s.erase i, g x := by
      apply Finset.prod_le_prod
      · intro i' hi'
        exact le_of_lt (h₀ i' (Finset.mem_of_mem_erase hi'))
      · intro i' hi'
        exact h₁ i' (Finset.mem_of_mem_erase hi')
    have h'' : 0 < ∏ x ∈ s.erase i, g x := by
      apply lt_of_le_of_lt' h'
      apply Finset.prod_pos
      intro i' hi'
      exact h₀ i' (Finset.mem_of_mem_erase hi')
    rw [mul_eq_mul_iff_eq_and_eq_of_pos (h₁ i hi) h' (h₀ i hi) h''] at h
    exact h.left
  · intro h
    exact Finset.prod_congr (by rfl) h

lemma Real.geom_mean_eq_arith_mean2_weighted_iff
    {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hw : w₁ + w₂ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ = w₁ * p₁ + w₂ * p₂ ↔ p₁ = p₂ := by
  have h' := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ ![w₁, w₂] ![p₁, p₂]
  simp at h'
  have h'' := h' hw₁ hw₂ hw (le_of_lt hp₁) (le_of_lt hp₂)
  rw [h'']
  constructor
  · intro h
    nth_rw 1 [h.left]
    nth_rw 2 [h.right]
  · intro h
    rw [h, ← add_mul, hw, one_mul]
    constructor <;> rfl

lemma aux₁ {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) ^ n = ∏ i ∈ Finset.Icc 2 n, (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) := by
  induction' n, hn using Nat.le_induction with n' hn' h'
  · norm_num
  · nth_rw 3 [← Nat.succ_eq_add_one]
    rw [← Nat.succ_eq_succ, ← Finset.insert_Icc_right_eq_Icc_succ (by lia : 2 ≤ n'.succ)]
    rw [Finset.prod_insert (by simp), Nat.succ_eq_succ, Nat.succ_eq_add_one, ← h']
    simp

lemma aux₂ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) :
    (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x =
    (i : ℝ) ^ i * (x ^ (1 / (i : ℝ)) * (1 / ((i : ℝ) - 1)) ^ (((i : ℝ) - 1) / (i : ℝ))) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
    rw [Nat.cast_pos]
    lia
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by lia), Nat.cast_pos]
    lia
  repeat rw [← Real.rpow_natCast]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) (by positivity)]
  rw [Real.one_rpow]
  repeat rw [div_mul_cancel₀ _ (by positivity)]
  field_simp
  rw [Real.rpow_one, mul_comm, Nat.cast_sub (by lia), Nat.cast_one]

lemma aux₃ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) : (1 + x) ^ i =
    (i : ℝ) ^ i * ((1 / (i : ℝ)) * x + (((i : ℝ) - 1) / (i : ℝ)) * (1 / ((i : ℝ) - 1))) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
    rw [Nat.cast_pos]
    lia
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by lia), Nat.cast_pos]
    lia
  repeat rw [← Real.rpow_natCast]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  field_simp
  ring_nf

lemma aux₄ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) :
    (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x ≤ (1 + x) ^ i := by
  have hpos₁ : 0 < (i : ℝ) := by
      rw [Nat.cast_pos]
      lia
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by lia), Nat.cast_pos]
    lia
  rw [aux₂ hi hx, aux₃ hi hx, mul_le_mul_iff_right₀ (by positivity)]
  rw [pow_le_pow_iff_left₀ (by positivity) (by positivity) (by lia)]
  apply Real.geom_mean_le_arith_mean2_weighted (by positivity) (by positivity) (by positivity) (by positivity)
  field

lemma aux₅ {i : ℕ} {x : ℝ} (hi : 2 ≤ i) (hx : 0 < x) :
    (i : ℝ) ^ i / ((i : ℝ) - 1) ^ (i - 1) * x = (1 + x) ^ i ↔ x = 1 / ((i : ℝ) - 1) := by
  have hpos₁ : 0 < (i : ℝ) := by
      rw [Nat.cast_pos]
      lia
  have hpos₂ : 0 < (i : ℝ) - 1 := by
    rw [← Nat.cast_one, ← Nat.cast_sub (by lia), Nat.cast_pos]
    lia
  rw [aux₂ hi hx, aux₃ hi hx, mul_left_cancel_iff_of_pos (by positivity)]
  repeat rw [← Real.rpow_natCast]
  rw [Real.rpow_left_inj (by positivity) (by positivity) (by positivity)]
  apply Real.geom_mean_eq_arith_mean2_weighted_iff (by positivity) (by positivity) (by positivity) (by positivity)
  field

lemma aux₆ {n : ℕ} (hn : 2 ≤ n) : ∏ x ∈ Finset.Icc 2 n, ((x : ℝ) - 1) = Nat.factorial (n - 1) := by
  induction' n, hn using Nat.le_induction with n' hn' h'
  · norm_num
  · nth_rw 1 [← Nat.succ_eq_add_one]
    rw [← Nat.succ_eq_succ, ← Finset.insert_Icc_right_eq_Icc_succ (by lia : 2 ≤ n'.succ)]
    rw [Finset.prod_insert (by simp), Nat.succ_eq_succ, Nat.succ_eq_add_one, h']
    push_cast
    field_simp
    ring_nf
    norm_cast
    rw [Nat.mul_factorial_pred (by lia: _)]

end Imo2012P2
