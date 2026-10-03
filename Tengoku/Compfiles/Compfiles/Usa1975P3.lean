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
# USA Mathematical Olympiad 1975, Problem 3

A polynomial p(x) of degree n satisfies p(0) = 0, p(1) = 1/2, p(2) = 2/3, ... ,
p(n) = n/(n+1). Find p(n+1).
-/

namespace Usa1975P3

open Polynomial

noncomputable abbrev answer (n : ℕ) : ℝ := if Odd n then 1 else (n : ℝ) / (n + 2)

/-- The degree of `∏_{i < m} (X - i)` is `m`. -/
lemma natDegree_prod_X_sub_C (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).natDegree = m := by
  have hdeg : (∏ i ∈ Finset.range m, (X - C (i : ℝ))).natDegree =
      ∑ i ∈ Finset.range m, (X - C (i : ℝ)).natDegree :=
    natDegree_prod _ _ fun i _ ↦ X_sub_C_ne_zero _
  rw [hdeg]
  trans ∑ i ∈ Finset.range m, (1 : ℕ)
  · exact Finset.sum_congr rfl fun x _ ↦ natDegree_X_sub_C _
  · simp

/-- `∏_{i < m} (i + 1) = m!`, cast to the reals. -/
lemma prod_range_add_one_cast (m : ℕ) :
    ∏ i ∈ Finset.range m, ((i : ℝ) + 1) = (Nat.factorial m : ℝ) := by
  exact_mod_cast Finset.prod_range_add_one_eq_factorial m

/-- `∏_{i < m} (X - i)` evaluated at `-1` equals `(-1)^m * m!`. -/
lemma eval_prod_X_sub_C_neg_one (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).eval (-1 : ℝ) = (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) := by
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have h2 : ∀ i ∈ Finset.range m, ((-1 : ℝ) - (i : ℝ)) = (-1) * ((i : ℝ) + 1) :=
    fun i _ ↦ by ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    prod_range_add_one_cast]

/-- `∏_{i < m} (X - i)` evaluated at `m` equals `m!`. -/
lemma eval_prod_X_sub_C_self (m : ℕ) :
    (∏ i ∈ Finset.range m, (X - C (i : ℝ))).eval (m : ℝ) = (Nat.factorial m : ℝ) := by
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have e : ∏ i ∈ Finset.range m, ((m : ℝ) - (i : ℝ)) = ∏ i ∈ Finset.range m, ((i : ℝ) + 1) := by
      rw [← Finset.prod_range_reflect (fun i ↦ (i : ℝ) + 1) m]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      show ((m : ℝ) - (j : ℝ)) = ((m - 1 - j : ℕ) : ℝ) + 1
      rw [Nat.cast_sub (by lia : j ≤ m - 1), Nat.cast_sub (by lia : 1 ≤ m)]
      push_cast
      ring
    rw [e, prod_range_add_one_cast]

end Usa1975P3
