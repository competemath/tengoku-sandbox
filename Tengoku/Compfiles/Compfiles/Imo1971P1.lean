/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francesco Cappetti
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1971, Problem 1

Prove that the following assertion is true for n = 3 and n = 5, and that it is
false for every other natural number n > 2:

If a1, a2, ..., an are arbitrary real numbers, then
(a1 − a2)(a1 − a3) · · · (a1 − an) + (a2 − a1)(a2 − a3) · · · (a2 − an)
+ · · · + (an − a1)(an − a2) · · · (an − an−1) ≥ 0
-/

namespace Imo1971P1

def E {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∏ j ≠ i, (a i - a j)

def P (n : ℕ) : Prop :=
  ∀ (a : Fin n → ℝ), E a ≥ 0

-- This makes working with the sum easier and simp more powerful.
lemma prod_ne_eq_prod_ite {n : ℕ} {i : Fin n} {a : Fin n → ℝ} : ∏ j ≠ i, (a i - a j) = ∏ j, if j = i then 1 else a i - a j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  grind [Finset.prod_congr]

-- A proof that E a = E b, where b is obtained by permuting a's indices.
lemma E_equiv_perm {n : ℕ} {a b : Fin n → ℝ} (h : ∃ σ : Equiv.Perm (Fin n), b = a ∘ σ) : E a = E b := by
  obtain ⟨σ, hσ⟩ := h
  simp [E]
  apply Finset.sum_equiv (e := σ.symm) (by simp)
  intro i hi
  apply Finset.prod_equiv (e := σ.symm) (by simp)
  intro j hj
  simp [hσ, Equiv.apply_symm_apply]

-- This gets a permutation of the indices of a such that the resulting sequence is antitone.
-- Uses Tuple.sort (which gives monotone) composed with Fin.revPerm (which reverses) to get antitone.
lemma antitone_of_monotone_comp_rev {n : ℕ} (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hm : Monotone (f ∘ σ)) : Antitone (f ∘ σ ∘ Fin.revPerm) := by
  intro i j hij
  simp only [Function.comp_apply]
  exact hm (by simp [Fin.revPerm_apply, Fin.rev_le_rev, hij])

lemma exists_antitone_perm {n : ℕ} (a : Fin n → ℝ) :
    ∃ b, ∃ σ : Equiv.Perm (Fin n), b = a ∘ σ ∧ Antitone b := by
  let σ : Equiv.Perm (Fin n) := Tuple.sort a * Fin.revPerm
  use a ∘ σ, σ
  constructor
  · rfl
  · simp only [σ, Equiv.Perm.coe_mul, Function.comp_def]
    exact antitone_of_monotone_comp_rev a _ (Tuple.monotone_sort a)

end Imo1971P1
