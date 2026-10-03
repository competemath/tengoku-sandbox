/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1973, Problem 6

Let $a_1, a_2,\cdots, a_n$ be $n$ positive numbers,
and let $q$ be a given real number such that $0 < q < 1$. Find $n$ numbers $b_1, b_2, \cdots, b_n$ for which

(a) $a_k < b_k$ for $k=1,2,\cdots, n$,

(b) $q < \dfrac{b_{k+1}}{b_k}<\dfrac{1}{q}$ for $k=1,2,\cdots,n-1$,

(c) $b_1+b_2+\cdots+b_n < \dfrac{1+q}{1-q}(a_1+a_2+\cdots+a_n)$.

-/

namespace Imo1973P6

variable (n : ℕ) (a : Fin n → ℝ) (q : ℝ)

open Matrix

def m (_:ℕ) : ℕ → ℕ := fun i => i

theorem m_zero : m n 0 = 0 := by
  rfl

theorem m_nonzero (i) (hi1 : 0 < i) : 0 < m n i := hi1

def Q : Fin n → Fin n → ℝ := fun i j => q ^ m n (Int.natAbs (i.val - j.val))

theorem Q_diag_one : ∀ i, Q n q i i = 1 := by
  unfold Q
  simp [m_zero]

theorem Q_pos (hq : q ∈ Set.Ioo 0 1) : ∀ i j, 0 < Q n q i j := by
  unfold Q
  intro i j
  apply pow_pos
  grind only [= Set.mem_Ioo]

theorem Q_row_neighbour_quot (k) (_ : k+1<n) (j) (hq : q ∈ Set.Ioo 0 1) : ∃ f ∈ ({q, q⁻¹} : Finset _),
    Q n q ⟨k+1, by lia⟩ j = f * Q n q ⟨k, by lia⟩ j := by
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, ↓existsAndEq, true_and]
  unfold Q
  repeat rw [← mul_inv_eq_iff_eq_mul₀ (by grind [pow_ne_zero])]
  rw [← zpow_natCast, ← zpow_natCast, ← div_eq_mul_inv]
  rw [← zpow_sub₀ (by grind only [= Set.mem_Ioo])]
  nth_rw 2 [show q = q^(1 : ℤ) by simp]
  rw [show q⁻¹ = q^(-1 : ℤ) by simp]
  repeat rw [zpow_right_inj₀ (by grind) (by grind)]
  unfold Int.natAbs m
  split <;> split
  all_goals grind

theorem imo1973_p6_of_n_eq_one (hn : n = 1) (hq : q ∈ Set.Ioo 0 1) (apos : ∀ i, 0 < a i)
    : ∃ b : Fin n → ℝ,
      (∀ k, a k < b k)
    ∧ (∀ k, ∀ _ : k < n-1, (b ⟨k+1, by lia⟩) / (b ⟨k, by lia⟩) ∈ Set.Ioo q (1 / q))
    ∧ (∑ k, b k < (1+q) / (1-q) * ∑ k, a k) := by
  subst n
  simp only [Fin.forall_fin_one, Fin.isValue, tsub_self, not_lt_zero, one_div, Set.mem_Ioo,
    IsEmpty.forall_iff, implies_true, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    true_and]
  rw [Set.mem_Ioo] at hq
  have : 1 < (1 + q) / (1 - q) := by
    refine (one_lt_div ?_).mpr ?_ <;> linarith
  use fun _ => √((1+q) / (1-q)) * a 0
  and_intros
  · rw [lt_mul_iff_one_lt_left (apos 0)]
    refine (Real.lt_sqrt ?_).mpr ?_ <;> linarith
  · rw [mul_lt_mul_iff_left₀ (apos 0)]
    refine (Real.sqrt_lt' ?_).mpr ?_ <;> nlinarith

end Imo1973P6
