/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1998, Problem 1

Suppose that the set { 1, 2, ..., 1998 } has been partitioned into disjoint
pairs {aᵢ, bᵢ}, where 1 ≤ i ≤ 999, so that for all i, |aᵢ - bᵢ| = 1 or 6.

Prove that the sum

  |a₁ - b₁| + |a₂ - b₂| + ... + |a₉₉₉ - b₉₉₉|

ends in the digit 9.
-/

namespace Usa1998P1

lemma zmod_eq (a b c : ℤ) : a ≡ b [ZMOD c] ↔ a % c = b % c := by rfl

lemma mod2_abs (a : ℤ) : |a| % 2 = a % 2 := by
  obtain h | h := abs_cases a <;> rw [h.1]
  rw [Int.neg_emod_two]

-- For integers M,N we have |M-N| ≡ M-N ≡ M+N MOD 2.
lemma mod2_diff (a b : ℤ) : |a - b| % 2 = (a + b) % 2 := by
  rw [mod2_abs, Int.sub_eq_add_neg, Int.add_emod, Int.neg_emod_two, ← Int.add_emod]

lemma lemma0 (n : ℕ) : (∑ x ∈ Finset.Icc 1 (4 * n + 2), (x:ℤ) % 2) % 2 = 1 := by
  norm_cast
  induction n with
  | zero => simp +arith +decide
  | succ n ih =>
    rw [show 4 * (n + 1) + 2 = (4 * n + 2) + 4 by lia]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [Finset.sum_Icc_succ_top (by norm_num)]
    lia

end Usa1998P1
