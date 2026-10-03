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
# International Mathematical Olympiad 1974, Problem 6

Let $P$ be a non-constant polynomial with integer coefficients. If $n(P)$ is
the number of different integers $k$ such that $(P(k))^2 = 1$, prove that
$n(P) - \deg(P) \leq 2$.

We formalize $n(P)$ as the cardinality (`Set.ncard`) of the set of integers
`k` with `P.eval k ^ 2 = 1`, and prove the equivalent inequality
`n(P) ≤ deg(P) + 2`.
-/

namespace Imo1974P6

open Polynomial

/-- The integers `k` with `Q.eval k = 0` are exactly the roots of `Q`. -/
theorem setOf_eval_eq_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0} = ↑(Q.roots.toFinset) := by
  ext k
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset]
  rw [mem_roots hQ, IsRoot.def]

/-- A nonzero integer polynomial has only finitely many integer roots. -/
theorem finite_eval_eq_zero {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0}.Finite := by
  rw [setOf_eval_eq_zero hQ]
  exact Finset.finite_toSet _

/-- A nonzero integer polynomial has at most `natDegree` distinct integer
roots. -/
theorem ncard_eval_eq_zero_le {Q : Polynomial ℤ} (hQ : Q ≠ 0) :
    {k : ℤ | Q.eval k = 0}.ncard ≤ Q.natDegree := by
  rw [setOf_eval_eq_zero hQ, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_roots' _)

/-- `P k = 1` means that `k` is a root of `P - 1`. -/
theorem setOf_eval_eq_one (P : Polynomial ℤ) :
    {k : ℤ | P.eval k = 1} = {k : ℤ | (P - 1).eval k = 0} := by
  ext k
  simp only [Set.mem_ofPred_eq, eval_sub, eval_one, sub_eq_zero]

/-- `P k = -1` means that `k` is a root of `P + 1`. -/
theorem setOf_eval_eq_neg_one (P : Polynomial ℤ) :
    {k : ℤ | P.eval k = -1} = {k : ℤ | (P + 1).eval k = 0} := by
  ext k
  simp only [Set.mem_ofPred_eq, eval_add, eval_one, add_eq_zero_iff_eq_neg]

/-- Key divisibility: if `P r = 1` and `P k = -1`, then `k - r ∣ 2`. -/
theorem sub_dvd_two {P : Polynomial ℤ} {r k : ℤ} (hr : P.eval r = 1)
    (hk : P.eval k = -1) : k - r ∣ 2 := by
  have h0 := sub_dvd_eval_sub k r P
  rw [hk, hr] at h0
  norm_num at h0
  exact h0

/-- Main step: if `r` is a least integer with `P r = ±1` and `P r = 1`, then
at most `deg P + 2` integers satisfy `P k = ±1`. -/
theorem ncard_le_of_exists_min {P : Polynomial ℤ} (hP : 0 < P.natDegree) {r : ℤ}
    (hmin : ∀ k : ℤ, P.eval k = 1 ∨ P.eval k = -1 → r ≤ k) (hr : P.eval r = 1) :
    ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).ncard ≤ P.natDegree + 2 := by
  have hP1 : P - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, natDegree_one] at hP
    exact (Nat.lt_irrefl 0 hP).elim
  have hdeg1 : (P - 1).natDegree = P.natDegree := by
    refine natDegree_sub_eq_left_of_natDegree_lt ?_
    rw [natDegree_one]
    exact hP
  -- At most `deg P` integers satisfy `P k = 1`.
  have hA : {k : ℤ | P.eval k = 1}.ncard ≤ P.natDegree := by
    rw [setOf_eval_eq_one, ← hdeg1]
    exact ncard_eval_eq_zero_le hP1
  -- At most two integers satisfy `P k = -1`, namely `r + 1` and `r + 2`.
  have hsub : {k : ℤ | P.eval k = -1} ⊆ {r + 1, r + 2} := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    have hle : r ≤ k := hmin k (Or.inr hk)
    have hne : k ≠ r := by
      rintro rfl
      rw [hr] at hk
      norm_num at hk
    have hdvd : k - r ∣ 2 := sub_dvd_two hr hk
    have hpos : 0 < k - r := by lia
    have hle2 : k - r ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    have hmem : k = r + 1 ∨ k = r + 2 := by lia
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hB : {k : ℤ | P.eval k = -1}.ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)).trans
      (le_of_eq (Set.ncard_pair (by lia)))
  calc ({k : ℤ | P.eval k = 1} ∪ {k : ℤ | P.eval k = -1}).ncard
      ≤ {k : ℤ | P.eval k = 1}.ncard + {k : ℤ | P.eval k = -1}.ncard :=
        Set.ncard_union_le _ _
    _ ≤ P.natDegree + 2 := Nat.add_le_add hA hB

end Imo1974P6
