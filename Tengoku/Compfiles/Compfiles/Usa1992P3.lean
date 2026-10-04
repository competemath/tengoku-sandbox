/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1992, Problem 3

A set of 11 distinct positive integers has the property that we can find a
subset with sum n for any n between 1 and 1500 inclusive. What is the smallest
possible value for the second largest element?
-/

namespace Usa1992P3

/--
If the values `a 0, …, a 10` are strictly increasing, then `a` is monotone
on the interval `[0, 10]`.
-/
lemma monotone_of_consec_lt (a : ℕ → ℕ) (h : ∀ i, i < 10 → a i < a (i + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 10) : a i ≤ a j := by
  have aux : ∀ k : ℕ, i + k ≤ 10 → a i ≤ a (i + k) := by
    intro k
    induction k with
    | zero => intro; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := ih (by lia)
      have h2 := h (i + k) (by lia)
      rw [show i + (k + 1) = i + k + 1 by ring]
      exact le_trans h1 (le_of_lt h2)
  have e : i + (j - i) = j := by lia
  have h3 := aux (j - i) (by lia)
  rwa [e] at h3

/--
The key gap lemma: writing `s j` for the sum of the `j` smallest elements,
if `s j < 1500` then the next element satisfies `a j ≤ s j + 1`.
Indeed, `s j + 1 ≤ 1500` must occur as a subset sum, and any subset with
that sum must contain some `a i` with `i ≥ j`, so `a j ≤ a i ≤ s j + 1`.
-/
lemma gap (a : ℕ → ℕ)
    (hsub : ∀ n : ℕ, 1 ≤ n → n ≤ 1500 →
      ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n)
    (hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ 10 → a i ≤ a j)
    {j : ℕ} (_hj : j ≤ 10)
    (hs : ∑ i ∈ Finset.range j, a i < 1500) :
    a j ≤ ∑ i ∈ Finset.range j, a i + 1 := by
  obtain ⟨t, ht, htsum⟩ :=
    hsub (∑ i ∈ Finset.range j, a i + 1) (by lia) (by lia)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i ∈ t, i < j := by
    intro i hi
    by_contra hij
    push Not at hij
    have hi10 : i ≤ 10 := by
      have h11 : i < 11 := Finset.mem_range.mp (ht hi)
      lia
    have hge : a j ≤ a i := hmono hij hi10
    have hle : a i ≤ ∑ x ∈ t, a x :=
      Finset.single_le_sum (fun x _ ↦ Nat.zero_le _) hi
    lia
  have htr : t ⊆ Finset.range j := fun i hi ↦ Finset.mem_range.mpr (hlt i hi)
  have hle2 : ∑ i ∈ t, a i ≤ ∑ i ∈ Finset.range j, a i :=
    Finset.sum_le_sum_of_subset htr
  lia

/--
Induction using the gap lemma: the sum of the `k` smallest elements is at
most `2 ^ k - 1`, for every `k ≤ 10`.
-/
lemma pow_bound (a : ℕ → ℕ)
    (hsub : ∀ n : ℕ, 1 ≤ n → n ≤ 1500 →
      ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n)
    (hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ 10 → a i ≤ a j) :
    ∀ k : ℕ, k ≤ 10 → ∑ i ∈ Finset.range k, a i ≤ 2 ^ k - 1 := by
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by lia)
    have hpow : (2 : ℕ) ^ k ≤ 2 ^ 9 := pow_le_pow_right' (by norm_num) (by lia)
    have hlt : ∑ i ∈ Finset.range k, a i < 1500 := by lia
    have hgap := gap a hsub hmono (j := k) (by lia) hlt
    rw [Finset.sum_range_succ]
    have _ : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    have hX : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
    lia

/--
Formalization of "a set of 11 distinct positive integers such that every
integer between 1 and 1500 is the sum of a subset", with the elements listed
in increasing order as `a 0 < a 1 < … < a 10`.
-/
def Good (a : ℕ → ℕ) : Prop :=
  (∀ i : ℕ, i < 11 → 0 < a i) ∧
  (∀ i : ℕ, i < 10 → a i < a (i + 1)) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ 1500 → ∃ t : Finset ℕ, t ⊆ Finset.range 11 ∧ ∑ i ∈ t, a i = n

/-- The answer to the problem. -/
abbrev answer : ℕ := 248

end Usa1992P3
