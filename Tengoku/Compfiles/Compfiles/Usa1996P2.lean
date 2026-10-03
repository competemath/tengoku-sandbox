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
# USA Mathematical Olympiad 1996, Problem 2

Let S be a set of n positive integers. Let P be the set of all integers which
are the sum of one or more distinct elements of S. Show that we can find n
subsets of P whose union is P such that if a, b belong to the same subset,
then a ≤ 2b.
-/

namespace Usa1996P2

/-- The set of all sums of one or more distinct elements of `S`. -/
def SubsetSums (S : Finset ℕ) : Set ℕ :=
  {x | ∃ A : Finset ℕ, A ⊆ S ∧ A.Nonempty ∧ x = A.sum id}

variable (S : Finset ℕ)

/-- The sum of the `m` smallest elements of `S`, taken in increasing order. -/
def prefixSum (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m), S.orderEmbOfFin rfl i

lemma prefixSum_zero : prefixSum S 0 = 0 := by
  rw [prefixSum, Finset.filter_false_of_mem (fun i _ ↦ Nat.not_lt_zero i.val),
    Finset.sum_empty]

lemma prefixSum_succ (m : ℕ) (hm : m < S.card) :
    prefixSum S (m + 1) = prefixSum S m + S.orderEmbOfFin rfl ⟨m, hm⟩ := by
  have hinsert : Finset.univ.filter (fun i : Fin S.card ↦ i.val < m + 1) =
      insert ⟨m, hm⟩ (Finset.univ.filter (fun i : Fin S.card ↦ i.val < m)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · intro h
      rcases h with rfl | h
      · exact Nat.lt_succ_self m
      · exact Nat.lt_succ_of_lt h
  have hnotmem : ⟨m, hm⟩ ∉ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m) := by
    simp
  show (∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m + 1),
      S.orderEmbOfFin rfl i) =
    (∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m), S.orderEmbOfFin rfl i) +
      S.orderEmbOfFin rfl ⟨m, hm⟩
  rw [hinsert, Finset.sum_insert hnotmem, add_comm]

lemma sum_eq_sum_univ : S.sum id = ∑ i : Fin S.card, S.orderEmbOfFin rfl i := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
  rw [Finset.sum_map]
  rfl

lemma prefixSum_card : prefixSum S S.card = S.sum id := by
  have h1 : Finset.univ.filter (fun i : Fin S.card ↦ i.val < S.card) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ ↦ i.isLt
  rw [prefixSum, h1, sum_eq_sum_univ]

/-- The sum over a subset `A` of `S` reindexed by the increasing enumeration of `S`. -/
lemma sum_eq_sum_filter (A : Finset ℕ) (hA : A ⊆ S) :
    A.sum id =
      ∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A),
        S.orderEmbOfFin rfl i := by
  have hmap : (Finset.univ.filter
        (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A)).map
      (S.orderEmbOfFin rfl).toEmbedding = A := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro ha
      have h : a ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hA ha
      obtain ⟨i, hi⟩ := h
      exact ⟨i, hi ▸ ha, hi⟩
  conv_lhs => rw [← hmap]
  rw [Finset.sum_map]
  rfl

/-- The key estimate: a subset sum strictly larger than the sum of the `m` smallest
elements must use some element with index at least `m`, hence is at least the `m`-th
smallest element, and twice the sum exceeds the `m + 1` prefix sum. -/
lemma prefixSum_succ_lt_two_mul_sum (A : Finset ℕ) (hAS : A ⊆ S)
    (m : ℕ) (hm : m < S.card) (hx : prefixSum S m < A.sum id) :
    prefixSum S (m + 1) < 2 * A.sum id := by
  have hsum : A.sum id =
      ∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A),
        S.orderEmbOfFin rfl i := sum_eq_sum_filter S A hAS
  have hex : ∃ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A),
      m ≤ i.val := by
    by_contra hcon
    push Not at hcon
    have hsub : Finset.univ.filter (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A) ⊆
        Finset.univ.filter (fun i : Fin S.card ↦ i.val < m) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcon i hi
    have hle : (∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ S.orderEmbOfFin rfl i ∈ A),
          S.orderEmbOfFin rfl i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m), S.orderEmbOfFin rfl i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
    have hprefix : prefixSum S m =
        ∑ i ∈ Finset.univ.filter (fun i : Fin S.card ↦ i.val < m),
          S.orderEmbOfFin rfl i := rfl
    rw [hsum] at hx
    lia
  obtain ⟨i, hiB, him⟩ := hex
  have hci : S.orderEmbOfFin rfl i ≤ A.sum id := by
    rw [hsum]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hiB
  have hle' : (⟨m, hm⟩ : Fin S.card) ≤ i := him
  have hcm : S.orderEmbOfFin rfl ⟨m, hm⟩ ≤ S.orderEmbOfFin rfl i :=
    (S.orderEmbOfFin rfl).strictMono.monotone hle'
  rw [prefixSum_succ S m hm]
  lia

end Usa1996P2
