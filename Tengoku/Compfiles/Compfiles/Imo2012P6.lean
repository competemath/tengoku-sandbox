/-
Copyright (c) 2023 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh, Codex
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2012, Problem 6

Find all positive integers n for which there exist non-negative
integers a₁, a₂, ..., aₙ such that
1/2^a₁ + 1/2^a₂ + ··· + 1/2^aₙ = 1/3^a₁ + 2/3^a₂ + ··· + n/3^aₙ = 1
-/

namespace Imo2012P6

abbrev solution_set : Set ℕ := { n : ℕ | n % 4 = 1 ∨ n % 4 = 2 }

def IsSolution (n : ℕ) : Prop := ∃ a : ℕ → ℕ, 0 < n ∧
  (∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / (2 ^ a i)) = 1 ∧
  (∑ i ∈ Finset.Icc 1 n, (i : ℚ) / (3 ^ a i)) = 1

lemma sum_id {n : ℕ} : ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) / 2 := by
  have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext i
    simp [Finset.mem_Icc, Nat.succ_le_iff, Nat.pos_iff_ne_zero]
  rw [hIcc, Finset.sum_erase] <;> simp [Finset.sum_range_id, Nat.mul_comm]

lemma solution_5 : IsSolution 5 := by
  use fun i ↦ if i ∈ Finset.Ico 1 4 then 2 else if i ∈ Finset.Icc 4 5 then 3 else 0
  constructor
  · decide
  · constructor <;> rw [show Finset.Icc 1 5 = {1, 2, 3, 4, 5} by decide] <;> norm_num

lemma solution_9 : IsSolution 9 := by
  use fun i ↦ if i ∈ Finset.Ico 1 2 then 2 else if i ∈ Finset.Ico 2 6 then 3 else if i ∈ Finset.Icc 6 9 then 4 else 0
  decide_cbv

-- If n=4k+1 is a solution then n=4k+2 is also a solution.
lemma ind_4k1_to_4k2 : ∀ k, IsSolution (4 * k + 1) → IsSolution (4 * k + 2) := by
  intro k hk
  obtain ⟨a, hpos, ha₁, ha₂⟩ := hk
  let R : Finset ℕ := Finset.Icc 1 (4 * k + 1)
  let j : ℕ := 2 * k + 1
  let b : ℕ → ℕ := fun i ↦ if i = j then a j + 1 else if i = 4 * k + 2 then a j + 1 else a i
  have hjmem : j ∈ R := by grind
  refine ⟨b, by lia, ?_, ?_⟩
  · rw [Finset.sum_Icc_succ_top (by lia) (fun i ↦ (1 : ℚ) / 2 ^ b i)]
    have : ∑ x ∈ R.erase j, (1 : ℚ) / 2 ^ b x = ∑ x ∈ R.erase j, (1 : ℚ) / 2 ^ a x := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]
  · rw [Finset.sum_Icc_succ_top (by lia) (fun i ↦ (i : ℚ) / 3 ^ b i)]
    have : ∑ x ∈ R.erase j, (x : ℚ) / 3 ^ b x = ∑ x ∈ R.erase j, (x : ℚ) / 3 ^ a x := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]

-- If n=4k+1 is a solution then n=4k+13 is also a solution.
lemma ind_4k1_to_4k13 : ∀ k, IsSolution (4 * k + 1) → IsSolution (4 * k + 13) := by
  intro k hk
  obtain ⟨a, hpos, ha₁, ha₂⟩ := hk
  let j : ℕ := k + 1
  let b : ℕ → ℕ := fun i ↦
    if i = j then a j + 2 else
    if i ≤ 4 * k + 1 then a i else
    if i ≤ 4 * k + 2 then a j + 2 else
    if i ≤ 4 * k + 4 then a j + 3 else
    if i ≤ 4 * k + 7 then a j + 6 else
    if i ≤ 4 * k + 8 then a j + 5 else
    if i ≤ 4 * k + 11 then a j + 6 else
    if i ≤ 4 * k + 13 then a j + 4 else
    a i
  let R : Finset ℕ := Finset.Icc 1 (4 * k + 1)
  have htmem : k + 1 ∈ R := by grind

  refine ⟨b, by grind, ?_, ?_⟩
  · iterate 12
      rw [Finset.sum_Icc_succ_top (by grind) (fun i ↦ (1 : ℚ) / 2 ^ b i)]
    have : ∑ i ∈ R.erase (k + 1), (1 : ℚ) / 2 ^ b i = ∑ i ∈ R.erase (k + 1), (1 : ℚ) / 2 ^ a i := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]
  · iterate 12
      rw [Finset.sum_Icc_succ_top (by grind) (fun i ↦ (i : ℚ) / 3 ^ b i)]
    have : ∑ i ∈ R.erase (k + 1), (i : ℚ) / 3 ^ b i = ∑ i ∈ R.erase (k + 1), (i : ℚ) / 3 ^ a i := by
      apply Finset.sum_congr rfl
      grind
    grind only [Finset.add_sum_erase]

end Imo2012P6
