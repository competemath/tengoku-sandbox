/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2006, Problem 2

For a given positive integer k find, in terms of k, the minimum value
of N for which there is a set of 2k + 1 distinct positive integers
that has sum greater than N but every subset of size k has sum at
most N / 2.
-/

namespace Usa2006P2

abbrev solution : ℕ → ℕ := fun k ↦ 2 * k ^ 3 + 3 * k ^ 2 + 3 * k

-- Following https://web.evanchen.cc/exams/USAMO-2006-notes.pdf

/-- Lower bound for the sum of a finset of natural numbers bounded below:
if every element of `J` is at least `a`, then the sum of `J` is at least the
sum of the `J.card` smallest allowed values `a, a+1, ...`.
Equivalently `2 * ∑ j ∈ J, j ≥ J.card * (2 * a + (J.card - 1))`; we use this
formulation to avoid truncated subtraction. -/
lemma two_mul_sum_ge (J : Finset ℕ) (a : ℕ) (hJ : ∀ j ∈ J, a ≤ j) :
    J.card * (2 * a) + J.card ^ 2 ≤ 2 * ∑ j ∈ J, j + J.card := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    by_cases hne : J.Nonempty
    · set M := J.max' hne with hMdef
      have hMmem : M ∈ J := J.max'_mem hne
      have ih' := ih (J.erase M) (Finset.erase_ssubset hMmem)
        (fun j hj ↦ hJ j (Finset.mem_of_mem_erase hj))
      have hcard : (J.erase M).card + 1 = J.card := J.card_erase_add_one hMmem
      have hsum : M + ∑ j ∈ J.erase M, j = ∑ j ∈ J, j :=
        J.add_sum_erase (fun x => x) hMmem
      have hcardle : (J.erase M).card ≤ (Finset.Ico a M).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_erase] at hj
        have hj3 : j ≤ M := J.le_max' j hj.2
        rw [Finset.mem_Ico]
        exact ⟨hJ j hj.2, by lia⟩
      rw [Nat.card_Ico] at hcardle
      have haM : a ≤ M := hJ M hMmem
      have h2M : 2 * (J.erase M).card + 2 * a ≤ 2 * M := by lia
      rw [← hcard, ← hsum]
      linarith [ih', h2M]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- Upper bound for the sum of a finset of natural numbers bounded above:
if every element of `J` is at most `b`, then the sum of `J` is at most the
sum of the `J.card` largest allowed values `b, b-1, ...`.
Equivalently `2 * ∑ j ∈ J, j ≤ J.card * (2 * b + 1 - J.card)`; we use this
formulation to avoid truncated subtraction. -/
lemma two_mul_sum_le (J : Finset ℕ) (b : ℕ) (hJ : ∀ j ∈ J, j ≤ b) :
    2 * ∑ j ∈ J, j + J.card ^ 2 ≤ 2 * (J.card * b) + J.card := by
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    by_cases hne : J.Nonempty
    · set m₀ := J.min' hne with hm₀def
      have hm₀mem : m₀ ∈ J := J.min'_mem hne
      have ih' := ih (J.erase m₀) (Finset.erase_ssubset hm₀mem)
        (fun j hj ↦ hJ j (Finset.mem_of_mem_erase hj))
      have hcard : (J.erase m₀).card + 1 = J.card := J.card_erase_add_one hm₀mem
      have hsum : m₀ + ∑ j ∈ J.erase m₀, j = ∑ j ∈ J, j :=
        J.add_sum_erase (fun x => x) hm₀mem
      have hcardle : (J.erase m₀).card ≤ (Finset.Ioc m₀ b).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_erase] at hj
        have hj3 : m₀ ≤ j := J.min'_le j hj.2
        rw [Finset.mem_Ioc]
        exact ⟨by lia, hJ j hj.2⟩
      rw [Nat.card_Ioc] at hcardle
      have hm₀b : m₀ ≤ b := hJ m₀ hm₀mem
      have h2m : 2 * m₀ + 2 * (J.erase m₀).card ≤ 2 * b := by lia
      rw [← hcard, ← hsum]
      linarith [ih', h2m]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- Twice the sum `1 + 2 + ... + n`. -/
lemma two_mul_sum_Icc_one (n : ℕ) :
    2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by lia : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
    rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by lia : (1 : ℕ) ≤ n + 1)]
    linear_combination ih

-- We formalise "every subset of size k has sum at most N / 2" as
-- `2 * ∑ x ∈ t, x ≤ N`, which is equivalent for natural numbers.

end Usa2006P2
