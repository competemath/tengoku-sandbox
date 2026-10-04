/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1971, Problem 6

Let $A = (a_{ij})$ be an $n \times n$ matrix with non-negative integer entries.
Suppose that for all $i, j$, if $a_{ij} = 0$, then the sum of the elements in the
$i$-th row plus the sum of the elements in the $j$-th column is at least $n$.
Prove that the sum of all elements in the matrix is at least $n^2 / 2$.

-/

namespace Imo1971P6

open BigOperators Matrix

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)

-- Definitions of row sum, column sum, and total sum
def rowSum (i : Fin n) : ℕ := ∑ j, A i j
def colSum (j : Fin n) : ℕ := ∑ i, Aᵀ j i
def totalSum : ℕ := ∑ i, ∑ j, A i j

-- Basic lemmas connecting total sum to row/col sums
lemma totalSum_eq_rowSum_sum : totalSum A = ∑ i, rowSum A i := rfl

lemma totalSum_eq_colSum_sum : totalSum A = ∑ j, colSum A j := Finset.sum_comm

theorem totalSum_transpose_eq : totalSum A = totalSum Aᵀ := by
  simp [totalSum, Matrix.transpose]
  exact Finset.sum_comm

/-- Auxiliary lemma: The inequality holds if there exists a row with sum `x`
    such that `x` is less than or equal to all row sums and column sums. -/
lemma aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (n_pos : 0 < n)
    (h_cond : ∀ i j : Fin n, A i j = 0 → rowSum A i + colSum A j ≥ n)
    (x : ℕ)
    (h_min_row : ∀ i, x ≤ rowSum A i)
    (h_min_col : ∀ j, x ≤ colSum A j)
    (h_exists_row : ∃ i, rowSum A i = x) :
    2 * totalSum A ≥ n^2 := by
  obtain ⟨i₀, h_xi0⟩ := h_exists_row
  by_cases h_x_large : n ≤ 2 * x
  · -- Case 1: x ≥ n/2
    have h_total_ge_nx : totalSum A ≥ n * x := calc
      totalSum A = ∑ i, rowSum A i := totalSum_eq_rowSum_sum A
      _ ≥ ∑ i, x := Finset.sum_le_sum (fun i _ => h_min_row i)
      _ = n * x := by simp
    zify at h_total_ge_nx h_x_large ⊢; nlinarith
  · -- Case 2: x < n/2
    push Not at h_x_large
    let Y := (Finset.univ : Finset (Fin n)).filter (fun j => A i₀ j ≠ 0)
    let y := Y.card
    have h_y_le_x : y ≤ x := by
      rw [← h_xi0, rowSum]
      calc y = ∑ j ∈ Y, 1 := by simp [y]
        _ ≤ ∑ j ∈ Y, A i₀ j := Finset.sum_le_sum (fun j hj =>
            Nat.one_le_iff_ne_zero.mpr (by simp [Y] at hj; exact hj))
        _ ≤ ∑ j, A i₀ j := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ Y) (fun _ _ _ => Nat.zero_le _)

    rw [totalSum_eq_colSum_sum A]
    have h_split : ∑ j, colSum A j = (∑ j ∈ Y, colSum A j) + (∑ j ∈ Yᶜ, colSum A j) := by
      rw [← Finset.sum_add_sum_compl Y]
    rw [h_split]

    have h_bound : (∑ j ∈ Y, colSum A j) + (∑ j ∈ Yᶜ, colSum A j) ≥ y * x + (n - y) * (n - x) := by
      apply add_le_add
      · have h_yx : y * x = ∑ j ∈ Y, x := by simp [y, Finset.sum_const]
        rw [h_yx]; apply Finset.sum_le_sum; intro j _; exact h_min_col j
      · have h_col_Yc (j : Fin n) (hj : j ∈ Yᶜ) : colSum A j ≥ n - x := by
          have h_zero : A i₀ j = 0 := by simp [Y] at hj; exact hj
          have h_app := h_cond i₀ j h_zero; rw [h_xi0] at h_app; lia
        have h_nx : (n - y) * (n - x) = ∑ j ∈ Yᶜ, (n - x) := by simp [y, Finset.card_compl]
        rw [h_nx]; exact Finset.sum_le_sum h_col_Yc

    zify at h_y_le_x h_bound h_x_large ⊢
    have h_nx_cast : (↑(n - x) : ℤ) = ↑n - ↑x := Int.ofNat_sub (by linarith)
    have h_ny_cast : (↑(n - y) : ℤ) = ↑n - ↑y := Int.ofNat_sub (by linarith)
    rw [h_nx_cast, h_ny_cast] at h_bound
    nlinarith

end Imo1971P6
