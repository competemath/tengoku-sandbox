/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2009, Problem 1

Let $n$ be a positive integer and let $a_1, a_2, \ldots, a_k$ ($k \ge 2$) be
distinct integers in the set $\{1, 2, \ldots, n\}$ such that $n$ divides
$a_i(a_{i+1} - 1)$ for $i = 1, 2, \ldots, k - 1$. Prove that $n$ does not
divide $a_k(a_1 - 1)$.
-/

namespace Imo2009P1

/-- Telescoping: if `c j * c (j+1) = c j` for all `j`, then the product of any
window `c i, c (i+1), …, c (i+m)` collapses to its first term `c i`. -/
lemma telescope {R : Type*} [CommMonoid R] (c : ℕ → R)
    (hc : ∀ j, c j * c (j + 1) = c j) :
    ∀ m i, ∏ x ∈ Finset.range (m + 1), c (i + x) = c i := by
  intro m i
  induction m with
  | zero => simp
  | succ m ih =>
    rwa [Finset.prod_range_succ, Finset.prod_range_succ, mul_assoc,
        ← add_assoc, hc (i + m), ← Finset.prod_range_succ]

/-- If the relation `c j * c (j+1) = c j` holds and `c` is periodic with period
`k ≥ 1`, then `c` is constant: `c i = c (i+1)` for all `i`. -/
lemma const_of_cyclic {R : Type*} [CommMonoid R] (c : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hc : ∀ j, c j * c (j + 1) = c j) (hper : ∀ i, c i = c (i + k)) :
    ∀ i, c i = c (i + 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
  intro i
  have hφi : ∏ x ∈ Finset.range (k' + 1), c (i + x) = c i := telescope c hc k' i
  have hφi1 : ∏ x ∈ Finset.range (k' + 1), c (i + 1 + x) = c (i + 1) :=
    telescope c hc k' (i + 1)
  rw [← hφi, ← hφi1, Finset.prod_range_succ', Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro x _
    rw [add_comm x, add_assoc]
  · rw [Nat.add_zero, show i + 1 + k' = i + (k' + 1) by ring]
    exact hper i

end Imo2009P1
