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
# USA Mathematical Olympiad 1994, Problem 1

a₁, a₂, a₃, ... are positive integers such that aₙ > aₙ₋₁ + 1.
Put bₙ = a₁ + a₂ + ... + aₙ. Show that there is always a square in the
range bₙ, bₙ+1, bₙ+2, ... , bₙ₊₁-1.
-/

namespace Usa1994P1

/-- If consecutive terms of `a` differ by more than one, then terms that are
`k` indices apart differ by at least `2 * k`. -/
lemma gap_lemma {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (i k : ℕ) :
    a i + 2 * k ≤ a (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 := h (i + k)
      calc a i + 2 * (k + 1) = a i + 2 * k + 2 := by ring
        _ ≤ a (i + k) + 2 := Nat.add_le_add_right ih 2
        _ ≤ a (i + k + 1) := by lia
        _ = a (i + (k + 1)) := by rw [Nat.add_assoc]

/-- The sum of the first `n + 1` terms is at most
`(n + 1) * (a n + 1) - (n + 1)^2`; we state it in an addition-only form. -/
lemma sum_bound {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), a i) + (n + 1) * (n + 1) ≤
      (n + 1) * (a n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 : (n + 1) * (a n + 2) ≤ (n + 1) * a (n + 1) :=
        mul_le_mul_right (gap_lemma h n 1) (n + 1)
      rw [Finset.sum_range_succ]
      nlinarith [ih, h2]

/-- The key estimate: `4 * bₙ ≤ (aₙ + 1)²`. -/
lemma key {a : ℕ → ℕ} (h : ∀ i, a i + 1 < a (i + 1)) (n : ℕ) :
    4 * (∑ i ∈ Finset.range (n + 1), a i) ≤ (a n + 1) ^ 2 := by
  have h2 := sum_bound h n
  zify at h2 ⊢
  nlinarith [sq_nonneg ((a n : ℤ) + 1 - 2 * ((n : ℤ) + 1))]

end Usa1994P1
