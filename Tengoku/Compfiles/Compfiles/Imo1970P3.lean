/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Ortega
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1970, Problem 3

 The real numbers a₀, a₁, a₂, ... satisfy 1 = a₀ ≤ a₁ ≤ a₂ ≤ ... . b₁, b₂, b₃, ... are defined by bₙ = ∑_{k=1}^{n} (1 - a_{k-1}/a_k)/√a_k.

(a)  Prove that 0 ≤ bₙ < 2.

(b)  Given c satisfying 0 ≤ c < 2, prove that we can find an so that bₙ > c for all sufficiently large n.
-/

namespace Imo1970P3

open scoped Real

/-- A sequence of real numbers satisfying the given conditions -/
structure IncreasingSequenceFromOne where
  a : ℕ → ℝ
  a_zero : a 0 = 1
  a_mono : Monotone a

/-- The b_n sequence defined in terms of the a sequence -/
noncomputable def b_seq (seq : IncreasingSequenceFromOne) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 - seq.a k / seq.a (k + 1)) / √ (seq.a (k + 1))

def ValidBounds : Set ℝ :=
  { b | 0 ≤ b ∧ b < 2 }

/-- Helper: c_k = √(a_k) -/
noncomputable def c_seq (seq : IncreasingSequenceFromOne) (k : ℕ) : ℝ := Real.sqrt (seq.a k)

/-- All elements of the sequence are positive -/
lemma seq_pos (seq: IncreasingSequenceFromOne) : ∀ n, 0 < seq.a n := by
  intro n
  induction n with
  | zero =>
    rw [seq.a_zero]
    exact zero_lt_one
  | succ n ih =>
    have h1 : seq.a n ≤ seq.a (n + 1) := seq.a_mono (Nat.le_succ n)
    exact lt_of_lt_of_le ih h1

/-- Key lemma: each term is bounded by 2(1/c_{k-1} - 1/c_k) -/
lemma term_bound (seq : IncreasingSequenceFromOne) (k : ℕ) :
  (1 - seq.a (k - 1) / seq.a k) / Real.sqrt (seq.a k) ≤
  2 * (1 / c_seq seq (k - 1) - 1 / c_seq seq k) := by
  -- Let c_k = √(a_k)
  have ck_pos : ∀ j, 0 < c_seq seq j := fun j => Real.sqrt_pos.mpr (seq_pos seq j)
  have ck_is_ak_squared: ∀ j, seq.a j = (c_seq seq j)^2 := by
    intro j
    simp [c_seq, Real.sq_sqrt (le_of_lt (seq_pos seq j))]

  have hcseq : c_seq seq (k - 1) ≤ c_seq seq k := Real.sqrt_le_sqrt (seq.a_mono (Nat.sub_le k 1))

  -- The term equals c_{k-1}²/c_k · (1/a_{k-1} - 1/a_k)
  have h1 : (1 - seq.a (k - 1) / seq.a k) / Real.sqrt (seq.a k) = (c_seq seq (k - 1))^2 / c_seq seq k * (1 / seq.a (k - 1) - 1 / seq.a k) := by
    simp [c_seq, Real.sq_sqrt (le_of_lt (seq_pos seq _))]
    have haUnit : IsUnit (seq.a (k - 1)) := by
      rw [isUnit_iff_ne_zero]
      let j := k - 1
      have hj : j = k-1 := rfl
      rw [← hj]
      have := seq_pos seq j
      linarith
    ring_nf
    simp [field]
    rw [IsUnit.div_mul_left haUnit]
    exact inv_eq_one_div √(seq.a k)

  -- Factor 1/a_{k-1} - 1/a_k using difference of squares
  have h2 : 1 / seq.a (k - 1) - 1 / seq.a k =
    (1 / c_seq seq (k - 1) + 1 / c_seq seq k) * (1 / c_seq seq (k - 1) - 1 / c_seq seq k) := by
    rw [ck_is_ak_squared (k-1), ck_is_ak_squared k]
    ring

  -- Show c_{k-1}²/c_k · (1/c_{k-1} + 1/c_k) ≤ 2
  have h3 : (c_seq seq (k - 1))^2 / c_seq seq k * (1 / c_seq seq (k - 1) + 1 / c_seq seq k) ≤ 2 := by
    calc
      _ = c_seq seq (k - 1) / c_seq seq k + (c_seq seq (k - 1) / c_seq seq k)^2 := by
        have := ck_pos k
        have := ck_pos (k - 1)
        field_simp
      _ ≤ 1 + 1 := by
        apply add_le_add
        · exact (div_le_one (ck_pos k)).mpr hcseq
        · rw [sq_le_one_iff_abs_le_one, abs_div, abs_of_pos (ck_pos (k-1)), abs_of_pos (ck_pos k)]
          exact (div_le_one (ck_pos k)).mpr hcseq
      _ = 2 := one_add_one_eq_two

  rw [h1, h2, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right h3
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (ck_pos (k - 1)) hcseq

end Imo1970P3
