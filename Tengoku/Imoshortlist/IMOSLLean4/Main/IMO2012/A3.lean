/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

/-!
# IMO 2012 A3 (P2)

Let $R$ be a totally ordered commutative ring and $x_0, x_1, …, x_n ∈ R$
  (with $n ≥ 1$) be positive elements such that $x_0 x_1 … x_n = 1$.
Prove that $$ (1 + x_0)^2 (1 + x_1)^3 … (1 + x_n)^{n + 2} > (n + 2)^{n + 2}. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf),
  but we avoid the given substitution, relying on Bernoulli's inequality instead.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A3

open Finset

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `n ≥ 2` and `a, b : R` with `a > 0`, `a + b ≥ 0`, and `b ≠ 0`.
  Then `a^n + na^{n - 1} b < (a + b)^n`. -/
theorem pow_add_mul_lt_add_pow
    {a b : R} (ha : 0 < a) (hab : 0 ≤ a + b) (hb : b ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    a ^ n + n * a ^ (n - 1) * b < (a + b) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := Nat.exists_eq_add_of_le' hn
  calc a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b
    _ < a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b + (k + 1 : ℕ) * a ^ k * b ^ 2 :=
      lt_add_of_pos_right _ (mul_pos (hb := sq_pos_of_ne_zero hb)
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) (pow_pos ha k)))
    _ = (a ^ (k + 1) + (k + 1 : ℕ) * a ^ k * b) * (a + b) := by rw [Nat.cast_succ]; ring
    _ ≤ (a + b) ^ (k + 1) * (a + b) := by
      have h : 0 ≤ 2 * a + b := calc
        _ ≤ a + (a + b) := add_nonneg ha.le hab
        _ = 2 * a + b := by rw [two_mul, add_assoc]
      exact mul_le_mul_of_nonneg_right (pow_add_mul_le_add_pow ha.le h _) hab
    _ = (a + b) ^ (k + 2) := (pow_succ _ _).symm

/-- An application of Bernoulli's inequality: if `1 + x ≥ 0`,
  then `(n + 2)^{n + 2} x ≤ (n + 1)^{n + 1} (1 + x)^{n + 2}` for any `n : ℕ`. -/
theorem bernoulli_special1 {x : R} (hx : 0 ≤ 1 + x) (n : ℕ) :
    (n + 2 : ℕ) ^ (n + 2) * x ≤ (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  refine le_of_mul_le_mul_of_pos_left ?_ (Nat.cast_pos.mpr (Nat.succ_pos n))
  calc (n + 1 : ℕ) * ((n + 2 : ℕ) ^ (n + 2) * x)
    _ = (n + 2 : ℕ) ^ (n + 2)
        + (n + 2 : ℕ) * (n + 2 : ℕ) ^ (n + 1) * ((n + 1 : ℕ) * x - 1) := by
      rw [← pow_succ', mul_sub_one, add_sub_cancel, mul_left_comm]
    _ ≤ ((n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1)) ^ (n + 2) := by
      have h : (0 : R) ≤ (n + 2 : ℕ) := Nat.cast_nonneg _
      have h0 : 0 ≤ 2 * (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := calc
        _ ≤ (n + 2 : ℕ) + (n + 1 : ℕ) * (1 + x) :=
          add_nonneg h (mul_nonneg (Nat.cast_nonneg _) hx)
        _ = 2 * (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := by
          rw [two_mul, add_assoc, add_right_inj, Nat.cast_succ (n + 1),
            add_add_sub_cancel, mul_one_add]
      exact pow_add_mul_le_add_pow h h0 (n + 2)
    _ = ((n + 1 : ℕ) * (1 + x)) ^ (n + 2) := by
      rw [Nat.cast_succ, add_add_sub_cancel, mul_one_add]
    _ = (n + 1 : ℕ) * ((n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2)) := by
      rw [mul_pow, pow_succ', mul_assoc]

/-- An application of Bernoulli's inequality: if `x ≥ -1` and `(n + 1)x ≠ 1`,
  then `(n + 2)^{n + 2} x ≤ (n + 1)^{n + 1} (1 + x)^{n + 2}` for any `n : ℕ`. -/
theorem bernoulli_special2 {x : R} (hx : 0 ≤ 1 + x) {n : ℕ} (hx0 : (n + 1 : ℕ) * x ≠ 1) :
    (n + 2 : ℕ) ^ (n + 2) * x < (n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2) := by
  ---- The proof is by redoing the proof of `bernoulli_special1`.
  have h : (0 : R) ≤ (n + 1 : ℕ) := Nat.cast_nonneg (n + 1)
  refine lt_of_mul_lt_mul_left ?_ h
  calc (n + 1 : ℕ) * ((n + 2 : ℕ) ^ (n + 2) * x)
    _ = (n + 2 : ℕ) ^ (n + 2)
        + (n + 2 : ℕ) * (n + 2 : ℕ) ^ (n + 1) * ((n + 1 : ℕ) * x - 1) := by
      rw [← pow_succ', mul_sub_one, add_sub_cancel, mul_left_comm]
    _ < ((n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1)) ^ (n + 2) := by
      have h0 : 0 ≤ (n + 2 : ℕ) + ((n + 1 : ℕ) * x - 1) := by
        rw [Nat.cast_succ, add_add_sub_cancel, ← mul_one_add]
        exact mul_nonneg h hx
      exact pow_add_mul_lt_add_pow (Nat.cast_pos.mpr (Nat.succ_pos _))
        h0 (sub_ne_zero_of_ne hx0) (Nat.le_add_left 2 n)
    _ = ((n + 1 : ℕ) * (1 + x)) ^ (n + 2) := by
      rw [Nat.cast_succ, add_add_sub_cancel, mul_one_add]
    _ = (n + 1 : ℕ) * ((n + 1 : ℕ) ^ (n + 1) * (1 + x) ^ (n + 2)) := by
      rw [mul_pow, pow_succ', mul_assoc]
