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
# IMO 2017 A1

Let $a_1, a_2, …, a_n$, and $k$ be positive integers such that $k = \sum_{j ≤ n} 1/a_j$.
Let $M = a_1 a_2 … a_n$, and suppose that $M > 1$.
Prove that for any $x ∈ ℝ$ with $x > 0$,
$$ M (x + 1)^k ≠ (x + a_1) (x + a_2) … (x + a_n). $$

### Solution

We follow and modify Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2017SL.pdf).
Instead of working over $ℝ$, we work over arbitrary ordered commutative rings.
We will need all exponents we work with to be natural numbers,
  so we also need to raise the power of both sides by $M$.
In addition, we use Bernoulli's inequality in place of the AM-GM inequality.
-/

@[expose] public section

namespace IMOSL
namespace IMO2017A1

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Let `n ≥ 2` and `a, b : R` with `a, b > 0`.
  Then `a^n + na^{n - 1} b < (a + b)^n`. -/
theorem pow_add_mul_lt_add_pow
    {a b : R} (ha : a > 0) (hb : b > 0) {n : ℕ} (hn : n ≥ 2) :
    a ^ n + n * a ^ (n - 1) * b < (a + b) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := Nat.exists_eq_add_of_le' hn
  have hab : a + b ≥ 0 := add_nonneg ha.le hb.le
  have hb0 : b ^ 2 > 0 := pow_pos hb 2
  have hab0 : 0 ≤ 2 * a + b := calc
    _ ≤ a + (a + b) := add_nonneg ha.le hab
    _ = 2 * a + b := by rw [two_mul, add_assoc]
  calc a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b
    _ < a ^ (k + 2) + (k + 2 : ℕ) * a ^ (k + 1) * b + (k + 1 : ℕ) * a ^ k * b ^ 2 :=
      lt_add_of_pos_right _ (mul_pos (hb := hb0)
        (mul_pos (Nat.cast_pos.mpr (Nat.succ_pos k)) (pow_pos ha k)))
    _ = (a ^ (k + 1) + (k + 1 : ℕ) * a ^ k * b) * (a + b) := by rw [Nat.cast_succ]; ring
    _ ≤ (a + b) ^ (k + 1) * (a + b) :=
      mul_le_mul_of_nonneg_right (ha := hab)
        (pow_add_mul_le_add_pow_of_sq_nonneg ha.le hb0.le (pow_nonneg hab 2) hab0 _)
    _ = (a + b) ^ (k + 2) := (pow_succ _ _).symm

/-- Let `n` be a positive integer and `x : R` with `x ≥ 0`.
  Then we have `n^n (x + 1) ≤ (x + n)^n`. -/
theorem bernoulli_special1 {x : R} (hx : x ≥ 0) {n : ℕ} (hn : n ≠ 0) :
    (n : R) ^ n * (x + 1) ≤ (x + n) ^ n :=
  calc (n : R) ^ n * (x + 1)
  _ = (n : R) ^ n + n * n ^ (n - 1) * x := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), mul_add_one, add_comm]
  _ ≤ (n + x) ^ n := by
    have hn0 : 0 ≤ (n : R) := Nat.cast_nonneg n
    have hnx : 0 ≤ n + x := add_nonneg hn0 hx
    have hnx0 : 0 ≤ 2 * n + x := add_nonneg (mul_nonneg zero_le_two hn0) hx
    exact pow_add_mul_le_add_pow_of_sq_nonneg hn0 (pow_nonneg hx 2) (pow_nonneg hnx _) hnx0 _
  _ = (x + n) ^ n := congrArg (· ^ n) (add_comm _ _)

/-- Let `n > 1` be an integer and `x : R` with `x > 0`.
  Then we have `n^n (x + 1) < (x + n)^n`. -/
theorem bernoulli_special2 {x : R} (hx : x > 0) {n : ℕ} (hn : n > 1) :
    (n : R) ^ n * (x + 1) < (x + n) ^ n := by
  have hn0 : n > 0 := Nat.zero_lt_of_lt hn
  calc (n : R) ^ n * (x + 1)
    _ = (n : R) ^ n + n * n ^ (n - 1) * x := by
      rw [← pow_succ', Nat.sub_add_cancel hn0, mul_add_one, add_comm]
    _ < (n + x) ^ n := pow_add_mul_lt_add_pow (Nat.cast_pos.mpr hn0) hx hn
    _ = (x + n) ^ n := congrArg (· ^ n) (add_comm _ _)

open Finset
