/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roozbeh Yousefzadeh
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1974, Problem 3

Prove that the sum from k = 0 to n inclusive of
   Choose[2n + 1, 2k + 1] * 2³ᵏ
is not divisible by 5 for any integer n ≥ 0.
-/

namespace Imo1974P3

open Finset

/- We work in ℤ√8.  The sum in question is the coefficient of √8 in
(1 + √8)^(2n+1), so taking norms gives A² - 8·B² = (-7)^(2n+1) where B is
the sum.  If 5 ∣ B, then A² ≡ ±2 (mod 5), which is impossible. -/

lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (2 * n), f i = ∑ i ∈ range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        sum_range_succ, ih, add_assoc]

lemma im_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ√8) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [sum_cons, sum_cons, Zsqrtd.im_add, ih]

lemma sqrtd_pow_two_mul (k : ℕ) :
    (Zsqrtd.sqrtd : ℤ√8) ^ (2 * k) = ((8 ^ k : ℤ) : ℤ√8) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, pow_succ, ih,
        mul_assoc, Zsqrtd.dmuld]
    push_cast
    ring

/-- The binomial sum is the coefficient of √8 in (√8 + 1)^(2n+1). -/
lemma im_pow (n : ℕ) :
    ((Zsqrtd.sqrtd + 1 : ℤ√8) ^ (2 * n + 1)).im =
      ∑ k ∈ range (n + 1), ((2 * n + 1).choose (2 * k + 1) : ℤ) * 8 ^ k := by
  rw [add_pow, im_sum, show 2 * n + 1 + 1 = 2 * (n + 1) by ring,
      sum_range_two_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [pow_succ Zsqrtd.sqrtd (2 * k), sqrtd_pow_two_mul]
  simp only [one_pow, mul_one, Zsqrtd.im_mul, Zsqrtd.re_mul, Zsqrtd.re_intCast,
    Zsqrtd.im_intCast, Zsqrtd.re_natCast, Zsqrtd.im_natCast, Zsqrtd.re_sqrtd,
    Zsqrtd.im_sqrtd, mul_zero, zero_mul, add_zero, zero_add]
  ring

lemma norm_pow (m : ℕ) :
    ((Zsqrtd.sqrtd + 1 : ℤ√8) ^ m).norm = (-7) ^ m := by
  have h1 : (Zsqrtd.sqrtd + 1 : ℤ√8).norm = -7 := by
    norm_num [Zsqrtd.norm_def]
  calc ((Zsqrtd.sqrtd + 1 : ℤ√8) ^ m).norm
      = Zsqrtd.normMonoidHom ((Zsqrtd.sqrtd + 1 : ℤ√8) ^ m) := rfl
    _ = ((Zsqrtd.sqrtd + 1 : ℤ√8).norm : ℤ) ^ m := by rw [map_pow]; rfl
    _ = (-7) ^ m := by rw [h1]

end Imo1974P3
