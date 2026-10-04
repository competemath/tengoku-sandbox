/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2013, Problem 5

Given positive integers m and n, prove that there is a positive integer c
such that the numbers cm and cn have the same number of occurrences of each
non-zero digit when written in base ten.
-/

namespace Usa2013P5

/-- `digitCount t x d` counts the occurrences of the digit `d` among the
first `t` decimal digits of `x` (least significant first), i.e. the digits of
`x` padded with leading zeros to length `t`. -/
def digitCount (t x d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (if (x / 10^i) % 10 = d then 1 else 0)

/-- The `j`-th decimal digit of `x` only depends on `x % 10^(j+1)`, hence
taking `x` modulo a higher power of `10` does not change that digit. -/
lemma mod_pow_div_mod (x j k : ℕ) (h : j + 1 ≤ k) :
    (x % 10^k) / 10^j % 10 = (x / 10^j) % 10 := by
  have e1 : (x % 10^k) / 10^j % 10 = ((x % 10^k) % 10^(j+1)) / 10^j := by
    rw [pow_succ 10 j]
    exact (Nat.mod_mul_right_div_self (x % 10^k) (10^j) 10).symm
  rw [e1, Nat.mod_mod_of_dvd _ (pow_dvd_pow 10 h), pow_succ 10 j,
    Nat.mod_mul_right_div_self]

/-- Multiplication by `10` modulo `10^t - 1` rotates the (padded) `t`-digit
representation of `x` by one place, so it preserves all digit counts. -/
lemma digitCount_mul_ten_mod (t x d : ℕ) (ht : 0 < t) (hx : x < 10^t - 1) :
    digitCount t ((10 * x) % (10^t - 1)) d = digitCount t x d := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, (Nat.sub_add_cancel ht).symm⟩
  set P := 10 ^ t' with hP
  have hPpos : 0 < P := pow_pos (by norm_num) _
  have h10t : 10 ^ (t' + 1) = P * 10 := by rw [pow_succ, ← hP]
  set b := x / P with hb
  set w := x % P with hw
  have hxbw : x = b * P + w := by
    rw [hb, hw, Nat.mul_comm (x / P) P]
    exact (Nat.div_add_mod x P).symm
  have hwle : w + 1 ≤ P := Nat.mod_lt x hPpos
  have hble : b ≤ 9 := by
    have hx2 : x < 10 ^ (t' + 1) := Nat.lt_of_lt_of_le hx (Nat.sub_le _ _)
    have h3 : x < 10 * P := by rwa [h10t, Nat.mul_comm P 10] at hx2
    have h4 : b < 10 := (Nat.div_lt_iff_lt_mul hPpos).mpr h3
    lia
  have hkey : b + 10 * w < P * 10 - 1 := by
    have hx' : x < P * 10 - 1 := by rw [← h10t]; exact hx
    by_contra hcon
    push Not at hcon
    have hb9 : b = 9 := by lia
    have hw9 : w = P - 1 := by lia
    have hxe : x = 9 * P + (P - 1) := by rw [hxbw, hb9, hw9]
    have h5 : 9 * P + (P - 1) = P * 10 - 1 := by lia
    lia
  have h10x : 10 * x = (b + 10 * w) + (10 ^ (t' + 1) - 1) * b := by
    have h1 : (10 : ℕ) ^ (t' + 1) = 10 ^ (t' + 1) - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm
    have h2 : b * (10 ^ (t' + 1)) = (10 ^ (t' + 1) - 1) * b + b := by
      nth_rewrite 1 [h1]
      ring
    calc 10 * x = b * (10 ^ (t' + 1)) + 10 * w := by rw [hxbw, h10t]; ring
      _ = (b + 10 * w) + (10 ^ (t' + 1) - 1) * b := by rw [h2]; ring
  have hy : (10 * x) % (10 ^ (t' + 1) - 1) = b + 10 * w := by
    rw [h10x, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (show b + 10 * w < 10 ^ (t' + 1) - 1 by rw [h10t]; exact hkey)]
  have hdiv10 : (b + 10 * w) / 10 = w := by
    rw [Nat.add_mul_div_left b w (by norm_num : 0 < 10),
      Nat.div_eq_of_lt (by lia : b < 10), zero_add]
  have hmod0term : (if ((b + 10 * w) / 10 ^ 0) % 10 = d then 1 else 0)
      = (if b = d then 1 else 0) := by
    rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by lia : b < 10)]
  have hblastterm : (if (x / 10 ^ t') % 10 = d then 1 else 0)
      = (if b = d then 1 else 0) := by
    rw [← hP, ← hb, Nat.mod_eq_of_lt (by lia : b < 10)]
  have hcongsum :
      (∑ i ∈ Finset.range t', (if ((b + 10 * w) / 10 ^ (i + 1)) % 10 = d then 1 else 0))
        = ∑ i ∈ Finset.range t', (if (x / 10 ^ i) % 10 = d then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : (b + 10 * w) / 10 ^ (i + 1) = w / 10 ^ i := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv10]
    have h2 : (w / 10 ^ i) % 10 = (x / 10 ^ i) % 10 := by
      show ((x % 10 ^ t') / 10 ^ i) % 10 = (x / 10 ^ i) % 10
      exact mod_pow_div_mod x i t' hi
    rw [h1, h2]
  rw [hy]
  simp only [digitCount]
  rw [Finset.sum_range_succ', Finset.sum_range_succ, hmod0term, hblastterm, hcongsum]

/-- Iterating the one-place rotation: multiplication by `10^e` modulo
`10^t - 1` preserves all digit counts. -/
lemma digitCount_pow_ten_mul_mod (t : ℕ) (ht : 0 < t) (x e d : ℕ) (hx : x < 10^t - 1) :
    digitCount t ((10^e * x) % (10^t - 1)) d = digitCount t x d := by
  have hT : 0 < 10^t - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp ht) (by norm_num))
  induction e with
  | zero => simp [Nat.mod_eq_of_lt hx]
  | succ e ih =>
    have h1 : (10 ^ (e + 1) * x) % (10^t - 1)
        = (10 * ((10^e * x) % (10^t - 1))) % (10^t - 1) := by
      have h2 : 10 ^ (e + 1) * x = 10 * (10^e * x) := by rw [pow_succ']; ring
      rw [h2]
      exact (Nat.ModEq.mul_left 10 (Nat.mod_modEq _ _)).symm
    rw [h1, digitCount_mul_ten_mod t _ d ht (Nat.mod_lt _ hT), ih]

/-- For a nonzero digit `d`, the number of occurrences of `d` in the decimal
representation of `x` equals `digitCount t x d` whenever `t` is large enough. -/
lemma count_digits_eq_digitCount (x t d : ℕ) (hd : d ≠ 0) (hx : x < 10^t) :
    (Nat.digits 10 x).count d = digitCount t x d := by
  induction t generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    simp [hx0, digitCount]
  | succ t ih =>
    obtain rfl | hxpos := Nat.eq_zero_or_pos x
    · rw [Nat.digits_zero, List.count_nil]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      simp [show ¬((0 : ℕ) = d) from mt Eq.symm hd]
    · rw [Nat.digits_def' (by norm_num) hxpos]
      have hcc : ((x % 10) :: Nat.digits 10 (x / 10)).count d
          = (Nat.digits 10 (x / 10)).count d + (if x % 10 = d then 1 else 0) := by
        by_cases h : x % 10 = d <;> simp [h]
      have hxt : x / 10 < 10 ^ t := by
        have h1 : x < 10 ^ t * 10 := by rw [← pow_succ]; exact hx
        exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)).mpr h1
      rw [hcc, ih (x / 10) hxt]
      have hsum :
          (∑ i ∈ Finset.range t, (if ((x / 10) / 10 ^ i) % 10 = d then 1 else 0))
            = ∑ i ∈ Finset.range t, (if (x / 10 ^ (i + 1)) % 10 = d then 1 else 0) := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [Nat.div_div_eq_div_mul, ← pow_succ']
      simp only [digitCount]
      rw [Finset.sum_range_succ',
        show (if (x / 10 ^ 0) % 10 = d then 1 else 0)
          = (if x % 10 = d then 1 else 0) by simp,
        ← hsum]

lemma two_pow_ge_add_one (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    lia

end Usa2013P5
