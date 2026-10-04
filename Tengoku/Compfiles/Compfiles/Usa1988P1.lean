/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1988, Problem 1

The repeating decimal 0.ab ... k pq ... u = m/n, where m and n are
relatively prime integers, and there is at least one decimal before
the repeating part. Show that n is divisible by 2 or 5 (or both).
[For example, 0.01136̅ = 0.01136363636 ... = 1/88 and 88 is divisible
by 2.]
-/

namespace Usa1988P1

/-!
We model the repeating decimal `0.ab…k⟨pq…u⟩` as follows: `r ≥ 1` is the
number of digits before the repeating part, `s ≥ 1` is the length of the
repeating part, `a` is the integer formed by the digits `ab…k` and `b` is
the integer formed by the digits `pq…u`. The value of the decimal is then

  a / 10^r + b / (10^r * (10^s - 1)) = (a * (10^s - 1) + b) / (10^r * (10^s - 1)).

The last digits of `a` and `b` differ (`k ≠ u`), for otherwise the
repeating part could have been started one digit earlier.
-/

-- Based on the solution by John Scholes (kalva):
-- https://prase.cz/kalva/usa/usoln/usol881.html

/-- The numerator `a * (10 ^ s - 1) + b` of the unreduced fraction is
congruent to `b - a` modulo 10, so it is not divisible by 10 when the
last digits of `a` and `b` differ. -/
lemma not_ten_dvd_num {a b s : ℕ} (hs : 1 ≤ s) (hab : a % 10 ≠ b % 10) :
    ¬ 10 ∣ a * (10 ^ s - 1) + b := by
  intro h
  have h1 : a * 10 ^ s ≡ 0 [MOD 10] :=
    Nat.modEq_zero_iff_dvd.mpr
      (dvd_mul_of_dvd_right (dvd_pow_self 10 (Nat.one_le_iff_ne_zero.mp hs)) a)
  have h2 : a * (10 ^ s - 1) + a = a * 10 ^ s := by
    conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_pow s 10 (by norm_num))]
    rw [mul_add, mul_one]
  have h3 : a * (10 ^ s - 1) + b + a ≡ b [MOD 10] := by
    have e : a * (10 ^ s - 1) + b + a = a * 10 ^ s + b := by
      rw [add_right_comm, h2]
    rw [e]
    simpa using h1.add_right b
  have h4 : a * (10 ^ s - 1) + b + a ≡ a [MOD 10] := by
    have hN : a * (10 ^ s - 1) + b ≡ 0 [MOD 10] := Nat.modEq_zero_iff_dvd.mpr h
    simpa using hN.add_right a
  exact hab (h4.symm.trans h3)

end Usa1988P1
