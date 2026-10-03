/-
Copyright (c) 2025 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Rydh
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1996, Problem 4

The positive integers a and b are such that the numbers 15a + 16b
and 16a − 15b are both squares of positive integers. What is the least
possible value that can be taken on by the smaller of these two squares?

-/

namespace Imo1996P4

abbrev solution : ℤ := 231361

def S := { l | ∃ a b m n : ℤ,
    0 < a ∧ 0 < b ∧ 0 < m ∧ 0 < n ∧
    15*a + 16*b = m^2 ∧
    16*a - 15*b = n^2 ∧
    l = min (m^2) (n^2) }

lemma coprime {n : ℤ} {p : ℕ} (hp : p.Prime) (h_not_dvd : ¬(p : ℤ) ∣ n) : IsCoprime ↑p n := by
  rw [Int.isCoprime_iff_nat_coprime]
  simp only [Int.natAbs_natCast]
  apply hp.coprime_iff_not_dvd.mpr
  contrapose! h_not_dvd
  exact Int.ofNat_dvd_left.mpr h_not_dvd

lemma false_of_zero_eqMod_pos {p a : ℕ} (h₁ : 0 ≡ a [ZMOD p]) (h₂ : 0 < a) (h₃ : a < p) : False := by
  have h_p_dvd_one := Int.modEq_zero_iff_dvd.mp h₁.symm
  have : p ≤ a := Nat.le_of_dvd h₂ (Int.ofNat_dvd.mp h_p_dvd_one)
  exact Nat.not_le_of_lt h₃ this

end Imo1996P4
