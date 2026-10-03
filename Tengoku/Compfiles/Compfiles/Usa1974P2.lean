/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1974, Problem 2

Prove that if a, b, and c are positive real numbers, then
a^a * b^b * c^c ≥ (abc)^((a+b+c)/3)
-/

namespace Usa1974P2

lemma usa1974_p2_wlog :
    ∀ (a b c : ℝ), a > 0 → b > 0 → c > 0 →
      a ≥ b → b ≥ c → a^a * b^b * c^c ≥ (a*b*c)^((a+b+c)/3) := by
  intro a b c ha hb hc hab hbc
  have habc : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
  have h : (a ^ a * b ^ b * c ^ c) * (a ^ b * b ^ c * c ^ a) * (a ^ c * b ^ a * c ^ b) =
            (a * b * c) ^ (a + b + c) := by
    simp (discharger := positivity) only [Real.rpow_add, Real.mul_rpow]
    ring
  apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity)
  rw [← Real.rpow_natCast]
  rw [←(Real.rpow_mul (le_of_lt habc))]
  norm_num
  rw [← h]
  rw [pow_three']
  have hab' := Real.log_le_log hb hab
  have hbc' := Real.log_le_log hc hbc
  -- ⊢ a ^ a * b ^ b * c ^ c * (a ^ b * b ^ c * c ^ a) * (a ^ c * b ^ a * c ^ b) ≤
  --   a ^ a * b ^ b * c ^ c * (a ^ a * b ^ b * c ^ c) * (a ^ a * b ^ b * c ^ c)
  gcongr ?_ * ?_ * ?_
  · rw [←(Real.log_le_log_iff (by positivity) (by positivity))]
    simp (discharger := positivity) only [Real.log_mul, Real.log_rpow]
    nlinarith only [hab', hbc', hab, hbc]
  · rw [←(Real.log_le_log_iff (by positivity) (by positivity))]
    simp (discharger := positivity) only [Real.log_mul, Real.log_rpow]
    nlinarith only [hab', hbc', hab, hbc]

end Usa1974P2
