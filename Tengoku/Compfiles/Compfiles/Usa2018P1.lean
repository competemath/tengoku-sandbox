/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2018, Problem 1

Given that a,b,c are positive real numbers such that

  a + b + c = 4 ∛(abc)

prove that 2(ab + bc + ca) + 4min(a²,b²,c²) ≥ a² + b² + c²
-/

namespace Usa2018P1

lemma am_gm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (a * b) ^ ((1 : ℝ) / 2) ≤ a + b := by
  have hw : (0 : ℝ) ≤ 1/2 := by norm_num
  rw [Real.mul_rpow ha hb]
  linarith [Real.geom_mean_le_arith_mean2_weighted hw hw ha hb (by norm_num)]

end Usa2018P1
