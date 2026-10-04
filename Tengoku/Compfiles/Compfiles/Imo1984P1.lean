/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InternLM-MATH LEAN Formalizer v0.1, Hongyu Ouyang
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1984, Problem 1

Let $x$, $y$, $z$ be nonnegative real numbers with $x + y + z = 1$.
Show that $0 \leq xy+yz+zx-2xyz \leq \frac{7}{27}$
-/

namespace Imo1984P1

lemma geom_mean_le_arith_mean_3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ (3 : ℝ) := by
  have abc_pos : 0 ≤ a * b * c := by positivity
  rw [show a * b * c = ((a * b * c) ^ ((1:ℝ) / 3)) ^ (3 : ℝ) by
        rw [←(Real.rpow_mul abc_pos ((1 : ℝ)/3) 3)]; simp]
  apply Real.rpow_le_rpow; rotate_right
  · norm_num
  · apply Real.rpow_nonneg abc_pos
  · let w := (1 : ℝ) / 3
    change (a * b * c) ^ w ≤ (a + b + c) / 3
    trans w * a + w * b + w * c; rotate_left
    · unfold w
      field_simp
      exact Std.IsPreorder.le_refl (a + b + c)
    rw [Real.mul_rpow (by positivity) hc]
    rw [Real.mul_rpow ha hb]
    apply Real.geom_mean_le_arith_mean3_weighted; all_goals try norm_num; try positivity

end Imo1984P1
