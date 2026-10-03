/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# Iranian Mathematical Olympiad 1998, problem 3

Let x₁, x₂, x₃, x₄ be positive real numbers such that

  x₁ ⬝ x₂ ⬝ x₃ ⬝ x₄ = 1.

Prove that
  x₁³ + x₂³ + x₃³ + x₄³ ≥ max(x₁ + x₂ + x₃ + x₄, 1/x₁ + 1/x₂ + 1/x₃ + 1/x₄).

-/

namespace Iran1998P3

lemma cube_root_cube (x : ℝ) (h : 0 ≤ x) : (x^(3:ℝ)) ^ ((1:ℝ)/3) = x := by
  rw [← Real.rpow_mul h, mul_div_cancel₀ (1 : ℝ) three_ne_zero]
  exact Real.rpow_one x

end Iran1998P3
