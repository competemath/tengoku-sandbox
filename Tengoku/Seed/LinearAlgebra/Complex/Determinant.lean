/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Complex.Module
public import Tengoku.Seed.LinearAlgebra.Determinant

/-!
# Determinants of maps in the complex numbers as a vector space over `ℝ`

This file provides results about the determinants of maps in the complex numbers as a vector
space over `ℝ`.

-/

public section


namespace Complex

/-- The determinant of `conjAe`, as a linear map. -/
@[simp]
theorem det_conjAe : conjAe.toLinearEquiv.toLinearMap.det = -1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_conjAe, Matrix.det_fin_two_of]
  simp

/-- The determinant of `conjAe`, as a linear equiv. -/
@[simp]
theorem linearEquiv_det_conjAe : conjAe.toLinearEquiv.det = -1 := by simp [← Units.val_inj]

end Complex
