/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Complex.Module
public import Tengoku.Seed.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

This had previously been in `LinearAlgebra.Orientation`,
but keeping it separate results in a significant import reduction.
-/

@[expose] public section


namespace Complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.orientation

end Complex
