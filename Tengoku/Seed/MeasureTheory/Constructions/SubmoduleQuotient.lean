/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Quotient.Defs
public import Tengoku.Seed.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability on the quotient of a module by a submodule
-/

public section

namespace Submodule.Quotient
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}

instance [MeasurableSpace M] : MeasurableSpace (M ⧸ p) := Quotient.instMeasurableSpace
instance [MeasurableSpace M] [DiscreteMeasurableSpace M] : DiscreteMeasurableSpace (M ⧸ p) :=
  Quotient.instDiscreteMeasurableSpace

end Submodule.Quotient
