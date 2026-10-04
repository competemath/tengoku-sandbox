/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of arctan

-/

public section


namespace Real

theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable

end Real

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}

@[fun_prop]
theorem Measurable.arctan (hf : Measurable f) : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf

end RealComposition
