/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Tengoku.Seed.CategoryTheory.Generator.Abelian

/-!
# Grothendieck categories have a coseparator
-/

public section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

instance : HasCoseparator C := by
  suffices HasCoseparator (ShrinkHoms C) from
    HasCoseparator.of_equivalence (ShrinkHoms.equivalence.{w} C).symm
  obtain ⟨G, -, hG⟩ := Abelian.has_injective_coseparator (separator (ShrinkHoms C))
    (isSeparator_separator _)
  exact ⟨G, hG⟩

end CategoryTheory.IsGrothendieckAbelian
