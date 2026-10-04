/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.FilteredColimits
public import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Generator
public import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Tengoku.Seed.CategoryTheory.Functor.ReflectsIso.Balanced
public import Tengoku.Seed.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# The category of presheaves of modules is Grothendieck abelian

-/

universe u

open CategoryTheory Limits

namespace PresheafOfModules

public instance {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun J _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := J) ⋙ PresheafOfModules.toPresheaf R) :=
      preservesLimit_of_natIso _ (preservesColimitNatIso (toPresheaf R)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R)⟩⟩⟩⟩

end PresheafOfModules
