/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules

/-!
# The category of sheaves of modules is Grothendieck abelian


-/

universe u

open CategoryTheory

namespace SheafOfModules

public instance {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ ↦
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
  hasSeparator :=
    .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

end SheafOfModules
