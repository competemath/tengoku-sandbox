/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.ZModuleEquivalence
public import Tengoku.Seed.Algebra.Category.ModuleCat.Subobject

/-!
# The category of abelian groups is well-powered
-/

public section


open CategoryTheory

universe u

namespace AddCommGrpCat

instance wellPowered_addCommGrp : WellPowered.{u} AddCommGrpCat.{u} :=
  wellPowered_of_equiv.{u} (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence

end AddCommGrpCat
