/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Grp.Colimits
public import Tengoku.Seed.Algebra.Category.Grp.Limits
public import Tengoku.Seed.Algebra.Category.Grp.ZModuleEquivalence
public import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
public import Tengoku.Seed.CategoryTheory.Adjunction.Limits
public import Tengoku.Seed.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The category of abelian groups is abelian
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace AddCommGrpCat

variable {X Y : AddCommGrpCat.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
@[instance_reducible]
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
@[instance_reducible]
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGrpCat.{u} where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

end AddCommGrpCat
