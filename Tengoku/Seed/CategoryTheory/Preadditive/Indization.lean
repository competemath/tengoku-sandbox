/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Limits.Indization.Category
public import Tengoku.Seed.CategoryTheory.Preadditive.Transfer
public import Tengoku.Seed.CategoryTheory.Preadditive.Opposite
public import Tengoku.Seed.Algebra.Category.Grp.LeftExactFunctor

/-!
# The category of ind-objects is preadditive
-/

public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteColimits C]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts in
noncomputable instance : Preadditive (Ind C) :=
  .ofFullyFaithful (((Ind.leftExactFunctorEquivalence C).trans
    (AddCommGrpCat.leftExactFunctorForgetEquivalence _).symm).fullyFaithfulFunctor.comp
      (ObjectProperty.fullyFaithfulι _))

instance : HasFiniteBiproducts (Ind C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

end CategoryTheory
