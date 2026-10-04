/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Preadditive.FunctorCategory
public import Tengoku.Seed.CategoryTheory.Center.Basic

/-!
# The center of an additive category

-/

public section

universe v u

namespace CategoryTheory

namespace CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma app_add (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl

@[simp]
lemma app_sub (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl

@[simp]
lemma app_neg (z : CatCenter C) (X : C) :
    (-z).app X = - z.app X := rfl

end CatCenter

end CategoryTheory
