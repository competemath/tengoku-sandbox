/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.CatCommSq
public import Tengoku.Seed.CategoryTheory.Comma.Arrow

/-!
# 2-commutative squares of categories of arrows

-/

public section

namespace CategoryTheory.Arrow

@[simps]
instance catCommSq
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ D₁) (R : C₂ ⥤ D₂) (B : D₁ ⥤ D₂) [CatCommSq T L R B] :
    CatCommSq T.mapArrow L.mapArrow R.mapArrow B.mapArrow where
  iso := (Functor.mapArrowFunctor _ _).mapIso (CatCommSq.iso T L R B)

end CategoryTheory.Arrow
