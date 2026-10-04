/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.EssentiallySmall
public import Tengoku.Seed.CategoryTheory.Quotient

/-!
# Quotient categories are locally small

-/

public section

universe w v u

namespace CategoryTheory.Quotient

instance {C : Type u} [Category.{v} C] (r : HomRel C) [LocallySmall.{w} C] :
    LocallySmall.{w} (Quotient r) where
  hom_small _ _ := small_of_surjective (functor r).map_surjective

end CategoryTheory.Quotient
