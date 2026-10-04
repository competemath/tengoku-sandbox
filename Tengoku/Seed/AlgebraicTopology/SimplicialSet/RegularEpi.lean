/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialSet.Basic
public import Tengoku.Seed.CategoryTheory.Functor.RegularEpi

/-!
# The category of simplicial sets is a regular epi category

-/

public section

universe u

open CategoryTheory

namespace SSet

instance : IsRegularEpiCategory SSet.{u} :=
  inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

end SSet
