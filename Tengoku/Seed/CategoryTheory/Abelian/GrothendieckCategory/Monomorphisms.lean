/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Tengoku.Seed.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Tengoku.Seed.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Monomorphisms in Grothendieck abelian categories

In this file, we show that in a Grothendieck abelian category,
monomorphisms are stable under transfinite composition.

-/

public section

universe w v u

namespace CategoryTheory

namespace IsGrothendieckAbelian

open MorphismProperty

instance {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsStableUnderTransfiniteComposition.{w} (monomorphisms C) := by
  infer_instance

end IsGrothendieckAbelian

end CategoryTheory
