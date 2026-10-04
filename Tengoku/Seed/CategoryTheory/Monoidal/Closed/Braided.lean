/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Adjunction.ParametrizedLimits
public import Tengoku.Seed.CategoryTheory.Monoidal.Braided.Basic
public import Tengoku.Seed.CategoryTheory.Monoidal.Closed.Basic

/-!
# Closed braided monoidal categories

Interactions between monoidal closed and braided category structures.

-/

public section

namespace CategoryTheory

open Category MonoidalCategory Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

namespace ihom

instance (A : C) [Closed A] :
    (tensorRight A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight A)

instance (A : C) [MonoidalClosed C] (J : Type*) [Category* J] :
    PreservesLimitsOfShape J (MonoidalClosed.internalHom.flip.obj A) :=
  MonoidalClosed.internalHomAdjunction₂.preservesLimitsOfShape_flip_obj _ _

end ihom

end CategoryTheory
