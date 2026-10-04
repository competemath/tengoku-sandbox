/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.Analysis.Normed.Lp.lpSpace

/-! # `lp ∞ A` as a C⋆-algebra

We place these here because, for reasons related to the import hierarchy, they should not be placed
in earlier files.
-/

public section
open scoped ENNReal

noncomputable section

variable {I : Type*} {A : I → Type*}

instance [∀ i, NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (lp A ∞) where

instance [∀ i, NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (lp A ∞) where

-- it's slightly weird that we need the `Nontrivial` instance here
-- it's because we have no way to say that `‖(1 : A i)‖` is uniformly bounded as a type class
-- aside from `∀ i, NormOneClass (A i)`, this holds automatically for C⋆-algebras though.
instance [∀ i, Nontrivial (A i)] [∀ i, CStarAlgebra (A i)] : NormedRing (lp A ∞) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

instance [∀ i, Nontrivial (A i)] [∀ i, CommCStarAlgebra (A i)] : CommCStarAlgebra (lp A ∞) where

end
