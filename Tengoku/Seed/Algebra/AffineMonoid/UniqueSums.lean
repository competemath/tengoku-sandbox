/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.UniqueProds.Basic
public import Tengoku.Seed.GroupTheory.Finiteness

import Tengoku.Seed.Algebra.AffineMonoid.Embedding
import Tengoku.Seed.Algebra.FreeAbelianGroup.UniqueSums

/-!
# Affine monoids have unique sums

In this file we show that finitely generated cancellative torsion-free commutative monoids have
unique sums. This is a direct corollary of them embedding into `ℤⁿ` for some `n`.
-/

public section

variable {M : Type*}

instance (priority := low) AffineAddMonoid.to_twoUniqueSums [AddCancelCommMonoid M] [AddMonoid.FG M]
    [IsAddTorsionFree M] : TwoUniqueSums M :=
  .of_injective_addHom (embedding M).toAddHom embedding_injective inferInstance

@[to_additive existing AffineAddMonoid.to_twoUniqueSums]
instance (priority := low) AffineMonoid.to_twoUniqueProds [CancelCommMonoid M] [Monoid.FG M]
    [IsMulTorsionFree M] : TwoUniqueProds M :=
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)
