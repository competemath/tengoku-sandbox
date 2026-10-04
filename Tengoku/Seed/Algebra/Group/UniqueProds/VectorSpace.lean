/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.UniqueProds.Basic
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace

/-!
# A `ℚ`-vector space has `TwoUniqueSums`.
-/

public section

variable {G : Type*}

/-- Any `ℚ`-vector space has `TwoUniqueSums`, because it is isomorphic to some
  `(Basis.ofVectorSpaceIndex ℚ G) →₀ ℚ` by choosing a basis, and `ℚ` already has
  `TwoUniqueSums` because it's ordered. -/
instance [AddCommGroup G] [Module ℚ G] : TwoUniqueSums G :=
  TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace ℚ G).repr.injective inferInstance
