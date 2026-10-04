/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Field.Subfield.Defs
public import Tengoku.Seed.Algebra.Order.Ring.InjSurj

/-!
# Ordered instances on subfields
-/

public section

namespace Subfield
variable {K : Type*}

/-- A subfield of an ordered field is an ordered field. -/
instance toIsStrictOrderedRing [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K) :
    IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end Subfield
