/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Hom.Ring
public import Tengoku.Seed.Algebra.Order.Ring.InjSurj
public import Tengoku.Seed.Algebra.Ring.Subring.Defs

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `IsOrderedRing` or an `IsStrictOrderRing` is again
  the respective kind of ordered ring.
-/

@[expose] public section

namespace Subring

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

/-- A subring of an ordered ring is an ordered ring. -/
instance toIsOrderedRing [IsOrderedRing R] (s : S) : IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subring of a strict ordered ring is a strict ordered ring. -/
instance toIsStrictOrderedRing [IsStrictOrderedRing R] (s : S) : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
def orderedSubtype (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
