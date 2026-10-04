/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic
public import Tengoku.Seed.Algebra.Ring.Subsemiring.Order

/-!
# Order instances on subalgebras
-/

public section

namespace Subalgebra

variable {R A : Type*}

instance toIsOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A] [IsOrderedRing A]
    [Algebra R A] (S : Subalgebra R A) : IsOrderedRing S :=
  S.toSubsemiring.toIsOrderedRing

instance toIsStrictOrderedRing [CommSemiring R] [Semiring A] [PartialOrder A]
    [IsStrictOrderedRing A] [Algebra R A] (S : Subalgebra R A) : IsStrictOrderedRing S :=
  S.toSubsemiring.toIsStrictOrderedRing

end Subalgebra
