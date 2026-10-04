/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.PrincipalIdealDomain
public import Tengoku.Seed.RingTheory.SimpleRing.Field
public import Tengoku.Seed.RingTheory.TwoSidedIdeal.Operations

/-!
# A commutative simple ring is a principal ideal domain

Indeed, it is a field.

-/

public section

variable {R : Type*} [CommRing R] [IsSimpleRing R]

instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder

instance IsPrincipalIdealRing.of_isSimpleRing :
    IsPrincipalIdealRing R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isPrincipalIdealRing

instance IsDomain.of_isSimpleRing :
    IsDomain R :=
  ((isSimpleRing_iff_isField _).mp ‹_›).isDomain
