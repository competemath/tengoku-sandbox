/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
public import Tengoku.Seed.RingTheory.Noetherian.Basic

/-!
# Noetherian quotient rings and quotient modules
-/

public section

instance Ideal.Quotient.isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower R <| inferInstance
