/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Divisibility.Prod
public import Tengoku.Seed.Algebra.Polynomial.FieldDivision
public import Tengoku.Seed.LinearAlgebra.InvariantBasisNumber
public import Tengoku.Seed.RingTheory.Artinian.Module

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

public section

/-- If each `Rⁿ` is a Artinian `R`-module, then `R` satisfies the strong rank condition.
Not an instance for performance reasons. -/
theorem StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R]
    [∀ n, IsArtinian R (Fin n → R)] : StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf ↦
    have e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    not_subsingleton R <| IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] fieldOfSubtypeIsMaximal

instance : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)

instance : DecompositionMonoid (Polynomial R) :=
  MulEquiv.decompositionMonoid <|
    (Polynomial.mapEquiv <| (equivPi R).toRingEquiv).trans (Polynomial.piEquiv _)

end IsArtinianRing
