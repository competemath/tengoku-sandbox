/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.Ring.Constructions
public import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
public import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Results on the category of rings requiring linear algebra

## Results

- `CommRingCat.nontrivial_of_isPushout_of_isField`: the pushout of non-trivial rings over a field
  is non-trivial.

-/

public section

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

lemma nontrivial_of_isPushout_of_isField {A B C D : CommRingCat.{u}}
    (hA : IsField A) {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    [Nontrivial B] [Nontrivial C]
    (h : IsPushout f g inl inr) : Nontrivial D := by
  let : Field A := hA.toField
  algebraize [f.hom, g.hom]
  let e : D ≅ .of (B ⊗[A] C) :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (CommRingCat.pushoutCoconeIsColimit A B C)
  let e' : D ≃ B ⊗[A] C := e.commRingCatIsoToRingEquiv.toEquiv
  exact e'.nontrivial

end CommRingCat
