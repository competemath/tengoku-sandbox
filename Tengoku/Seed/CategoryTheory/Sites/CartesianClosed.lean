/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Monoidal.Closed.Ideal
public import Tengoku.Seed.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Tengoku.Seed.CategoryTheory.Sites.CartesianMonoidal
public import Tengoku.Seed.CategoryTheory.Sites.Sheafification
/-!

# Sheaf categories are Cartesian closed

...if the underlying presheaf category is Cartesian closed, the target category has
(chosen) finite products, and there exists a sheafification functor.
-/

public section

noncomputable section

open CategoryTheory Presheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

instance [HasSheafify J A] [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] :
    MonoidalClosed (Sheaf J A) :=
  cartesianClosedOfReflective' (sheafToPresheaf _ _) {
    obj F := ⟨F.obj, (isSheaf_of_iso_iff F.2.choose_spec.some).1 F.2.choose.property⟩
    map f := ⟨f.hom⟩ } (Iso.refl _)
