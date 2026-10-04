/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
public import Tengoku.Seed.Algebra.Category.ModuleCat.Adjunctions
public import Tengoku.Seed.Algebra.Category.ModuleCat.FilteredColimits
public import Tengoku.Seed.CategoryTheory.Sites.Abelian
public import Tengoku.Seed.CategoryTheory.Sites.Adjunction
public import Tengoku.Seed.Condensed.Light.Basic
public import Tengoku.Seed.Condensed.Light.Instances
/-!

# Light condensed `R`-modules

This file defines light condensed modules over a ring `R`.

## Main results

* Light condensed `R`-modules form an abelian category.

* The forgetful functor from light condensed `R`-modules to light condensed sets has a left
  adjoint, sending a light condensed set to the corresponding *free* light condensed `R`-module.
-/

@[expose] public section


universe u

open CategoryTheory

variable (R : Type u) [Ring R]

/--
The category of light condensed `R`-modules, defined as sheaves of `R`-modules over
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)

noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from light condensed `R`-modules to light condensed sets. -/
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)

@[simp]
lemma LightCondensed.forget_obj_obj_map_hom_apply (X : LightCondMod R)
    {S T : LightProfiniteᵒᵖ} (f : S ⟶ T) (a : ((sheafToPresheaf _ _).obj X).obj S) :
    ((forget R).obj X).obj.map f a = X.obj.map f a :=
  rfl

@[simp]
lemma LightCondensed.forget_map_hom_app_hom_apply
    {X Y : LightCondMod R} (f : X ⟶ Y) (S : LightProfiniteᵒᵖ)
    (a : ((sheafToPresheaf _ _).obj X).obj S) :
    ((forget R).map f).hom.app S a = f.hom.app S a :=
  rfl

/--
The left adjoint to the forgetful functor. The *free light condensed `R`-module* on a light
condensed set.
-/
noncomputable
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

open LightCondensed

instance : (LightCondensed.free R).IsLeftAdjoint := freeForgetAdjunction R |>.isLeftAdjoint

instance : (LightCondensed.forget R).IsRightAdjoint := freeForgetAdjunction R |>.isRightAdjoint

/--
The category of light condensed abelian groups, defined as sheaves of `ℤ`-modules over
`LightProfinite.{0}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondMod ℤ

noncomputable example : Abelian LightCondAb := inferInstance

namespace LightCondMod

lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end LightCondMod
