/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Projective
public import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!

# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.

-/

public section

universe v u

variable (R : Type u) [Ring R]

instance [Small.{v} R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)
