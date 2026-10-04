/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.Linear
public import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
public import Tengoku.Seed.RingTheory.Noetherian.Basic

/-!

# `Ext`-modules between finitely generated modules over Noetherian rings are finitely generated

-/

public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian

instance ModuleCat.finite_ext [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext N M i) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv).symm
  | succ n ih =>
    obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R N
    let exac := LinearMap.shortExact_shortComplexKer surjf
    exact Module.Finite.of_surjective (exac.extClass.precompOfLinear R M (add_comm 1 n))
      (precomp_extClass_surjective_of_projective_X₂ M exac n)
