/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Sites.RegularEpi
public import Tengoku.Seed.Condensed.Light.Epi

/-!

# The functor from light profinite sets to light condensed sets preserves effective epimorphisms
-/

public section

open CategoryTheory CompHausLike

universe u

instance : lightProfiniteToLightCondSet.PreservesEpimorphisms where
  preserves f hf := by
    rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    refine ⟨pullback f g, pullback.snd _ _, fun y ↦ ?_, pullback.fst _ _, pullback.condition _ _⟩
    rw [LightProfinite.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

instance : IsRegularEpiCategory LightCondSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)

example : lightProfiniteToLightCondSet.PreservesEffectiveEpis := inferInstance
