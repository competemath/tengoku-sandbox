/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Sites.RegularEpi
public import Tengoku.Seed.Condensed.Epi
public import Tengoku.Seed.Condensed.Functors
public import Tengoku.Seed.Condensed.Limits  -- shake: keep (compHausToCondensed.PreservesEffectiveEpis), cf. lean#13417

/-!

# The functor from compact Hausdorff spaces to condensed sets preserves effective epimorphisms
-/

public section

open CategoryTheory CompHausLike

universe u

instance : compHausToCondensed.PreservesEpimorphisms where
  preserves f hf := by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y ↦ ?_, ⟨pullback.fst _ _⟩,
      ULift.ext _ _ <| pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

instance : IsRegularEpiCategory CondensedSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance
