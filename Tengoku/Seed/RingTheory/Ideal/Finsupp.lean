/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Finsupp.Pi
public import Tengoku.Seed.RingTheory.Ideal.Operations

/-!

# Lemmas for action of ideals on submodules of `Finsupp`

-/

public section

variable (R : Type*) [CommRing R]

lemma Finsupp.submodule_smul {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) (p : ι → Submodule R M) (I : Ideal R) :
    Finsupp.submodule (fun i ↦ I • p i) = I • Finsupp.submodule p := by
  simp only [Finsupp.submodule_eq_iSup, Submodule.map_smul'', ← Submodule.smul_iSup]
