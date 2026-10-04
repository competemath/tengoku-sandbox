/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.FieldTheory.Minpoly.Basic
public import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Tengoku.Seed.RingTheory.FiniteType

/-!
# Minimal polynomials on a finite algebra

This file proves the bound on the degree of a minimal polynomial on an algebra
that is finite as a module.

-/

public section

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B] [Module.Finite A B] (x : B)

open Polynomial

namespace minpoly

variable (A) in
theorem natDegree_le_spanFinrank :
    (minpoly A x).natDegree ≤ (⊤ : Submodule A B).spanFinrank := by
  rcases LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero _ (Algebra.lmul A _ x) with
    ⟨f, f_monic, f_deg, f_aeval⟩
  refine f_deg ▸ (natDegree_le_natDegree <| minpoly.min _ _ f_monic ?_)
  rw [aeval_algHom_apply] at f_aeval
  exact Algebra.lmul_injective (R := A) <| by simpa using f_aeval

theorem natDegree_le [Module.Free A B] : (minpoly A x).natDegree ≤ Module.finrank A B := by
  nontriviality A
  simpa [Module.finrank_eq_spanFinrank_of_free] using natDegree_le_spanFinrank A x

theorem degree_le [Module.Free A B] : (minpoly A x).degree ≤ Module.finrank A B :=
  degree_le_of_natDegree_le <| natDegree_le x

end minpoly
