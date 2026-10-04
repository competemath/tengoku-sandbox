/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.RingTheory.Finiteness.Basic
public import Tengoku.Seed.LinearAlgebra.PiTensorProduct.Generators

/-!
# A multiple tensor product of finitely generated modules is finitely generated

-/

public section

open TensorProduct

namespace PiTensorProduct

instance finite {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  choose n γ hg using fun i => Module.Finite.exists_fin (R := R) (M := M i)
  rw [Module.finite_def, ← submodule_span_eq_top hg]
  exact Submodule.fg_span (Set.finite_range _)

end PiTensorProduct
