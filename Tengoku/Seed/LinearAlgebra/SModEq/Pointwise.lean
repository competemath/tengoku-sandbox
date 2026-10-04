/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Algebra.Operations
public import Tengoku.Seed.LinearAlgebra.SModEq.Basic

/-!
# Pointwise lemmas for modular equivalence

In this file, we record more lemmas about `SModEq` on elements
of modules or rings.
-/

public section

open Submodule

variable {R : Type*} [Ring R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M] {U : Submodule R M}
variable {x y : M}

namespace SModEq

/--
A variant of `SModEq.smul`, where the scalar belongs to an ideal.
-/
theorem smul' (hxy : x ≡ y [SMOD U])
    {c : R} (hc : c ∈ I) : c • x ≡ c • y [SMOD (I • U)] := by
  rw [SModEq.sub_mem] at hxy ⊢
  rw [← smul_sub]
  exact smul_mem_smul hc hxy

end SModEq
