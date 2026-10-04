/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.MonoidAlgebra.PointwiseSMul

/-!
# Deprecated

-/

@[expose] public section

open Finset Function

noncomputable section

variable {G P R V : Type*}

namespace Finsupp
@[deprecated (since := "2026-02-13")] alias finite_vaddAntidiagonal :=
  Set.SMulAntidiagonal.finite_of_finite_fst

@[deprecated (since := "2026-02-13")] noncomputable alias vaddAntidiagonal :=
  Finset.VAddAntidiagonal

@[deprecated (since := "2026-02-13")] alias mem_vaddAntidiagonal_iff :=
  Finset.mem_vaddAntidiagonal

@[deprecated (since := "2026-02-13")] alias mem_vaddAntidiagonal_of_addGroup :=
  AddMonoidAlgebra.mem_vaddAntidiagonal_of_addGroup

@[deprecated (since := "2026-02-13")] alias smul_eq := AddMonoidAlgebra.smul_eq

@[deprecated (since := "2026-02-13")] alias smul_apply_addAction :=
  AddMonoidAlgebra.smul_apply_addAction

end Finsupp
