/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.Prod
public import Tengoku.Seed.Tactic.Abel
public import Tengoku.Seed.Algebra.Module.LinearMap.Defs

/-!
# Addition and subtraction are linear maps from the product space

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/

public section

variable {R : Type*} {M : Type*} [Semiring R]

namespace IsLinearMap

theorem isLinearMap_add [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · simp [smul_add]

theorem isLinearMap_sub [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

end IsLinearMap
