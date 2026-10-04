/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Subsemigroup.Operations
public import Tengoku.Seed.GroupTheory.Subsemigroup.Center

/-!
# Lemmas about subsemigroups

This file collects various lemmas about subsemigroups.
-/

public section

variable {M N : Type*} [Mul M] [Mul N]

namespace Subsemigroup

@[to_additive]
protected theorem center_prod : center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

end Subsemigroup
