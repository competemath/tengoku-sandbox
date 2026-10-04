/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Subgroup.Defs
public import Tengoku.Seed.Algebra.Group.Submonoid.DistribMulAction
public import Tengoku.Seed.Algebra.Ring.Action.Basic

/-!
# Instances of `MulSemiringAction` for subobjects

These are defined in this file as `Semiring`s are not available yet where `Submonoid` and `Subgroup`
are defined.

Instances for `Subsemiring` and `Subring` are provided next to the other scalar actions instances
for those subobjects.

-/

public section

assert_not_exists RelIso

variable {M G R : Type*}
variable [Monoid M] [Group G] [Semiring R]

instance (priority := low) [MulSemiringAction M R] {S : Type*} [SetLike S M] (s : S)
    [SubmonoidClass S M] : MulSemiringAction s R :=
  { (inferInstance : DistribMulAction s R), (inferInstance : MulDistribMulAction s R) with }

/-- A stronger version of `Submonoid.distribMulAction`. -/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  inferInstance

/-- A stronger version of `Subgroup.distribMulAction`. -/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  inferInstance
