/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Shrink
public import Tengoku.Seed.Algebra.GroupWithZero.Action.TransferInstance
public import Tengoku.Seed.Algebra.GroupWithZero.TransferInstance

/-!
# Transfer group with zero structures from `α` to `Shrink α`
-/

public section

noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

instance [SemigroupWithZero α] : SemigroupWithZero (Shrink α) :=
  (equivShrink _).symm.semigroupWithZero
instance [MulZeroClass α] : MulZeroClass (Shrink α) := (equivShrink _).symm.mulZeroClass
instance [MulZeroOneClass α] : MulZeroOneClass (Shrink α) := (equivShrink _).symm.mulZeroOneClass

instance [Monoid M] [AddCommMonoid α] [DistribMulAction M α] : DistribMulAction M (Shrink.{v} α) :=
  Shrink.addEquiv.distribMulAction M
