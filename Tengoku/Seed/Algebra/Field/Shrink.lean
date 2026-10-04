/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Field.TransferInstance
public import Tengoku.Seed.Logic.Small.Defs

/-!
# Transfer field structures from `α` to `Shrink α`
-/

public section

noncomputable section

universe v
variable {α : Type*} [Small.{v} α]

namespace Shrink

instance [NNRatCast α] : NNRatCast (Shrink.{v} α) := (equivShrink α).symm.nnratCast
instance [RatCast α] : RatCast (Shrink.{v} α) := (equivShrink α).symm.ratCast
instance [DivisionRing α] : DivisionRing (Shrink.{v} α) := (equivShrink _).symm.divisionRing
instance [Field α] : Field (Shrink.{v} α) := (equivShrink _).symm.field

end Shrink
