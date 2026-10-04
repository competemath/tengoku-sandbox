/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.Submodule.Defs
public import Tengoku.Seed.Algebra.Order.Monoid.Basic

/-!
# Ordered instances on submodules
-/

public section

namespace Submodule
variable {R M : Type*}

section OrderedMonoid
variable [Semiring R]

/-- A submodule of an ordered additive monoid is an ordered additive monoid. -/
instance toIsOrderedAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] (S : Submodule R M) :
    IsOrderedAddMonoid S :=
  Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submodule of an ordered cancellative additive monoid is an ordered cancellative additive
monoid. -/
instance toIsOrderedCancelAddMonoid [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] [Module R M] (S : Submodule R M) :
    IsOrderedCancelAddMonoid S :=
  Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

end OrderedMonoid

end Submodule
