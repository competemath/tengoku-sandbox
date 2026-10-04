/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Group.Multiset
public import Tengoku.Seed.Algebra.Order.Monoid.Canonical.Defs

/-!
# Multisets as ordered monoids

The `IsOrderedCancelAddMonoid` and `CanonicallyOrderedAdd` instances on `Multiset α`

-/

public section

variable {α : Type*}

namespace Multiset

instance : IsOrderedCancelAddMonoid (Multiset α) where
  add_le_add_left := fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left

instance : CanonicallyOrderedAdd (Multiset α) where
  le_add_self := le_add_left
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h

end Multiset
