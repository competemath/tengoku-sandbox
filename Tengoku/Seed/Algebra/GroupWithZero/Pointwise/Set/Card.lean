/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Pointwise.Set.Scalar
public import Tengoku.Seed.Algebra.GroupWithZero.Action.Basic
public import Tengoku.Seed.SetTheory.Cardinal.Finite

/-!
# Cardinality of sets under pointwise group with zero operations
-/

public section

assert_not_exists Field

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

namespace Set
variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

lemma _root_.Cardinal.mk_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

lemma natCard_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective₀ ha) _

end Set
