/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Action.Basic
public import Tengoku.Seed.Algebra.Group.Pointwise.Set.Scalar
public import Tengoku.Seed.Data.Set.Finite.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

open scoped Pointwise

namespace Set
variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

@[to_additive (attr := simp)]
lemma finite_smul_set : (a • s).Finite ↔ s.Finite := finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]
lemma infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

end Set
