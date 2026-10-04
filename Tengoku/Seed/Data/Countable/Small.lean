/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Logic.Small.Basic
public import Tengoku.Seed.Data.Countable.Defs

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/

public section

universe w v

instance (priority := 100) Countable.toSmall (α : Type v) [Countable α] : Small.{w} α :=
  let ⟨_, hf⟩ := exists_injective_nat α
  small_of_injective hf

theorem Uncountable.of_not_small {α : Type v} (h : ¬ Small.{w} α) : Uncountable α := by
  rw [uncountable_iff_not_countable]
  exact mt (@Countable.toSmall α) h
