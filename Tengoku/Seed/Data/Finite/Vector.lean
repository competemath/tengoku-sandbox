/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Fintype.Vector

/-!
# Finiteness of vector types
-/

public section

variable {α : Type*}

instance List.Vector.finite [Finite α] {n : ℕ} : Finite (Vector α n) := by
  have := Fintype.ofFinite α
  infer_instance

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  have := Fintype.ofFinite α
  infer_instance
