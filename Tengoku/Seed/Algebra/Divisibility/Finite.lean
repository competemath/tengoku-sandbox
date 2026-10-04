/-
Copyright (c) 2025 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Divisibility.Basic
public import Tengoku.Seed.Data.Fintype.Defs

/-!
# Divisibility in finite types
-/

public section

variable {M : Type*} [Semigroup M]

instance [Fintype M] [DecidableEq M] (a b : M) : Decidable (a ∣ b) :=
  decidable_of_iff (∃ c, b = a * c) dvd_def
