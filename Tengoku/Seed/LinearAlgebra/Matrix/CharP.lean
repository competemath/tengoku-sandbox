/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.CharP.Defs
public import Tengoku.Seed.Data.Matrix.Diagonal

/-!
# Matrices in prime characteristic

In this file we prove that matrices over a ring of characteristic `p`
with nonempty index type have the same characteristic.
-/

public section


open Matrix

variable {n : Type*} {R : Type*} [AddMonoidWithOne R]

instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] :
    CharP (Matrix n n R) p where
  cast_eq_zero_iff k := by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]
