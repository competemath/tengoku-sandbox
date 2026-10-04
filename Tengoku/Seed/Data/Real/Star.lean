/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Star.Basic
public import Tengoku.Seed.Data.Real.Basic

/-!
# The real numbers are a \*-ring, with the trivial \*-structure
-/

public section

/-- The real numbers are a \*-ring, with the trivial \*-structure. -/
instance : StarRing ℝ :=
  starRingOfComm

instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩
