/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
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
