/-
Copyright (c) 2024 euprunin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: euprunin
-/
module

public import Tengoku.Seed.Algebra.Ring.Defs
public import Tengoku.Seed.RingTheory.NonUnitalSubring.Defs
public import Tengoku.Seed.RingTheory.TwoSidedIdeal.Basic

/-!
# Additional instances for two-sided ideals.
-/

public section
instance {R} [NonUnitalNonAssocRing R] : NonUnitalSubringClass (TwoSidedIdeal R) R where
  mul_mem _ hb := TwoSidedIdeal.mul_mem_left _ _ _ hb
