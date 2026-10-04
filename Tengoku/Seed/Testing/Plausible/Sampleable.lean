/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Int.Order.Basic
public meta import Tengoku.Seed.Data.List.Monad
public meta import Tengoku.Seed.Data.PNat.Defs
public import Tengoku.Seed.Testing.Random.Sampleable
public import Tengoku.Seed.Testing.Random.Arbitrary
public import Tengoku.Seed.Testing.Random.Gen
public import Tengoku.Seed.Testing.Random.Random
public meta import Tengoku.Seed.Testing.Random.Sampleable

/-!
This module contains `Plausible.Shrinkable` and `Plausible.SampleableExt` instances for mathlib
types.
-/

public section

namespace Plausible

open Random Gen

section Shrinkers

meta instance Rat.shrinkable : Shrinkable Rat where
  shrink r :=
    (Shrinkable.shrink r.num).flatMap fun d => Nat.shrink r.den |>.map fun n => Rat.divInt d n

meta instance PNat.shrinkable : Shrinkable PNat where
  shrink m := Nat.shrink m.natPred |>.map Nat.succPNat

end Shrinkers

section Samplers

open SampleableExt

meta instance Rat.Arbitrary : Arbitrary Rat where
  arbitrary := do
    let d ← choose Int (-(← getSize)) (← getSize)
      (le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.natCast_nonneg _))
    let n ← choose Nat 0 (← getSize) (Nat.zero_le _)
    return Rat.divInt d n

meta instance Rat.sampleableExt : SampleableExt Rat := by infer_instance


meta instance PNat.Arbitrary : Arbitrary PNat where
  arbitrary := do
    let n ← chooseNat
    return Nat.succPNat n

meta instance PNat.sampleableExt : SampleableExt PNat := by infer_instance

end Samplers

end Plausible
