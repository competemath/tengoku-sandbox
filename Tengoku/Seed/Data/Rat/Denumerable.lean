/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.Rat
public import Tengoku.Seed.Data.Rat.Encodable
public import Tengoku.Seed.Algebra.CharZero.Infinite
public import Tengoku.Seed.Logic.Denumerable

/-!
# Denumerability of ℚ

This file proves that ℚ is denumerable.

The fact that ℚ has cardinality ℵ₀ is proved in `Mathlib/Data/Rat/Cardinal.lean`
-/

public section

assert_not_exists Module Field

namespace Rat

open Denumerable

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ

end Rat
