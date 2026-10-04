/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.CharZero.Infinite
public import Tengoku.Seed.Algebra.Ring.Rat
public import Tengoku.Seed.Data.Rat.Encodable
public import Tengoku.Seed.SetTheory.Cardinal.Basic

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
