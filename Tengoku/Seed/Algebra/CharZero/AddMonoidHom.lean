/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.CharZero.Defs
public import Tengoku.Seed.Algebra.Group.Equiv.Defs
public import Tengoku.Seed.Data.Nat.Cast.Basic

/-!
# Transporting `CharZero` across injective `AddMonoidHom`s

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

public section

theorem CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] (e : M →+ N) (he : e 1 = 1) (he' : Function.Injective e) : CharZero N where
  cast_injective n m h := by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h
