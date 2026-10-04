/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.Torsion.Free
public import Tengoku.Seed.SetTheory.Cardinal.Basic

/-!
# Cardinality of a module

This file proves that the cardinality of a module without zero divisors is at least the cardinality
of its base ring.
-/

public section

open Function

universe u v

namespace Cardinal

/-- The cardinality of a nontrivial torsion-free module over a domain is at least the cardinality of
the ring. -/
theorem mk_le_of_module (R : Type u) (E : Type v)
    [AddCommGroup E] [Ring R] [IsDomain R] [Module R E] [Nontrivial E] [Module.IsTorsionFree R E] :
    Cardinal.lift.{v} (#R) ≤ Cardinal.lift.{u} (#E) := by
  obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0
  have : Injective (fun k ↦ k • x) := smul_left_injective R hx
  exact lift_mk_le_lift_mk_of_injective this

end Cardinal
