/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.Order.UpperLowerSetTopology
public import Tengoku.Seed.Topology.Separation.Regular

/-!
# Linear upper or lower sets topologies are completely normal
-/

public section

open Set Topology.IsUpperSet

instance (priority := low) {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [Topology.IsUpperSet α] : CompletelyNormalSpace α where
  completely_normal s t hcst hsct := by
    obtain (rfl | ⟨a, ha⟩) := s.eq_empty_or_nonempty
    case inl => simp
    obtain (rfl | ⟨b, hb⟩) := t.eq_empty_or_nonempty
    case inl => simp
    exfalso
    grewrite [← singleton_subset_iff.mpr ha, ← singleton_subset_iff.mpr hb] at hcst hsct
    conv at hcst => equals a < b => simp
    conv at hsct => equals b < a => simp
    exact lt_asymm hcst hsct

instance (priority := low) {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [Topology.IsLowerSet α] :
    CompletelyNormalSpace α :=
  inferInstanceAs (CompletelyNormalSpace αᵒᵈ)

instance : CompletelyNormalSpace Prop :=
  inferInstance
