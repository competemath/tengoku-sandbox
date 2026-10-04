/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Nonneg.Module
public import Tengoku.Seed.Topology.Algebra.ConstMulAction
public import Tengoku.Seed.Topology.Algebra.MulAction

/-!
# Continuous nonnegative scalar multiplication
-/

public section

variable {R α : Type*} [Semiring R] [PartialOrder R] [SMul R α] [TopologicalSpace α]

instance [ContinuousConstSMul R α] : ContinuousConstSMul {r : R // 0 ≤ r} α where
  continuous_const_smul r := continuous_const_smul r.1

instance [TopologicalSpace R] [ContinuousSMul R α] : ContinuousSMul {r : R // 0 ≤ r} α where
  continuous_smul := continuous_smul (M := R).comp <| continuous_subtype_val.prodMap continuous_id
