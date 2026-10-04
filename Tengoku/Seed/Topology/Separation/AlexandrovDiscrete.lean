/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.Separation.Basic
public import Tengoku.Seed.Topology.AlexandrovDiscrete

/-!
# T1 Alexandrov-discrete topology is discrete
-/

public section

open Filter

variable {X : Type*} [TopologicalSpace X]

@[simp]
lemma nhdsKer_eq_of_t1Space [T1Space X] (s : Set X) : nhdsKer s = s := by
  ext; simp [mem_nhdsKer_iff_specializes]

instance (priority := low) [AlexandrovDiscrete X] [T1Space X] : DiscreteTopology X := by
  simp [discreteTopology_iff_nhds, ← principal_nhdsKer_singleton]
