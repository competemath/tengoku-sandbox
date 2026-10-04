/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.MetricSpace.Pseudo.Pi
public import Tengoku.Seed.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distances on pi types

This file contains results on the behavior of ultrametrics in products of ultrametric spaces.

## Main results

* `Pi.instIsUltrametricDist`: a product of ultrametric spaces is ultrametric.


ultrametric, nonarchimedean
-/

public section

instance Pi.instIsUltrametricDist {ι : Type*} {X : ι → Type*} [Fintype ι]
    [(i : ι) → PseudoMetricSpace (X i)] [(i : ι) → IsUltrametricDist (X i)] :
    IsUltrametricDist ((i : ι) → X i) := by
  constructor
  intro f g h
  simp only [dist_pi_def, ← NNReal.coe_max, NNReal.coe_le_coe, ← Finset.sup_sup]
  exact Finset.sup_mono_fun fun i _ ↦ IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)
