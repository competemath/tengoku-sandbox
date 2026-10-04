/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
public import Tengoku.Seed.Geometry.Manifold.IsManifold.Basic
public import Tengoku.Seed.Topology.Compactness.Paracompact
public import Tengoku.Seed.Topology.Metrizable.Urysohn

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite-dimensional real
vector space is metrizable.
-/

public section


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite-dimensional real vector space is
metrizable. -/
theorem Manifold.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  have := I.locallyCompactSpace; have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M
