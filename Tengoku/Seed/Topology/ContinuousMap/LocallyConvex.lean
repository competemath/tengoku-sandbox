/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.ContinuousMap.Algebra
public import Tengoku.Seed.Topology.Algebra.Module.LocallyConvex

/-!
# The space of continuous maps is a locally convex space

In this file we prove that the space of continuous maps from a topological space
to a locally convex topological vector space is a locally convex topological vector space.
-/

public section

open scoped Topology

instance ContinuousMap.instLocallyConvexSpace {X 𝕜 E : Type*}
    [TopologicalSpace X]
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [LocallyConvexSpace 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] :
    LocallyConvexSpace 𝕜 C(X, E) :=
  .ofBasisZero _ _ _ _ (LocallyConvexSpace.convex_basis_zero 𝕜 E).nhds_continuousMapConst <| by
    rintro ⟨K, U⟩ ⟨hK, hU₀, hUc⟩ f hf g hg a b ha hb hab x hx
    exact hUc (hf hx) (hg hx) ha hb hab
