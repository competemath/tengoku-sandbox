/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Real.ENatENNReal
public import Tengoku.Seed.Topology.Instances.ENat
import Tengoku.Seed.Algebra.Order.Floor.Extended
public import Tengoku.Seed.Algebra.Order.Module.Field
public import Tengoku.Seed.Data.EReal.Operations
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order
public import Tengoku.Seed.Topology.MetricSpace.Bounded
public import Tengoku.Seed.Topology.Order.Real

/-!
# Topology lemma for `ENat.toENNReal`

This file shows `ENat.toENNReal` is a closed embedding.
-/

public section

namespace ENat

@[continuity]
theorem continuous_toENNReal : Continuous toENNReal := by
  refine OrderTopology.continuous_iff.mpr fun a ↦ ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat
