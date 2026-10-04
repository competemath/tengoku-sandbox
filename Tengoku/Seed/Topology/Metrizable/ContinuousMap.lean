/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.UniformSpace.CompactConvergence
public import Tengoku.Seed.Algebra.Order.Module.Field
public import Tengoku.Seed.Topology.MetricSpace.Pseudo.Defs
public import Tengoku.Seed.Topology.Metrizable.Basic

/-!
# Metrizability of `C(X, Y)`

If `X` is a weakly locally compact σ-compact space and `Y` is a (pseudo)metrizable space,
then `C(X, Y)` is a (pseudo)metrizable space.
-/

public section

open TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*}
  [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y]

instance [PseudoMetrizableSpace Y] : PseudoMetrizableSpace C(X, Y) :=
  let := pseudoMetrizableSpaceUniformity Y
  have := pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

instance [MetrizableSpace Y] : MetrizableSpace C(X, Y) where

end ContinuousMap
