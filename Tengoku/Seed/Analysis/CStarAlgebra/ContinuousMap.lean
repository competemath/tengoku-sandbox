/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.Classes
public import Tengoku.Seed.Topology.ContinuousMap.Compact
public import Tengoku.Seed.Topology.ContinuousMap.ZeroAtInfty

/-! # C⋆-algebras of continuous functions

We place these here because, for reasons related to the import hierarchy, they cannot be placed in
earlier files.
-/

public section

variable {α A : Type*}
noncomputable section

namespace BoundedContinuousFunction

variable [TopologicalSpace α]

instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) where

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α →ᵇ A) where

instance [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) where

instance [CommCStarAlgebra A] : CommCStarAlgebra (α →ᵇ A) where

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) where

instance [CStarAlgebra A] : CStarAlgebra C(α, A) where

instance [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) where

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

instance [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where

instance [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) where

end ZeroAtInftyContinuousMap
