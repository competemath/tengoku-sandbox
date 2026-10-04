/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Topology.Order
public import Tengoku.Seed.Data.ZMod.Defs

/-!
# Topology on `ZMod N`

We equip `ZMod N` with the discrete topology.
-/

public section

namespace ZMod

variable {N : ℕ}

/-- The discrete topology (every set is open). -/
instance : TopologicalSpace (ZMod N) := ⊥

instance : DiscreteTopology (ZMod N) := ⟨rfl⟩

end ZMod
