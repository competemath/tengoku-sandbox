/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Logic.Small.Defs
public import Tengoku.Seed.Topology.Homeomorph.TransferInstance

/-!
# Topological space structure on `Shrink X`
-/

@[expose] public section

universe v u

namespace Shrink

noncomputable instance (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    TopologicalSpace (Shrink.{v} X) :=
  (equivShrink X).symm.topologicalSpace

/-- `equivShrink` as a homeomorphism. -/
@[simps! toEquiv]
noncomputable def homeomorph (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    X ≃ₜ Shrink.{v} X :=
  (equivShrink X).symm.homeomorph.symm

end Shrink
