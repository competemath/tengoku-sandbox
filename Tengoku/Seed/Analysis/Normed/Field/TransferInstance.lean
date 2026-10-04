/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.TransferInstance
public import Tengoku.Seed.Algebra.Field.TransferInstance
public import Tengoku.Seed.Analysis.Normed.Field.Basic
public import Tengoku.Seed.Data.EReal.Operations
public import Tengoku.Seed.Topology.MetricSpace.Bounded

/-!
# Transfer normed algebraic structures across `Equiv`s

In this file, we transfer a normed field structure across an equivalence.
This continues the pattern set in `Mathlib/Algebra/Module/TransferInstance.lean`.
-/

public section

variable {α β : Type*}

namespace Equiv

/-- Transfer a `NormedField` across an `Equiv` -/
protected abbrev normedField [NormedField β] (e : α ≃ β) : NormedField α :=
  letI := e.field
  .induced α β e.ringEquiv e.injective

end Equiv
