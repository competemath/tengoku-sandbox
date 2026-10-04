/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Module.TransferInstance
public import Tengoku.Seed.Algebra.Group.Shrink

/-!
# Transfer normed algebraic structures from `α` to `Shrink α`
-/

public section

noncomputable section

namespace Shrink

universe v
variable {𝕜 α : Type*} [Small.{v} α] [NormedField 𝕜]

instance [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.seminormedAddCommGroup

instance [NormedAddCommGroup α] : NormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.normedAddCommGroup

instance [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α) :=
  (Shrink.addEquiv (α := α)).normedSpace 𝕜

end Shrink
