/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Real.ENatENNReal
public import Tengoku.Seed.SetTheory.Cardinal.NatCard

/-!
# Lemmas about `Nat.card` and `ENNReal`
-/

public section

namespace ENNReal

@[simp] lemma toReal_enatCard (α : Type*) : ENNReal.toReal (ENat.card α) = Nat.card α := by
  cases finite_or_infinite α <;> simp [ENat.card_eq_coe_natCard]

end ENNReal
