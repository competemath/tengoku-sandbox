/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.PNat.Defs
public import Tengoku.Seed.Logic.Equiv.Defs

/-!
# The equivalence between `ℕ+` and `ℕ`
-/

@[expose] public section

/-- An equivalence between `ℕ+` and `ℕ` given by `PNat.natPred` and `Nat.succPNat`. -/
@[simps -fullyApplied]
def _root_.Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := PNat.succPNat_natPred
  right_inv := Nat.natPred_succPNat
