/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Int.ModEq
public import Tengoku.Seed.Tactic.NormNum.DivMod

/-!
# `norm_num` extensions for `Nat.ModEq` and `Int.ModEq`

In this file we define `norm_num` extensions for `a ≡ b [MOD n]` and `a ≡ b [ZMOD n]`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq

/-- `norm_num` extension for `Nat.ModEq`. -/
@[norm_num _ ≡ _ [MOD _]]
def evalNatModEq : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q($a ≡ $b [MOD $n]) =>
    let ⟨b, pb⟩ ← deriveBoolOfIff _ e q(Nat.modEq_iff_dvd.symm)
    return .ofBoolResult pb
  | _, _, _ => failure

/-- `norm_num` extension for `Int.ModEq`. -/
@[norm_num _ ≡ _ [ZMOD _]]
def evalIntModEq : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q($a ≡ $b [ZMOD $n]) =>
    let ⟨b, pb⟩ ← deriveBoolOfIff _ e q(Int.modEq_iff_dvd.symm)
    return .ofBoolResult pb
  | _, _, _ => failure

end Mathlib.Meta.NormNum
