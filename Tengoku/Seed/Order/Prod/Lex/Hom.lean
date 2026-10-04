/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Prod.Lex
public import Tengoku.Seed.Order.Hom.Basic

/-!
# Order homomorphism for `Prod.Lex`
-/

@[expose] public section

/-- `toLex` as an `OrderHom`. -/
@[simps]
def Prod.Lex.toLexOrderHom {α β : Type*} [PartialOrder α] [Preorder β] :
    α × β →o α ×ₗ β where
  toFun := toLex
  monotone' := Prod.Lex.toLex_mono
