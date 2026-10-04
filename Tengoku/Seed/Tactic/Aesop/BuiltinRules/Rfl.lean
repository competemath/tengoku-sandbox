/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.Frontend.Attribute

public section

open Lean Lean.Elab.Tactic

namespace Aesop.BuiltinRules

@[aesop safe 0 (rule_sets := [builtin])]
meta def rfl : RuleTac :=
  RuleTac.ofTacticSyntax λ _ => `(tactic| rfl)

end Aesop.BuiltinRules
