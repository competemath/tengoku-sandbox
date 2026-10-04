/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.Forward.Substitution
public import Tengoku.Seed.Tactic.Aesop.Rule.Name

public section

open Lean

set_option linter.missingDocs true

namespace Aesop

/-- Entry of the rule pattern cache. -/
@[expose] def RulePatternCache.Entry := Array (RuleName × Substitution)

set_option linter.missingDocs false in
/-- A cache for the rule pattern index. -/
structure RulePatternCache where
  map : Std.HashMap Expr RulePatternCache.Entry
  deriving Inhabited

instance : EmptyCollection RulePatternCache :=
  ⟨⟨∅⟩⟩

end Aesop
