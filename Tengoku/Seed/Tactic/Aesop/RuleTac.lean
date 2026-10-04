/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.RuleTac.Apply
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Basic
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Cases
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Forward
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Preprocess
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Tactic
public import Tengoku.Seed.Tactic.Aesop.RuleTac.Descr

public section

open Lean

namespace Aesop.RuleTacDescr

protected def run : RuleTacDescr → RuleTac
  | apply t md => RuleTac.apply t md
  | constructors cs md => RuleTac.applyConsts cs md
  | forward t immediate clear => RuleTac.forward t immediate clear
  | cases target md isRecursiveType ctorNames =>
    RuleTac.cases target md isRecursiveType ctorNames
  | tacticM decl => RuleTac.tacticM decl
  | singleRuleTac decl => RuleTac.singleRuleTac decl
  | ruleTac decl => RuleTac.ruleTac decl
  | tacticStx stx => RuleTac.tacticStx stx
  | tacGen decl => RuleTac.tacGen decl
  | preprocess => RuleTac.preprocess
  | forwardMatches m => RuleTac.forwardMatches m

end RuleTacDescr
