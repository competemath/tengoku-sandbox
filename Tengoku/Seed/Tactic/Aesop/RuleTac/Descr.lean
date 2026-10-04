/-
Changed for Tengoku: copied from Aesop (leanprover-community/aesop at 18889deb9e83); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Aesop.RuleTac.Basic
public import Tengoku.Seed.Tactic.Aesop.Forward.Match.Types
public import Tengoku.Seed.Tactic.Aesop.Script.CtorNames

public section

open Lean Lean.Meta

namespace Aesop

inductive RuleTacDescr
  | apply (term : RuleTerm) (md : TransparencyMode)
  | constructors (constructorNames : Array Name) (md : TransparencyMode)
  | forward (term : RuleTerm) (immediate : UnorderedArraySet PremiseIndex)
      (isDestruct : Bool)
  | cases (target : CasesTarget) (md : TransparencyMode)
      (isRecursiveType : Bool) (ctorNames : Array CtorNames)
  | tacticM (decl : Name)
  | ruleTac (decl : Name)
  | tacGen (decl : Name)
  | singleRuleTac (decl : Name)
  | tacticStx (stx : Syntax)
  | preprocess
  | forwardMatches (ms : Array ForwardRuleMatch)
  deriving Inhabited

namespace RuleTacDescr

def forwardRuleMatches? : RuleTacDescr → Option (Array ForwardRuleMatch)
  | forwardMatches ms => ms
  | _ => none

end RuleTacDescr

end Aesop
