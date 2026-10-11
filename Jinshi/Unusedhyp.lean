/-
Jinshi — unusedhyp: a statement that claims to need a hypothesis its proof never uses (docs/jinshi.md).

For every theorem of an examined module (the seed included: this examines proofs, not statements), the outer binders of the
type are walked together with the lambdas of the proof term, stopping at the shorter. A binder whose type is a proposition
(not a variable, not an instance) that the proof body never mentions, and that no later binder's type nor the conclusion
mentions, is reported: the theorem holds without it, so the statement promises less than was proved, and a reader who takes
the hypothesis as necessary is misled. Structural only: no `isDefEq`, no unfolding; a proof that is `sorry`, or whose value
does not pair with its type, is skipped.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- the propositional hypotheses of `ty` (its outer binders, paired with the lambdas of `val`) that `val` never mentions, each
with its binder name and its printed type -/
private partial def unusedHyps (ty val : Expr) (acc : Array (Name × String)) : MetaM (Array (Name × String)) := do
  match ty, val.consumeMData with
  | .forallE n t tb bi, .lam _ _ vb _ =>
    -- `t` is closed (the earlier binders are fvars by now); this binder is bvar 0 of both `tb` and `vb`
    let used := vb.hasLooseBVar 0 || tb.hasLooseBVar 0
    let mut acc := acc
    if !used && bi != .instImplicit then
      if ← (try Meta.isProp t catch _ => pure false) then
        let shown ← try
            let s ← withOptions (fun o => pp.maxSteps.set (pp.proofs.set o false) 200) (ppExpr t)
            pure ((toString s).replace "\n" " ")
          catch _ => pure "?"
        let shown := if shown.length > 120 then String.ofList (shown.toList.take 120) ++ "…" else shown
        acc := acc.push (n, shown)
    withLocalDecl n bi t fun x => unusedHyps (tb.instantiate1 x) vb acc
  | _, _ => return acc

def unusedhyp (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    if t.value.hasSorry then continue
    let hyps ← try unusedHyps t.type t.value #[] catch _ => pure #[]
    for (h, shown) in hyps do
      -- a hypothesis named with a leading underscore is declared unused by its author: recorded, not warned
      let declaredUnused := (h.eraseMacroScopes.toString.startsWith "_")
      out := out.push { check := "unusedhyp", severity := if declaredUnused then "info" else "warn", module := m, name := n, line := ← lineOf n,
                        detail := s!"hypothesis `{h.eraseMacroScopes} : {shown}` is never used by the proof: the theorem holds without it (the statement promises less than was proved)" ++ (if declaredUnused then " (named with a leading underscore: declared unused)" else "") }
  return out

end Jinshi
