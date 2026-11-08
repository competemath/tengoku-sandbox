/-
nested — an inventory of nested inductive declarations (docs/jinshi.md). When a constructor argument's type contains the
inductive being defined NESTED inside another type former (`inductive Tree (α : Type) | node : List (Tree α) → Tree α`, `Tree`
inside `List`), Lean's kernel does not check this directly: it builds an auxiliary, unnested inductive under a reserved name,
type-checks THAT, and rewrites ("restores") the result back into the nested form. Lean's own kernel source comment near this
code says it defensively re-checks everything the restoration step rewrites, "because it is cheap and it keeps a mistake in the
restoration from reaching the environment" — upstream itself treats this translate/rewrite step as a plausible source of bugs.

This examination does NOT re-verify a nested inductive's soundness, and is not an accusation: nested inductives are a normal,
supported feature. Every declaration of an examined module, nested inductives included, is already independently re-type-checked
at the whole-module level by `replay` (`leanchecker`) and `lean4lean` (scripts/jinshi/run.py: `replay_finding`/`lean4lean_finding`
re-add EVERY declaration of the module to a fresh environment, not theorems only — confirmed by reading those functions).
`nested` exists purely to make nested-inductive declarations VISIBLE and SEARCHABLE — a maintainer, or a differential-fuzzing
pass, can specifically target the kernel's restoration step — not to duplicate verification those checks already do.

For every inductive declaration of an examined module (the seed included) passing `okName` whose `InductiveVal.numNested > 0`
(`Lean.InductiveVal`, from `ConstantInfo.inductInfo?`, matched on the constructor directly — the same caution as Jinshi/Importance
.lean: don't assume a convenience accessor works on an imported constant): a best-effort, heartbeat-capped structural walk of
each constructor's argument types names WHICH argument has a nested occurrence and of what shape (an argument whose own head is
some OTHER type former that mentions the inductive somewhere inside, as opposed to a plain direct recursive argument — the
inductive applied directly — or a non-recursive one). One `info` finding per nested inductive; one summary `info` per run with
the count.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- distinct subterms visited while searching one constructor argument's type for a nested occurrence, before the search gives up -/
def nestedSearchCap : Nat := 5000

/-- heartbeats (in the option's unit of 1000) the occurrence walk of one inductive's constructors may spend -/
def nestedHeartbeats : Nat := 100000

/-- `true` when `e`, read as an application, is headed by a constant in `names` -/
def headIsOneOf (names : List Name) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some c => names.contains c
  | none => false

/-- does a constant in `names` occur anywhere in `e`, as the head of some subterm? an iterative walk with a visited set on
structural equality, capped at `cap` distinct subterms (Jinshi/Forensics.lean's `walkTerm` idiom) -/
def containsHeadOf (names : List Name) (cap : Nat) (root : Expr) : Bool := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array Expr := #[root]
  let mut steps : Nat := 0
  let mut found := false
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    if steps ≥ cap then break
    seen := seen.insert e
    steps := steps + 1
    if headIsOneOf names e then
      found := true
      break
    match e with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return found

/-- one constructor's fields (the binders after the inductive's own parameters), each checked for a nested occurrence of `v`'s
own type names (`v.all`) -/
def describeCtor (env : Environment) (v : InductiveVal) (ctorName : Name) : MetaM (Array String) := do
  match env.find? ctorName with
  | some (.ctorInfo cv) =>
    forallTelescope cv.type fun xs _ => do
      let mut out := #[]
      let fields := (xs.toList.drop cv.numParams).toArray
      let shortCtor := toString ((ctorName.components.getLast?).getD ctorName)
      for x in fields do
        let fty ← instantiateMVars (← inferType x)
        let label := toString (← x.fvarId!.getUserName)
        match fty.getAppFn.constName? with
        | some h =>
          if v.all.contains h then
            pure ()  -- a direct recursive occurrence at this position (`v`'s own type applied directly): not nested
          else if containsHeadOf v.all nestedSearchCap fty then
            let shown ← try
                let s ← withOptions (fun o => pp.maxSteps.set (pp.proofs.set o false) 200) (ppExpr fty)
                pure (toString s)
              catch _ => pure "?"
            let shown := if shown.length > 120 then String.mk (shown.toList.take 120) ++ "…" else shown
            out := out.push s!"constructor `{shortCtor}`, argument `{label} : {shown}`: `{v.name}` occurs nested inside `{h}`"
          else
            pure ()
        | none =>
          -- the argument's own head is not a plain constant application (a function type, a bound variable, …): too oddly
          -- shaped to confidently name the outer type former, even though `v`'s type occurs somewhere inside it
          if containsHeadOf v.all nestedSearchCap fty then
            out := out.push
              s!"constructor `{shortCtor}`, argument `{label}`: a nested occurrence exists (kernel reports numNested = {v.numNested})"
          else
            pure ()
      return out
  | _ => return #[]

/-- every constructor of `v`, each constructor's fields in turn -/
def describeNested (env : Environment) (v : InductiveVal) : MetaM (Array String) := do
  let mut out := #[]
  for ctorName in v.ctors do
    out := out ++ (← describeCtor env v ctorName)
  return out

/-- `describeNested` under its own heartbeat budget, every exception (runtime ones included) turned into `Except` — the
`roundtripGuard` idiom of Jinshi/Roundtrip.lean -/
def nestedGuard (env : Environment) (v : InductiveVal) : MetaM (Except String (Array String)) :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := nestedHeartbeats * 1000 }) <|
    withCurrHeartbeats <|
      tryCatchRuntimeEx (Except.ok <$> describeNested env v) fun e => do
        let msg ← try e.toMessageData.toString catch _ => pure "exception"
        return Except.error msg

def nested (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  let mut count := 0
  for (m, n, ci) in selected c env do
    let some v := (match ci with | .inductInfo v => some v | _ => none) | continue
    unless okName n do continue
    unless v.isNested do continue
    count := count + 1
    let guarded ← nestedGuard env v
    let occs := match guarded with
      | .ok os => os
      | .error msg => #[s!"the occurrence walk did not complete: {msg}"]
    let occDetail :=
      if occs.isEmpty then
        "no constructor argument's occurrence could be structurally characterized"
      else
        "; ".intercalate occs.toList
    out := out.push { check := "nested", severity := "info", module := m, name := n, line := ← lineOf n,
                      detail := s!"nested inductive, numNested = {v.numNested}: {occDetail} — not separately re-verified by this check: " ++
                        "every declaration of the module, this one included, is already re-type-checked at the whole-module level by " ++
                        "`replay` (leanchecker) and `lean4lean`; `nested` exists to make it visible and searchable, not to duplicate " ++
                        "that verification" }
  out := out.push { check := "nested", severity := "info", module := c.mods.headD .anonymous, name := .anonymous,
                    detail := s!"{count} nested inductive declaration(s) found" }
  return out

end Jinshi
