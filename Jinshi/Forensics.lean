/-
Jinshi, the `forensics` examination (docs/jinshi.md): what the PROOF TERM of a theorem tells about how the kernel accepted it, the
places where the kernel's own machinery is stressed or trusted most. The proof term of every theorem of an examined module (the
seed included) is walked once, structurally, with a visited set on structural equality (proof terms share subterms heavily, and
can be huge: the walk stops at a cap), and five things are collected:

  1. big literals (warn)       a `Nat` literal ≥ 2^64 in the proof or the statement: the kernel's bignum arithmetic checked it
  2. decide on a big prop (info) a `Decidable.decide`/`of_decide_eq_true`/`Nat.decEq`-family application whose proposition has more
                               than 200 nodes: the kernel evaluated a decision procedure of that size
  3. cast chains (info)        nested `Eq.mpr`/`Eq.mp`/`cast`/`Eq.rec` deeper than 50: kernel reduction carries the goal through them
  4. proof vs statement (info) a proof of more than 500× the statement's nodes (automation output, fragile); a `rfl`-class proof of
                               a statement of 30 nodes or more (the kernel's definitional unfolding is the whole proof)
  5. trusted heads (warn)      the proof mentions `Lean.ofReduceBool`/`ofReduceNat`/`trustCompiler`/`sorryAx`, or a constant that is
                               `unsafe`, `implemented_by` or `extern` (the kernel checked its Lean definition, not the code that runs;
                               the Nat operations the kernel computes itself are exempt, they are category 1's business)

One finding per theorem per category. Nothing is elaborated: everything is read from the compiled environment.
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-! ## forensics — what the proof term says about how the kernel accepted it -/

/-- distinct nodes walked per theorem before the walk gives up -/
def forensicsCap : Nat := 2000000
/-- raw nodes counted in a decided proposition before the count gives up (only "more than 200" matters) -/
def forensicsPropCap : Nat := 20000

def castHeads : List Name := [``Eq.mpr, ``Eq.mp, ``cast, ``Eq.rec, ``Eq.ndrec]
/-- heads whose first argument is the proposition decided -/
def decideHeads : List Name := [``Decidable.decide, ``of_decide_eq_true, ``of_decide_eq_false, ``decide_eq_true]
/-- the `Nat.decEq` family: the arguments together are the proposition decided -/
def decEqHeads : List Name :=
  [``Nat.decEq, ``Nat.decLt, ``Nat.decLe, ``instDecidableEqNat, `Nat.decidableBallLT, `Nat.decidableBallLE,
   `Nat.decidableExistsLT, `Nat.decidableExistsLE, `Nat.decidableForallFin, `Nat.decidableExistsFin]
/-- a proof that is one of these applied to the statement's own terms rests on the kernel's definitional unfolding alone -/
def rflHeads : List Name := [``rfl, ``Eq.refl, ``HEq.refl, ``HEq.rfl, ``Iff.refl, ``Iff.rfl, ``trivial, ``True.intro]
/-- the Nat operations the kernel computes itself (its bignum code, never the compiled `extern`): mentioning one trusts no compiler -/
def kernelNat : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
   ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe]

/-- `some kind` when a proof that mentions `n` was accepted on something other than a Lean definition the kernel checked -/
def trustedKind (env : Environment) (n : Name) : Option String :=
  if n == `Lean.ofReduceBool || n == `Lean.ofReduceNat then some "the compiler's answer taken as proof"
  else if n == `Lean.trustCompiler then some "trustCompiler"
  else if n == ``sorryAx then some "sorry"
  else if kernelNat.contains n then none
  else match env.find? n with
    | some ci =>
      if ci.isUnsafe then some "unsafe"
      else if (Compiler.implementedByAttr.getParam? env n).isSome then some "implemented_by"
      else if isExtern env n then some "extern"
      else none
    | none => none

/-- raw (undeduplicated) node count of an expression, stopping at `cap` -/
partial def rawSize (cap : Nat) (e : Expr) (acc : Nat := 0) : Nat :=
  if acc ≥ cap then acc else
  match e with
  | .app f a => rawSize cap a (rawSize cap f (acc + 1))
  | .lam _ t b _ | .forallE _ t b _ => rawSize cap b (rawSize cap t (acc + 1))
  | .letE _ t v b _ => rawSize cap b (rawSize cap v (rawSize cap t (acc + 1)))
  | .mdata _ b | .proj _ _ b => rawSize cap b (acc + 1)
  | _ => acc + 1

/-- what one walk of a term collects -/
structure Walk where
  /-- distinct nodes (structurally): the spine of an application counts one per argument -/
  nodes : Nat := 0
  capped : Bool := false
  /-- literals ≥ 2^64, and the digit count of the largest -/
  bigLits : Nat := 0
  bigDigits : Nat := 0
  /-- the largest proposition a decide-family head was applied to, and that head -/
  decideNodes : Nat := 0
  decideHead : Name := .anonymous
  castDepth : Nat := 0
  /-- the trusted constants mentioned, each with its kind -/
  trusted : Array (Name × String) := #[]

/-- the verdict on a constant, kept across theorems (a round mentions the same constants again and again) -/
abbrev TrustCache := Std.HashMap Name (Option String)

/-- one structural walk of `root`: every distinct subterm once, an explicit stack (proof terms are deep), stopping at `cap` -/
def walkTerm (env : Environment) (cache : TrustCache) (root : Expr) (cap : Nat) : Walk × TrustCache := Id.run do
  let mut w : Walk := {}
  let mut cache := cache
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array (Expr × Nat) := #[(root, 0)]
  while !stack.isEmpty do
    let (e, d) := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    if w.nodes ≥ cap then
      w := { w with capped := true }
      break
    seen := seen.insert e
    w := { w with nodes := w.nodes + 1 }
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      w := { w with nodes := w.nodes + args.size - 1 }
      let mut d' := d
      if let .const c _ := fn then
        if castHeads.contains c then
          d' := d + 1
          if d' > w.castDepth then w := { w with castDepth := d' }
        if decideHeads.contains c && args.size > 0 then
          let k := rawSize forensicsPropCap args[0]!
          if k > w.decideNodes then w := { w with decideNodes := k, decideHead := c }
        else if decEqHeads.contains c && args.size > 0 then
          let k := args.foldl (fun acc a => rawSize forensicsPropCap a acc) 0
          if k > w.decideNodes then w := { w with decideNodes := k, decideHead := c }
      stack := stack.push (fn, d')
      for a in args do stack := stack.push (a, d')
    | .const c _ =>
      let kind ← match cache.get? c with
        | some k => pure k
        | none =>
          let k := trustedKind env c
          cache := cache.insert c k
          pure k
      if let some k := kind then w := { w with trusted := w.trusted.push (c, k) }
    | .lit (.natVal n) =>
      if n ≥ 2 ^ 64 then
        let digits := (toString n).length
        w := { w with bigLits := w.bigLits + 1, bigDigits := max w.bigDigits digits }
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push (t, d) |>.push (b, d)
    | .letE _ t v b _ => stack := stack.push (t, d) |>.push (v, d) |>.push (b, d)
    | .mdata _ b | .proj _ _ b => stack := stack.push (b, d)
    | _ => pure ()
  return (w, cache)

/-- the body of a proof under the binders the statement quantifies -/
def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | e => e

def forensics (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let mut out := #[]
  let mut cache : TrustCache := {}
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    let line ← lineOf n
    let (st, cache₁) := walkTerm env cache t.type forensicsCap
    let (pr, cache₂) := walkTerm env cache₁ t.value forensicsCap
    cache := cache₂
    let push (sev : String) (detail : String) : Array Finding → Array Finding := fun out =>
      out.push { check := "forensics", severity := sev, module := m, name := n, line, detail }
    -- 1. big literals
    if st.bigLits + pr.bigLits > 0 then
      let where' := if st.bigLits > 0 && pr.bigLits > 0 then "statement and proof" else if st.bigLits > 0 then "statement" else "proof"
      out := push "warn" s!"{st.bigLits + pr.bigLits} numeral(s) ≥ 2^64 in the {where'}, the largest of {max st.bigDigits pr.bigDigits} digits: checked by the kernel's bignum arithmetic" out
    -- 5. trusted heads
    unless pr.trusted.isEmpty do
      let parts := pr.trusted.toList.map (fun (k, kind) => s!"{k} ({kind})") |>.eraseDups
      let axiomatic := pr.trusted.any fun (_, kind) => kind.startsWith "the compiler" || kind == "trustCompiler" || kind == "sorry"
      let why := if axiomatic then "the kernel took the compiler's word, or a sorry, for part of this proof"
                 else "the kernel checked the Lean definition, the code that runs is another"
      out := push "warn" s!"proof mentions {", ".intercalate parts}: {why}" out
    -- 2. decide on a large proposition
    if pr.decideNodes > 200 then
      let shown := if pr.decideNodes ≥ forensicsPropCap then s!"≥ {forensicsPropCap}" else toString pr.decideNodes
      out := push "info" s!"decide on a proposition of {shown} nodes (`{pr.decideHead}`): the kernel evaluated a decision procedure of that size" out
    -- 3. cast chains
    if pr.castDepth > 50 then
      out := push "info" s!"cast chain of depth {pr.castDepth} (nested Eq.mpr/Eq.mp/cast/Eq.rec): kernel reduction carries the goal through every step" out
    -- 4. proof vs statement, when the walk completed
    if pr.capped then
      out := push "info" s!"proof term larger than the cap ({forensicsCap} nodes walked): the other findings cover what was walked, the proof-to-statement ratio was not judged" out
    else if st.capped then
      pure ()
    else
      if pr.nodes > 500 * st.nodes then
        out := push "info" s!"proof of {pr.nodes} nodes for a statement of {st.nodes} ({pr.nodes / st.nodes}×): likely automation output, fragile under a change of the seed" out
      else
        let body := stripLams t.value
        if let .const h _ := body.getAppFn then
          if rflHeads.contains h && body.getAppNumArgs ≤ 2 && st.nodes ≥ 30 then
            out := push "info" s!"nearly trivial: the proof is `{h}` (statement of {st.nodes} nodes): the kernel's definitional unfolding is the whole proof" out
  return out

end Jinshi
