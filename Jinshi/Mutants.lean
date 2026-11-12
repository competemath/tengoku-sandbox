/-
mutants — differential kernel fuzzing seeded from the tree's own proofs (docs/jinshi.md, head K).

The kernel is the single point of trust, and this toolchain carries two implementations of it that Jinshi can run (Lean's own, in
this process and through `leanchecker`; lean4lean, a kernel written in Lean). If they ever disagree on a declaration, one of them
has a bug, and a real proof is the best seed for finding such a disagreement: mutate it slightly and ask every kernel.

For the first N theorems (by name, JINSHI_MUTANTS_PER_MODULE, default 20) of each examined module, a fixed list of mutation
operators is applied, each at the first position of the proof where it applies (no randomness: the same input gives the same
mutants):

  swapArgs     two arguments of an application that have the same type (isDefEq) exchanged
  subterm      a subterm replaced by another subterm of the term with the same inferred type
  reflOther    `Eq.refl a` made `Eq.refl b` for another `b : α` found in the term (ill-typed unless `a ≡ b`)
  dropArg      the last argument of an application dropped (ill-typed)
  proofOther   a proof replaced by a proof of a different proposition from the same term (ill-typed; never `sorryAx`)
  universe     the first universe level of a constant raised by one
  literal      a `Nat` literal of the STATEMENT raised by one, the proof kept (accepted only when the proof never looks at it)
  eta          a subterm of function type eta-expanded (well-typed: every kernel must accept)

Each mutant is a theorem `<original>_mut<k>` judged in this process by Lean's kernel (`Environment.addDeclCore` with checking, under
a heartbeat cap; the verdict and the kind of refusal are the finding's detail, severity `info`), and, when an output directory is
given (`--mutants-out DIR` or JINSHI_MUTANTS_OUT), written UNCHECKED (`addDeclCore … (doCheck := false)`, as `debug.skipKernelTC`
does) into an .olean of its own: the module `JinshiMutants.<Module>.M<k>`, which imports the examined module and holds exactly one
declaration, so that `leanchecker` and `lean4lean` judge exactly one mutant per run. `scripts/jinshi/mutants.py` runs them and
reports a disagreement between kernels as `fail`. DIR/generated.jsonl repeats the findings for the script.

The examination writes files and is costly, so it is off in the all-examinations run: it runs when `--check` names it, and, in the
all-examinations run, only on a module whose module doc (`/-! … -/`) contains `jinshi: mutants` (the fixture).
-/
import Jinshi.Base
open Lean Meta

namespace Jinshi

/-- the directory the mutant modules are written to: `--mutants-out` (the executable sets this) or JINSHI_MUTANTS_OUT -/
initialize mutantsOutRef : IO.Ref (Option String) ← IO.mkRef none

def mutantsOutDir : IO (Option String) := do
  if let some d ← mutantsOutRef.get then return some d
  IO.getEnv "JINSHI_MUTANTS_OUT"

/-- theorems per module (the first N by name): JINSHI_MUTANTS_PER_MODULE, default 20 -/
def mutantsPerModule : IO Nat := do
  return ((← IO.getEnv "JINSHI_MUTANTS_PER_MODULE").bind fun s => s.trimAscii.toString.toNat?).getD 20

/-- heartbeats (in the option's unit of 1000) each inference, comparison and kernel check may spend -/
def mutantsHeartbeats : Nat := 50000

/-- a proof of more nodes than this is not mutated (the kernel check of a mutant costs what the original's did) -/
def mutantsMaxNodes : Nat := 5000

/-- the closed subterms of a proof looked at (the first ones in pre-order) -/
def mutantsMaxSubterms : Nat := 200

/-- run `x` with its own heartbeat budget, every exception (runtime ones included) made `none` -/
def mutantsGuard (x : MetaM α) : MetaM (Option α) :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := mutantsHeartbeats * 1000 }) <|
    withCurrHeartbeats <|
      tryCatchRuntimeEx (some <$> x) fun _ => pure none

/-- the number of nodes of `e`, counting stops at `cap` -/
partial def mutantsSize (e : Expr) (cap : Nat) (acc : Nat := 0) : Nat :=
  if acc ≥ cap then acc else
  match e with
  | .app f a => mutantsSize a cap (mutantsSize f cap (acc + 1))
  | .lam _ t b _ | .forallE _ t b _ => mutantsSize b cap (mutantsSize t cap (acc + 1))
  | .letE _ t v b _ => mutantsSize b cap (mutantsSize v cap (mutantsSize t cap (acc + 1)))
  | .mdata _ b | .proj _ _ b => mutantsSize b cap (acc + 1)
  | _ => acc + 1

/-- the closed subterms of `e` (no loose bound variables) in pre-order, left to right, without repeats, the first
`mutantsMaxSubterms` of them -/
partial def mutantsSubterms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if acc.size ≥ mutantsMaxSubterms then acc else
  let acc := if !e.hasLooseBVars && !acc.contains e then acc.push e else acc
  match e with
  | .app f a => mutantsSubterms a (mutantsSubterms f acc)
  | .lam _ t b _ | .forallE _ t b _ => mutantsSubterms b (mutantsSubterms t acc)
  | .letE _ t v b _ => mutantsSubterms b (mutantsSubterms v (mutantsSubterms t acc))
  | .mdata _ b | .proj _ _ b => mutantsSubterms b acc
  | _ => acc

/-- every occurrence of `s` in `e` replaced by `t` -/
def mutantsReplace (e s t : Expr) : Expr :=
  e.replace fun x => if x == s then some t else none

/-- the first literal `.natVal` of `e` -/
partial def mutantsFirstLit (e : Expr) : Option Expr :=
  match e with
  | .lit (.natVal _) => some e
  | .app f a => mutantsFirstLit f <|> mutantsFirstLit a
  | .lam _ t b _ | .forallE _ t b _ => mutantsFirstLit t <|> mutantsFirstLit b
  | .letE _ t v b _ => mutantsFirstLit t <|> mutantsFirstLit v <|> mutantsFirstLit b
  | .mdata _ b | .proj _ _ b => mutantsFirstLit b
  | _ => none

/-- the first constant of `e` that has a universe level -/
partial def mutantsFirstLeveled (e : Expr) : Option Expr :=
  match e with
  | .const _ (_ :: _) => some e
  | .app f a => mutantsFirstLeveled f <|> mutantsFirstLeveled a
  | .lam _ t b _ | .forallE _ t b _ => mutantsFirstLeveled t <|> mutantsFirstLeveled b
  | .letE _ t v b _ => mutantsFirstLeveled t <|> mutantsFirstLeveled v <|> mutantsFirstLeveled b
  | .mdata _ b | .proj _ _ b => mutantsFirstLeveled b
  | _ => none

/-- a subterm with what is known about it -/
structure MutantsNode where
  e : Expr
  ty : Expr
  isProof : Bool
  isType : Bool

/-- the same type: structurally, or by `isDefEq` under the cap -/
def mutantsSameType (a b : MutantsNode) : MetaM Bool := do
  if a.ty == b.ty then return true
  return (← mutantsGuard (withReducible (isDefEq a.ty b.ty))).getD false

/-- a mutant: the operator's name, the statement, the proof -/
structure Mutant where
  op : String
  type : Expr
  value : Expr

/-- the subterms of the proof's body (and of the statement, as candidates), typed -/
def mutantsNodes (body ty : Expr) : MetaM (Array MutantsNode) := do
  let mut nodes := #[]
  let bs := mutantsSubterms body
  for e in bs ++ (mutantsSubterms ty).filter (fun e => !bs.contains e) do
    if e.isSort then continue
    let some info ← mutantsGuard do
        let t ← instantiateMVars (← inferType e)
        pure (t, ← isProof e, ← isType e)
      | continue
    let (t, p, k) := info
    nodes := nodes.push { e, ty := t, isProof := p, isType := k }
  return nodes

/-- every mutant of the theorem `ty := value`, one per operator at the first position where the operator applies -/
def mutantsOf (ty value : Expr) : MetaM (Array Mutant) := do
  let mut out := #[]
  -- the statement's operators: a literal raised, the proof kept
  if let some (.lit (.natVal k)) := mutantsFirstLit ty then
    out := out.push { op := "literal", type := mutantsReplace ty (.lit (.natVal k)) (.lit (.natVal (k + 1))), value }
  -- the proof's operators, under its binders
  let bodyMutants ← mutantsGuard <| lambdaTelescope value fun xs body => do
    let nodes ← mutantsNodes body ty
    let bs := mutantsSubterms body
    let bodyNodes := nodes.filter fun n => bs.contains n.e
    let mut ms : Array (String × Expr) := #[]
    -- swapArgs: the first application two of whose arguments have the same type
    let mut found := false
    for n in bodyNodes do
      if found then break
      let args := n.e.getAppArgs
      if args.size < 2 then continue
      for i in [:args.size] do
        if found then break
        for j in [i+1:args.size] do
          if args[i]! == args[j]! then continue
          let some (ti : Expr) ← mutantsGuard (do instantiateMVars (← inferType args[i]!)) | continue
          let some (tj : Expr) ← mutantsGuard (do instantiateMVars (← inferType args[j]!)) | continue
          if ← mutantsSameType { e := args[i]!, ty := ti, isProof := false, isType := false } { e := args[j]!, ty := tj, isProof := false, isType := false } then
            let swapped := mkAppN n.e.getAppFn ((args.set! i args[j]!).set! j args[i]!)
            ms := ms.push ("swapArgs", mutantsReplace body n.e swapped)
            found := true
            break
    -- subterm: the first proper, non-type subterm for which another subterm has the same type
    found := false
    for n in bodyNodes do
      if found then break
      if n.e == body || n.isType then continue
      for m in nodes do
        if m.e == n.e || m.isType then continue
        if ← mutantsSameType n m then
          ms := ms.push ("subterm", mutantsReplace body n.e m.e)
          found := true
          break
    -- reflOther: `Eq.refl a` made `Eq.refl b`
    found := false
    for n in bodyNodes do
      if found then break
      let .app (.app (.const ``Eq.refl ls) α) a := n.e | continue
      for m in nodes do
        if m.e == a || m.isProof || m.isType then continue
        if ← mutantsSameType { e := a, ty := α, isProof := false, isType := false } m then
          ms := ms.push ("reflOther", mutantsReplace body n.e (mkApp2 (.const ``Eq.refl ls) α m.e))
          found := true
          break
    -- dropArg: the first application loses its last argument
    for n in bodyNodes do
      if n.e.isApp then
        ms := ms.push ("dropArg", mutantsReplace body n.e n.e.appFn!)
        break
    -- proofOther: the first proper proof subterm replaced by a proof of a different proposition
    found := false
    for n in bodyNodes do
      if found then break
      if n.e == body || !n.isProof then continue
      for m in nodes do
        if m.e == n.e || !m.isProof then continue
        if !(← mutantsSameType n m) then
          ms := ms.push ("proofOther", mutantsReplace body n.e m.e)
          found := true
          break
    -- universe: the first constant with a level gets its first level raised
    if let some c@(.const cn (l :: ls)) := mutantsFirstLeveled body then
      ms := ms.push ("universe", mutantsReplace body c (.const cn (mkLevelSucc l :: ls)))
    -- eta: the first subterm of function type that is not a lambda, eta-expanded (the kernels must accept)
    for n in bodyNodes do
      if n.e.isLambda || n.isType then continue
      let some w ← mutantsGuard (whnf n.ty) | continue
      unless w.isForall do continue
      let some expanded ← mutantsGuard (etaExpand n.e) | continue
      if expanded == n.e then continue
      ms := ms.push ("eta", mutantsReplace body n.e expanded)
      break
    let mut res := #[]
    for (op, b) in ms do
      if b == body then continue
      res := res.push (op, ← mkLambdaFVars xs b)
    return res
  for (op, v) in bodyMutants.getD #[] do
    out := out.push { op, type := ty, value := v }
  return out

def mutantsKind : Kernel.Exception → String
  | .unknownConstant .. => "unknownConstant"
  | .alreadyDeclared .. => "alreadyDeclared"
  | .declTypeMismatch .. => "declTypeMismatch"
  | .declHasMVars .. => "declHasMVars"
  | .declHasFVars .. => "declHasFVars"
  | .funExpected .. => "funExpected"
  | .typeExpected .. => "typeExpected"
  | .letTypeMismatch .. => "letTypeMismatch"
  | .exprTypeMismatch .. => "exprTypeMismatch"
  | .appTypeMismatch .. => "appTypeMismatch"
  | .invalidProj .. => "invalidProj"
  | .thmTypeIsNotProp .. => "thmTypeIsNotProp"
  | .other _ => "other"
  | .deterministicTimeout => "deterministicTimeout"
  | .excessiveMemory => "excessiveMemory"
  | .deepRecursion => "deepRecursion"
  | .interrupted => "interrupted"

/-- Lean's kernel on the declaration, with checking, under the heartbeat cap: `accept` or `reject(<kind>)` -/
def mutantsVerdict (env : Environment) (decl : Declaration) : String :=
  match env.addDeclCore (mutantsHeartbeats * 1000).toUSize 512 decl none true with
  | .ok _ => "accept"
  | .error e => s!"reject({mutantsKind e})"

/-- the declaration added UNCHECKED to `env` (as `debug.skipKernelTC` would) and written as the module `modName` at `path` -/
def mutantsWrite (env : Environment) (modName : Name) (path : System.FilePath) (decl : Declaration) : IO (Option String) := do
  match (env.setMainModule modName).addDeclCore 0 512 decl none false with
  | .error e => return some s!"could not add unchecked: {mutantsKind e}"
  | .ok env' =>
    try
      if let some d := path.parent then IO.FS.createDirAll d
      writeModule env' path (writeIR := false)
      return none
    catch e => return some s!"could not write: {e}"

/-- whether a module opts in to the examination in the all-examinations run -/
def mutantsOptedIn (env : Environment) (m : Name) : Bool :=
  match getModuleDoc? env m with
  | some docs => docs.any fun d => (d.doc.splitOn "jinshi: mutants").length > 1
  | none => false

def mutants (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let named := c.checks.contains "mutants"
  let outDir ← mutantsOutDir
  let perModule ← mutantsPerModule
  let mut out := #[]
  let mut byModule : Array (Name × Array (Name × ConstantInfo)) := #[]
  for (m, n, ci) in selected c env do
    let .thmInfo _ := ci | continue
    unless okName n do continue
    if byModule.back?.map (·.1) == some m then
      let last := byModule.back!
      if last.2.size < perModule then byModule := byModule.pop.push (m, last.2.push (n, ci))
    else
      byModule := byModule.push (m, #[(n, ci)])
  for (m, thms) in byModule do
    unless named || mutantsOptedIn env m do continue
    -- the environment the kernels will see: the examined module alone (its olean's imports), one per examined module
    let base? ← try
        some <$> importModules #[{ module := m }] {} (trustLevel := 0)
      catch _ => pure none
    let base ← match base? with
      | some b => pure b
      | none =>
        out := out.push { check := "mutants", severity := "warn", module := m, name := .anonymous,
                          detail := "the module could not be imported on its own: no mutants" }
        continue
    let mut k := 0
    for (n, ci) in thms do
      let .thmInfo t := ci | continue
      let value := t.value
      if mutantsSize value mutantsMaxNodes ≥ mutantsMaxNodes then
        out := out.push { check := "mutants", severity := "info", module := m, name := n, line := ← lineOf n,
                          detail := s!"not mutated: the proof has {mutantsMaxNodes} nodes or more" }
        continue
      let ms ← try mutantsOf ci.type value catch _ => pure #[]
      let line ← lineOf n
      for mu in ms do
        k := k + 1
        let mutName := n.appendAfter s!"_mut{k}"
        let decl := Declaration.thmDecl { name := mutName, levelParams := ci.levelParams, type := mu.type, value := mu.value }
        let verdict := mutantsVerdict base decl
        let modName := (`JinshiMutants ++ m).str s!"M{k}"
        let mut detail := s!"lean: {verdict}; op: {mu.op}; from: {n}"
        if let some dir := outDir then
          let path : System.FilePath := (modName.components.foldl (fun (p : System.FilePath) c => p / c.toString) ⟨dir⟩).addExtension "olean"
          match ← mutantsWrite base modName path decl with
          | none => detail := detail ++ s!"; module: {modName}"
          | some err => detail := detail ++ s!"; module: none ({err})"
        out := out.push { check := "mutants", severity := "info", module := m, name := mutName, line, detail }
  if let some dir := outDir then
    try
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir / "generated.jsonl") ("".intercalate (out.toList.map fun f => f.json ++ "\n"))
    catch _ => pure ()
  return out

end Jinshi
