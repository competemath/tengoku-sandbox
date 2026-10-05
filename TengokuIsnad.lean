/-
isnad: the identity of a theorem, recomputed from the compiled environment (docs/isnad.md).

For every theorem of the selected modules this prints one line, tab-separated,

  isnad1 <name> <module> <kind> <hyps> <vars> <nodes> <canonical> <shape> <vocabulary>

and nothing is hashed here: the canonical strings are hashed by scripts/isnad.py (sha256), so the hashing is auditable on its own and
independent of Lean's `String.hash`. Records are sorted by (module, name): two runs give identical bytes.

  lake build tengoku-isnad
  lake env .lake/build/bin/tengoku-isnad --module Tengoku.Seed.Logic.Basic
  lake env .lake/build/bin/tengoku-isnad --import Init.Data.Nat.Basic --module Init.Data.Nat.Basic --name Nat.add_comm

The canonical form (version 1) is an S-expression and a pure function of the elaborated statement: bound variables are de Bruijn indices, universe
parameters are numbered by first appearance, constants are quoted strings of their cleaned name (macro scopes and `private` prefixes removed), proof
terms are replaced by `⊢`. The theorem's own name, its module, its binder names, its docstring and its proof do not enter it.
-/
import Lean
open Lean

namespace Isnad

-- BEGIN CANON (scripts/isnad.py leaves this block to the tests: the same code is run as a command on Leak IV, which cannot run an executable)
structure St where
  params : Array Name := #[]
  consts : Array Name := #[]
  nodes : Nat := 0

abbrev M := StateM St

/-- The name a constant is written by: macro scopes removed. A `private` name keeps its whole form (`_private.<Module>.0.<name>`): two
different private constants called `p` in two modules are different constants, and a private constant cannot be referenced from another module, so a
statement that mentions one is module-specific by nature. -/
def cleanName (n : Name) : Name :=
  n.eraseMacroScopes

def lvl : Level → M String
  | .zero => pure "0"
  | .succ l => do return s!"(S {← lvl l})"
  | .max a b => do return s!"(M {← lvl a} {← lvl b})"
  | .imax a b => do return s!"(I {← lvl a} {← lvl b})"
  | .param n => do
      let s ← get
      match s.params.findIdx? (· == n) with
      | some i => return s!"p{i}"
      | none =>
        set { s with params := s.params.push n }
        return s!"p{s.params.size - 1}"
  | .mvar _ => pure "?"

/-- A proof term is not part of a statement: a theorem, or one of the few constants whose application is a proof by construction. -/
def proofHead (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => n == ``Eq.refl || n == ``rfl || n == ``of_decide_eq_true || n == ``Eq.mpr || n == ``Eq.mp

/-- Which of the first `k` arguments of an applied constant sit at instance-implicit parameters of its type. A bound instance variable is an
instance argument too: what counts is the parameter, not what the argument looks like. -/
def instMask (env : Environment) (n : Name) (k : Nat) : Array Bool := Id.run do
  let some ci := env.find? n | return Array.replicate k false
  let mut t := ci.type
  let mut out : Array Bool := #[]
  for _ in [0:k] do
    match t with
    | .forallE _ _ b bi =>
      out := out.push (bi == .instImplicit)
      t := b
    | _ => out := out.push false
  return out

/-- A constant. `shape = false`: its cleaned name as a quoted string (self-delimiting, so no two statements share a canonical string by the way
names and separators run together) with its universe levels in braces. `shape = true`: `c<order of first appearance>/<arity>`. -/
def constStr (shape : Bool) (n0 : Name) (ls : List Level) (arity : Nat) : M String := do
  let n := cleanName n0
  if shape then
    let s ← get
    match s.consts.findIdx? (· == n) with
    | some i => return s!"c{i}/{arity}"
    | none =>
      set { s with consts := s.consts.push n }
      return s!"c{s.consts.size - 1}/{arity}"
  else
    let mut out := (toString n).quote
    if !ls.isEmpty then
      let strs ← ls.mapM lvl
      out := out ++ "{" ++ " ".intercalate strs ++ "}"
    return out

/-- The canonical form: an S-expression, every node `(head child…)` or an atom, children separated by one space. -/
partial def ser (env : Environment) (shape : Bool) (e : Expr) : M String := do
  modify fun s => { s with nodes := s.nodes + 1 }
  match e with
  | .bvar i => return s!"v{i}"
  | .fvar _ => return "f"
  | .mvar _ => return "?"
  | .sort l => return s!"(T {← lvl l})"
  | .const n ls => constStr shape n ls 0
  | .mdata _ e' => ser env shape e'
  | .lit (.natVal n) => return (if shape then "#" else s!"n{n}")
  | .lit (.strVal s) => return (if shape then "s" else s!"s{s.quote}")
  | .proj sn i e' => do
      let h ← constStr shape sn [] 1
      return s!"(π{i} {h} {← ser env shape e'})"
  | .lam _ t b _ => do return s!"(λ {← ser env shape t} {← ser env shape b})"
  | .forallE _ t b _ => do return s!"(Π {← ser env shape t} {← ser env shape b})"
  | .letE _ t v b _ => do return s!"(L {← ser env shape t} {← ser env shape v} {← ser env shape b})"
  | .app .. =>
    let f := e.getAppFn
    let args0 := e.getAppArgs
    match f with
    | .const n ls =>
      if proofHead env n then return "⊢"
      let mask := instMask env n args0.size
      let args := if shape then (args0.zip mask).filterMap (fun (a, inst) => if inst then none else some a) else args0
      let hd ← constStr shape n ls args.size
      let mut out := s!"({hd}"
      for a in args do
        out := out ++ " " ++ (← ser env shape a)
      return out ++ ")"
    | _ =>
      let hd ← ser env shape f
      let mut out := s!"({hd}"
      for a in args0 do
        out := out ++ " " ++ (← ser env shape a)
      return out ++ ")"

/-- (canonical string, expression nodes) of a statement. -/
def canonical (env : Environment) (t : Expr) : String × Nat :=
  let (s, st) := (ser env false t).run {}
  (s, st.nodes)

def shapeOf (env : Environment) (t : Expr) : String :=
  ((ser env true t).run {}).1

partial def codomainIsProp (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => codomainIsProp b
  | .sort .zero => true
  | _ => false

/-- A binder type that is a proposition: a hypothesis, not a variable. Heuristic, and part of the v1 recipe. -/
partial def isPropLike (env : Environment) (t : Expr) : Bool :=
  match t with
  | .forallE _ _ b _ => isPropLike env b
  | _ =>
    match t.getAppFn with
    | .const n _ => match env.find? n with
        | some ci => codomainIsProp ci.type
        | none => false
    | _ => false

/-- (conclusion, instance binders, hypotheses, variables) of a statement. -/
partial def profile (env : Environment) (e : Expr) (insts hyps vars : Nat) : Expr × Nat × Nat × Nat :=
  match e with
  | .forallE _ t b bi =>
    if bi == .instImplicit then profile env b (insts + 1) hyps vars
    else if isPropLike env t then profile env b insts (hyps + 1) vars
    else profile env b insts hyps (vars + 1)
  | _ => (e, insts, hyps, vars)

/-- Names the lab-measured population leaves out: generated and internal declarations. -/
def okName (n : Name) : Bool :=
  let s := n.getString!
  !(n.isInternal || n.hasMacroScopes || s.startsWith "eq_" || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "sizeOf_" || s == "injEq" || s.startsWith "_")

/-- What the theorem concludes: a short readable code. A known head has a fixed code; any other head is the last component of its
cleaned name, lower-cased, letters and digits only, at most 8 characters (no `.` ever: the id is split on dots). -/
def kindOf (concl : Expr) : String :=
  match concl.getAppFn with
  | .const c _ =>
    let n := cleanName c
    if n == ``Eq then "eq"
    else if n == ``LE.le || n == ``GE.ge then "le"
    else if n == ``LT.lt || n == ``GT.gt then "lt"
    else if n == ``Ne then "ne"
    else if n == ``Iff then "iff"
    else if n == ``Exists then "ex"
    else if n == ``And then "and"
    else if n == ``Or then "or"
    else if n == ``Not then "not"
    else
      let last := match n with
        | .str _ s => s
        | _ => "x"
      let chars := (last.toList.filter (fun ch => ch.isAlphanum && ch.toNat < 128)).map Char.toLower
      let k := String.ofList (chars.take 8)
      if k.isEmpty then "x" else k
  | .bvar _ => "var"
  | .sort _ => "sort"
  | _ => "other"

/-- Logical vocabulary left out of a statement's vocabulary: it says nothing about which objects the statement is about. -/
def stop : List Name := [``Eq, ``And, ``Or, ``Not, ``Iff, ``Exists, ``True, ``False, ``OfNat.ofNat, ``Ne]

/-- The sorted, distinct, comma-joined cleaned names of the constants a statement mentions (no logic, no instances). -/
def vocabOf (env : Environment) (t : Expr) : String :=
  let cs := t.getUsedConstants.filter (fun c => !(stop.contains c) && !(Lean.Meta.isInstanceCore env c))
  let names := ((cs.map (fun c => (toString (cleanName c)).quote)).qsort (· < ·)).toList
  ",".intercalate (names.eraseDups)

/-- The fields of a theorem's record: name, module, kind, hypotheses, variables, nodes, canonical, shape, vocabulary. -/
def fields (env : Environment) (n : Name) (modName : String) (t : Expr) : List String :=
  let (s, nodes) := canonical env t
  let (concl, _, hyps, vars) := profile env t 0 0 0
  [toString (cleanName n), modName, kindOf concl, toString hyps, toString vars, toString nodes, s, shapeOf env t, vocabOf env t]

/-- One output line of a theorem. -/
def line (env : Environment) (n : Name) (modName : String) (t : Expr) : String :=
  "\t".intercalate ("isnad1" :: fields env n modName t)
-- END CANON

/-- The records of the theorems of `mods` (module prefixes), or only those called `names` when given, sorted by (module, name). -/
def records (env : Environment) (mods : List Name) (names : List Name) : Array (String × String × String) := Id.run do
  let mut out : Array (String × String × String) := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    if !mods.isEmpty && !mods.any (·.isPrefixOf m) then continue
    if !okName n then continue
    if !names.isEmpty && !names.contains n then continue
    out := out.push (m.toString, n.toString, line env n m.toString ci.type)
  return out.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)

end Isnad

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  let opt (k : String) : List String := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == k then some b else none
  let mods := (opt "--module").map String.toName
  let names := (opt "--name").map String.toName
  let imports := (opt "--import").map String.toName ++ mods
  if imports.isEmpty then
    IO.eprintln "usage: tengoku-isnad --module <M> [--module <M>…] [--import <M>…] [--name <theorem>…]"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (imports.eraseDups.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let rs := Isnad.records env mods names
  for (_, _, l) in rs do IO.println l
  IO.eprintln s!"isnad: {rs.size} theorems"
  return (if !names.isEmpty && rs.size < names.length then 1 else 0)
