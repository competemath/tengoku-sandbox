/-
entailed — the entailment oracle (docs/jinshi.md). The tree grows by translations and contributions; a theorem is worth more when it
is NOT a consequence of what the tree already had. For every theorem T of an examined module the tree itself is asked to prove T's
statement from OTHER theorems: Lean's library search (`Lean.Meta.LibrarySearch`, the engine of `exact?`) runs on a fresh goal of
T's type with the candidate lemmas restricted so that T and every constant of T's own module are excluded, and the subgoals a
candidate leaves are closed from the hypotheses alone (no `rfl`, no `trivial`: a lemma applied to the hypotheses is one step; a
computation is not an entailment). The glue of logic (`Eq.refl`, `Eq.symm`, `Eq.mp`, `id`, …) is not a candidate either. The
search unifies at `instances` transparency: a lemma whose conclusion merely computes to the statement (`3 + 0 = 3` for `tri 2 = 3`;
a hypothesis `True` for a predicate defined as `True`) does not entail it, one that is the statement up to instance paths does.
The seed's candidates are tried before any library's, so a theorem both entail is reported as the seed's (the stronger finding).

A proof the search finds is a CERTIFICATE only once it is re-checked: `Meta.check` on the term and `isDefEq` of its inferred type
with T's statement; a proof with unassigned metavariables, or one that after all mentions T or a theorem of T's module, is
discarded. Outcomes:

  warn  entailed by the seed: the lemmas used are all the seed's or Lean's own (a consequence of what the tree already had; a
        translation that adds no new claim)
  info  entailed by another library (tawatur of libraries), or by another module of its own library (redundancy)
  info  a seed theorem that is a one-step consequence of other seed theorems (the seed is informational only)
  info  a summary line per run: tried, entailed by the seed, entailed by a library, closed without a lemma, unknown, skipped

Nothing is said about a theorem the search cannot close within the cap: silence here means "not found", not "new".
Expensive on a real round: per theorem `JINSHI_ENTAILED_HEARTBEATS` (default 50000, ×1000 raw heartbeats), per module
`JINSHI_ENTAILED_MAX` theorems (default 50, in name order; the rest are counted as skipped); `JINSHI_ENTAILED_TIMING=1` prints
the time per theorem to stderr.
-/
import Jinshi.Base
import Jinshi.Duplicate
import Jinshi.Forensics
open Lean Meta Lean.Meta.LibrarySearch

namespace Jinshi

/-- applying one of these is logic, not a lemma: never a candidate, never reported as what entails a theorem -/
def entailGlue : List Name :=
  [``Eq.refl, ``rfl, ``Eq.symm, ``Eq.trans, ``Eq.mp, ``Eq.mpr, ``Eq.subst, ``Eq.rec, ``Eq.ndrec, ``cast, ``id, ``HEq.refl,
   ``Iff.refl, ``Iff.rfl, ``Iff.symm, ``Iff.mp, ``Iff.mpr, ``Iff.trans, ``Iff.intro, ``congrArg, ``congrFun, ``congr, ``funext,
   ``propext, ``absurd, ``False.elim, ``trivial, ``True.intro, ``of_eq_true, ``eq_true, ``eq_self, ``eq_false, ``of_eq_false,
   ``Classical.byContradiction, ``Decidable.byContradiction, ``Classical.byCases, ``Classical.em, ``Decidable.em,
   ``Decidable.not_not, ``Classical.not_not, ``Classical.choice, ``Quot.sound, ``Subsingleton.elim, ``proof_irrel]

/-- the per-theorem heartbeat cap (`JINSHI_ENTAILED_HEARTBEATS`, in thousands) and the per-module theorem cap (`JINSHI_ENTAILED_MAX`) -/
def entailLimits : IO (Nat × Nat × Bool) := do
  let num (k : String) (d : Nat) : IO Nat := do
    return match (← IO.getEnv k) with
      | some s => (s.trimAscii.toString.toNat?).getD d
      | none => d
  return (← num "JINSHI_ENTAILED_HEARTBEATS" 50000, ← num "JINSHI_ENTAILED_MAX" 50, (← IO.getEnv "JINSHI_ENTAILED_TIMING").isSome)

/-- what one search returns: the checked certificate, the lemmas it rests on (theorems and axioms, glue excluded), its size -/
structure Certificate where
  lemmas : Array Name
  nodes : Nat

/-- a theorem or an axiom that is not logic's glue: a lemma the certificate rests on -/
def isLemma (env : Environment) (k : Name) : Bool :=
  !entailGlue.contains k && (match env.find? k with | some (.thmInfo _) | some (.axiomInfo _) => true | _ => false)

/-- library search on a fresh goal of `type`, the candidates filtered by `keep`, each candidate followed by the hypotheses alone on
its subgoals; `some` only when the proof term is closed, mentions none of the forbidden constants, and re-checks against `type` -/
def entailSearch (type : Expr) (keep first : Name → Bool) (forbidden : Name → Bool) : MetaM (Option Certificate) := do
  let env ← getEnv
  let root ← mkFreshExprMVar type
  let (_, goal) ← root.mvarId!.intros
  -- the seed's candidates before any library's: a theorem both entail is the seed's finding (the stronger one)
  let order (cs : Array (Name × DeclMod)) : Array (Name × DeclMod) :=
    let cs := cs.filter fun (k, _) => keep k
    cs.filter (fun (k, _) => first k) ++ cs.filter (fun (k, _) => !first k)
  -- `instances` transparency: a lemma whose conclusion only computes to the statement (`3 + 0 = 3` for `tri 2 = 3`) is not an
  -- entailment; a statement that is the lemma's up to instance paths is
  let solved ← goal.withContext <| withTransparency .instances do
    let finder : CandidateFinder := fun ty => return order (← libSearchFindDecls ty)
    let cfg : ApplyConfig := { allowSynthFailures := true }
    let shouldAbort ← mkHeartbeatCheck 10
    -- the subgoals a candidate leaves: `solve_by_elim only [*]` (the local hypotheses, with symmetry; no `rfl`, no `trivial`)
    let close (goals : List MVarId) : MetaM (List MVarId) := do
      let sbe : SolveByElim.SolveByElimConfig :=
        { maxDepth := 6, exfalso := false, symm := true, commitIndependentGoals := true, transparency := ← getTransparency,
          constructor := false }
      let ⟨lemmas, ctx⟩ ← SolveByElim.mkAssumptionSet true true [] [] #[]
      SolveByElim.solveByElim sbe lemmas ctx goals
    let act : Candidate → MetaM (List MVarId) := fun ((g, mctx), (name, mod)) => do
      if ← shouldAbort then abortSpeculation
      setMCtx mctx
      let lem ← mkLibrarySearchLemma name mod
      let newGoals ← g.apply lem cfg
      let remaining ← close newGoals
      unless remaining.isEmpty do failure
      -- a solution with a metavariable left (an argument nothing determined) is not a proof: search on
      if (← instantiateMVars root).hasMVar then failure
      return []
    match ← tryOnEach act (← librarySearchSymm finder goal) with
    | none => pure true
    | some _ =>
      let stars := order (← getStarLemmas)
      if stars.isEmpty then pure false
      else
        let mctx ← getMCtx
        pure ((← tryOnEach act (stars.map ((goal, mctx), ·))).isNone)
  unless solved do return none
  let proof ← instantiateMVars root
  if proof.hasMVar then return none
  let used := proof.getUsedConstants
  if used.any forbidden then return none
  -- the certificate: the term type-checks (default transparency) and its type is the statement
  Meta.check proof
  unless ← isDefEq (← inferType proof) type do return none
  return some { lemmas := (used.filter (isLemma env)).qsort (·.toString < ·.toString), nodes := rawSize 2000000 proof }

def entailed (c : Ctx) : MetaM (Array Finding) := do
  let env ← getEnv
  let (hb, maxPerModule, timing) ← entailLimits
  let mut out := #[]
  let mut tried := 0
  let mut bySeed := 0
  let mut byLibrary := 0
  let mut byNothing := 0
  let mut unknown := 0
  let mut skipped := 0
  let mut perModule : NameMap Nat := {}
  let show_ (k : Name) := s!"`{k}` ({(moduleOf env k).getD `_})"
  let names (xs : Array Name) :=
    ", ".intercalate ((xs.toList.take 5).map show_) ++ (if xs.size > 5 then s!" and {xs.size - 5} more" else "")
  for (m, n, ci) in selected c env do
    let .thmInfo t := ci | continue
    unless okName n do continue
    if t.value.hasSorry then continue
    let done := perModule.getD m 0
    if done ≥ maxPerModule then
      skipped := skipped + 1
      continue
    perModule := perModule.insert m (done + 1)
    tried := tried + 1
    let t0 ← IO.monoMsNow
    let keep (k : Name) : Bool := k != n && !entailGlue.contains k && (moduleOf env k != some m)
    let forbidden (k : Name) : Bool := k == n || (moduleOf env k == some m && (env.find? k matches some (.thmInfo _)))
    let cert ← withoutModifyingState <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) <| withCurrHeartbeats <|
        tryCatchRuntimeEx (entailSearch t.type keep (isSeedOrCore c env) forbidden) (fun _ => pure none)
    let outcome ← do
      match cert with
      | none => unknown := unknown + 1; pure "unknown"
      | some cert =>
        if cert.lemmas.isEmpty then
          byNothing := byNothing + 1; pure "no lemma"
        else
          let selfSeed := c.seed.isPrefixOf m
          let lib := libraryOf m
          let foreign := cert.lemmas.filter fun k => !isSeedOrCore c env k
          let libs := (foreign.filterMap fun k => (moduleOf env k).map libraryOf).toList.eraseDups
          let tail := s!"; certificate checked, proof of {cert.nodes} nodes"
          let prove := if cert.lemmas.size == 1 then "proves" else "prove"
          if foreign.isEmpty then
            bySeed := bySeed + 1
            if selfSeed then
              out := out.push { check := "entailed", severity := "info", module := m, name := n, line := ← lineOf n,
                                detail := s!"a one-step consequence of other seed theorems: {names cert.lemmas} {prove} it{tail}" }
            else
              out := out.push { check := "entailed", severity := "warn", module := m, name := n, line := ← lineOf n,
                                detail := s!"entailed by the seed: {names cert.lemmas} {prove} it in one step (the theorem is a consequence of what the tree already had; a translation that adds no new claim){tail}" }
            pure "seed"
          else
            byLibrary := byLibrary + 1
            let own := libs.all (· == lib)
            let who := if selfSeed then "entailed by a library" else if own then s!"entailed by its own library ({lib}, another module)"
                       else s!"entailed by {", ".intercalate (libs.map toString)}"
            let why := if selfSeed then "a seed theorem a library proves in one step" else if own then "redundancy within the library"
                       else "tawatur of libraries: the same claim rests on another library's theorems too"
            out := out.push { check := "entailed", severity := "info", module := m, name := n, line := ← lineOf n,
                              detail := s!"{who}: {names cert.lemmas} {prove} it in one step ({why}){tail}" }
            pure "library"
    if timing then IO.eprintln s!"entailed: {n} {(← IO.monoMsNow) - t0} ms: {outcome}"
  if tried > 0 || skipped > 0 then
    out := out.push { check := "entailed", severity := "info", module := (c.mods.headD .anonymous), name := .anonymous,
                      detail := s!"{tried} theorems tried: {bySeed} entailed by the seed, {byLibrary} by a library, {byNothing} closed without a lemma, {unknown} not closed within {hb}k heartbeats; {skipped} skipped past {maxPerModule} per module (JINSHI_ENTAILED_MAX)" }
  return out

end Jinshi
