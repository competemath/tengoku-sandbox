/-
Jinshi: the environment examinations (docs/jinshi.md). For the modules named, this walks the compiled environment and prints one JSON
line per finding:

  {"check": <name>, "severity": "fail"|"warn"|"info", "module": M, "name": N, "line": L, "detail": …}

and a last line {"check": "summary", …} with the counts. No Lean is elaborated here: everything is read from the environment the
modules were compiled into, as the merge queue's axiom check and the leak scan do.

  lake build tengoku-jinshi
  lake env .lake/build/bin/tengoku-jinshi --module Tengoku.Compfiles [--module …] [--import M …] [--seed Tengoku.Seed] [--check tcb,…]
  lake env .lake/build/bin/tengoku-jinshi --list                        # the examinations this build knows
  lake env .lake/build/bin/tengoku-jinshi --module M --check mutants --mutants-out DIR   # the mutant modules for scripts/jinshi/mutants.py

`--seed` names the module prefix of the seed (what `shadow` compares a library's names against; the seed itself is exempt from the
examinations that read a library's theorems). `--import` loads a module without examining it (the fixtures). One examination per
file under Jinshi/, registered in `examinations` below.
-/
import Jinshi.ArithUniverse
import Jinshi.Base
import Jinshi.Decide
import Jinshi.Duplicate
import Jinshi.Entailed
import Jinshi.Forensics
import Jinshi.Importance
import Jinshi.Instdrift
import Jinshi.Lineage
import Jinshi.Mutants
import Jinshi.Nearname
import Jinshi.Necessity
import Jinshi.Nested
import Jinshi.Roundtrip
import Jinshi.Unusedhyp
open Lean Meta Jinshi

/-- every examination this build knows: its name (the `check` field, the `--check` key) and its runner -/
def examinations : List (String × (Ctx → MetaM (Array Finding))) :=
  [("tcb", fun c => tcb c),
   ("shadow", fun c => shadow c),
   ("arith", fun c => arith c),
   ("arithUniverse", arithUniverse),
   ("dossier", dossier),
   ("content", content),
   ("decide", decide),
   ("duplicate", duplicate),
   ("entailed", entailed),
   ("forensics", forensics),
   ("importance", importance),
   ("instdrift", instdrift),
   ("lineage", lineage),
   ("mutants", mutants),
   ("nearname", nearname),
   ("necessity", necessity),
   ("nested", nested),
   ("roundtrip", roundtrip),
   ("unusedhyp", unusedhyp)]

unsafe def main (argv : List String) : IO UInt32 := do
  enableInitializersExecution
  if argv.contains "--list" then
    for (n, _) in examinations do IO.println n
    return 0
  let opt (k : String) : List String := (argv.zip (argv.drop 1)).filterMap fun (a, b) => if a == k then some b else none
  let mods := (opt "--module").map String.toName
  let imports := (opt "--import").map String.toName ++ mods
  let seed := ((opt "--seed").headD "Tengoku.Seed").toName
  let checks := ((opt "--check").map fun s => (s.splitOn ",").map fun t => t.trimAscii.toString).flatten
  if imports.isEmpty then
    IO.eprintln "usage: tengoku-jinshi --module <M> [--module <M>…] [--import <M>…] [--seed <prefix>] [--check a,b,…] | --list"
    return 2
  for ch in checks do
    unless examinations.any (·.1 == ch) do
      IO.eprintln s!"unknown examination `{ch}` (--list prints them)"
      return 2
  if let some d := (opt "--mutants-out").head? then mutantsOutRef.set (some d)  -- where `mutants` writes its modules
  initSearchPath (← findSysroot)
  let env ← importModules (imports.eraseDups.toArray.map fun m => { module := m }) {} (trustLevel := 0) (loadExts := true)
  let idxs := ((List.range env.header.moduleNames.size).filter fun i => mods.any (·.isPrefixOf env.header.moduleNames[i]!)).toArray
  let c : Ctx := { idxs, mods, seed, checks }
  let ctx : Core.Context := { fileName := "<tengoku-jinshi>", fileMap := default, maxHeartbeats := 0 }
  let mut all : Array Finding := #[]
  for (name, run) in examinations do
    if c.on name then
      -- an examination that throws (a heartbeat or recursion cap, a bug) loses only its own findings, as one warn
      let lost (why : String) : Finding :=
        { check := name, severity := "warn", module := c.mods.headD .anonymous, name := .anonymous,
          detail := s!"the examination threw and its findings for these modules are lost: {why}" }
      let guarded : MetaM (Array Finding) :=
        tryCatchRuntimeEx (run c) fun e => do return #[lost (← e.toMessageData.toString)]
      let r ← try
          let (r, _) ← (guarded.run' {} {}).toIO ctx { env }
          pure r
        catch e => pure #[lost (toString e)]
      all := all ++ r
  for f in all do IO.println f.json
  let count (s : String) := (all.filter (·.severity == s)).size
  IO.println (Json.mkObj [("check", "summary"), ("modules", (idxs.size : Json)), ("findings", (all.size : Json)),
                          ("fail", (count "fail" : Json)), ("warn", (count "warn" : Json)), ("info", (count "info" : Json))]).compress
  return 0
