/-
Every keyword that can start a command in the tree's Lean: the leading tokens of the `command` parser category with the module given (default `Tengoku`, the seed's
root) loaded. scripts/ci/allowlist.py reads a word at column 0 as a command only if it is on this list (schemas/command-keywords.json); the nightly build compares it
(scripts/ci/cmdkw_check.py) and says so when the seed has changed the set.

  lake env lean --run tools/CommandKeywords.lean [Module]        one keyword per line, sorted
-/
import Lean

open Lean Parser

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution  -- `lean --run` interprets this file: the initializers of the imported modules must be allowed to run
  initSearchPath (← findSysroot)
  let mod := (args.head?.getD "Tengoku").toName
  let env ← importModules #[{ module := mod }] {} (trustLevel := 0) (loadExts := true)
  let some cat := (parserExtension.getState env).categories.find? `command | do
    IO.eprintln "the environment has no `command` category"
    return 1
  let words : Array String := cat.tables.leadingTable.toList.toArray.map fun p => p.1.toString
  for w in words.qsort (· < ·) do
    IO.println w
  return 0
