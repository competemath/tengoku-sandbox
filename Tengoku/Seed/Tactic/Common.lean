/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/

-- First import Aesop, Qq, and Plausible
module  -- shake: keep-all, shake: keep-downstream

public import Tengoku.Seed.Tactic.Aesop
public import Tengoku.Seed.Meta.Qq
public import Tengoku.Seed.Testing.Random

-- Import common Batteries tactics and commands
public import Tengoku.Seed.Std.Tactic.Basic
public import Tengoku.Seed.Std.Tactic.Case
public import Tengoku.Seed.Std.Tactic.HelpCmd
public import Tengoku.Seed.Std.Tactic.Alias
public import Tengoku.Seed.Std.Tactic.GeneralizeProofs

-- Import Batteries code actions
public import Tengoku.Seed.Std.CodeAction

-- Import syntax for leansearch
public import Tengoku.Seed.Search.LeanSearchClient

-- Import Mathlib-specific linters.
public import Tengoku.Seed.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
public import Tengoku.Seed.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib/Order/Monotone/Basic.lean`
-- import Mathlib.Tactic.ApplyFun
public import Tengoku.Seed.Tactic.ApplyAt
public import Tengoku.Seed.Tactic.ApplyWith
public import Tengoku.Seed.Tactic.Basic
public import Tengoku.Seed.Tactic.ByCases
public import Tengoku.Seed.Tactic.ByContra
public import Tengoku.Seed.Tactic.CasesM
public import Tengoku.Seed.Tactic.Check
public import Tengoku.Seed.Tactic.Choose
public import Tengoku.Seed.Tactic.ClearExclamation
public import Tengoku.Seed.Tactic.ClearExcept
public import Tengoku.Seed.Tactic.Clear_
public import Tengoku.Seed.Tactic.ClickSuggestions
public import Tengoku.Seed.Tactic.Coe
public import Tengoku.Seed.Tactic.CongrExclamation
public import Tengoku.Seed.Tactic.CongrM
public import Tengoku.Seed.Tactic.Constructor
public import Tengoku.Seed.Tactic.Contrapose
public import Tengoku.Seed.Tactic.Conv
public import Tengoku.Seed.Tactic.Convert
public import Tengoku.Seed.Tactic.DefEqAbuse
public import Tengoku.Seed.Tactic.DefEqTransformations
public import Tengoku.Seed.Tactic.DeprecateTo
public import Tengoku.Seed.Tactic.DepRewrite
public import Tengoku.Seed.Tactic.DSimpPercent
public import Tengoku.Seed.Tactic.ErwQuestion
public import Tengoku.Seed.Tactic.Eqns
public import Tengoku.Seed.Tactic.ExistsI
public import Tengoku.Seed.Tactic.ExtractGoal
public import Tengoku.Seed.Tactic.FailIfNoProgress
public import Tengoku.Seed.Tactic.Find
public import Tengoku.Seed.Tactic.FunProp
public import Tengoku.Seed.Tactic.GCongr
public import Tengoku.Seed.Tactic.GRewrite
public import Tengoku.Seed.Tactic.GrindAttrs
public import Tengoku.Seed.Tactic.GuardGoalNums
public import Tengoku.Seed.Tactic.GuardHypNums
public import Tengoku.Seed.Tactic.HigherOrder
public import Tengoku.Seed.Tactic.Hint
public import Tengoku.Seed.Tactic.InferParam
public import Tengoku.Seed.Tactic.Inhabit
public import Tengoku.Seed.Tactic.IrreducibleDef
public import Tengoku.Seed.Tactic.Lift
public import Tengoku.Seed.Tactic.Linter
public import Tengoku.Seed.Tactic.MkIffOfInductiveProp
-- NormNum imports `Algebra.Order.Invertible`, `Data.Int.Basic`, `Data.Nat.Cast.Commute`
-- import Mathlib.Tactic.NormNum.Basic
public import Tengoku.Seed.Tactic.NthRewrite
public import Tengoku.Seed.Tactic.Observe
public import Tengoku.Seed.Tactic.OfNat
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
public import Tengoku.Seed.Tactic.Push
public import Tengoku.Seed.Tactic.RSuffices
public import Tengoku.Seed.Tactic.Recover
public import Tengoku.Seed.Tactic.Relation.Rfl
public import Tengoku.Seed.Tactic.Rename
public import Tengoku.Seed.Tactic.RenameBVar
public import Tengoku.Seed.Tactic.Says
public import Tengoku.Seed.Tactic.ScopedNS
public import Tengoku.Seed.Tactic.Set
public import Tengoku.Seed.Tactic.SimpIntro
public import Tengoku.Seed.Tactic.SimpRw
public import Tengoku.Seed.Tactic.Simproc.ExistsAndEq
public import Tengoku.Seed.Tactic.Simps
public import Tengoku.Seed.Tactic.SplitIfs
public import Tengoku.Seed.Tactic.Spread
public import Tengoku.Seed.Tactic.Subsingleton
public import Tengoku.Seed.Tactic.Substs
public import Tengoku.Seed.Tactic.SuccessIfFailWithMsg
public import Tengoku.Seed.Tactic.SudoSetOption
public import Tengoku.Seed.Tactic.SwapVar
public import Tengoku.Seed.Tactic.Tauto
public import Tengoku.Seed.Tactic.ToFun
public import Tengoku.Seed.Tactic.TermCongr
-- TFAE imports `Mathlib/Data/List/TFAE.lean` and thence `Mathlib/Data/List/Basic.lean`.
-- import Mathlib.Tactic.TFAE
public import Tengoku.Seed.Tactic.ToExpr
public import Tengoku.Seed.Tactic.ToLevel
public import Tengoku.Seed.Tactic.Trace
public import Tengoku.Seed.Tactic.UnsetOption
public import Tengoku.Seed.Tactic.Use
public import Tengoku.Seed.Tactic.Variable
public import Tengoku.Seed.Tactic.Widget.Calc
public import Tengoku.Seed.Tactic.Widget.CongrM
public import Tengoku.Seed.Tactic.Widget.Conv
public import Tengoku.Seed.Tactic.Widget.LibraryRewrite
public import Tengoku.Seed.Tactic.WLOG
public import Tengoku.Seed.Util.CountHeartbeats
public import Tengoku.Seed.Util.PrintSorries
public import Tengoku.Seed.Util.TransImports
public import Tengoku.Seed.Util.WhatsNew
public import Lean.Elab.Tactic.Try
public meta import Lean.Meta.Tactic.Try.Collect

/-!
# Common tactics, linters, and utilities

This file imports all tactics which do not have significant theory imports,
and hence can be imported very low in the theory import hierarchy,
thereby making tactics widely available without needing specific imports.

We include some commented out imports here, with an explanation of their theory requirements,
to save some time for anyone wondering why they are not here.

We also import theory-free linters, commands, and utilities which are useful to have low in the
import hierarchy.
-/

public meta section

/-!
### Register tactics with `hint`. Tactics with larger priority run first.
-/

section Hint

register_hint 1000 trivial
register_hint 1000 split
register_hint 1000 intro
register_hint 1000 decide
register_hint 800 simp_all?
register_hint 600 exact?
register_hint 500 tauto
register_hint 200 grind
register_hint 200 omega
register_hint 200 fun_prop
register_hint 80 aesop

end Hint

/-!
### Register tactics with `try?`. Tactics with larger priority run first.
-/

section Try

register_try?_tactic (priority := 500) tauto
register_try?_tactic (priority := 80) aesop
register_try?_tactic (priority := 200) fun_prop

end Try
