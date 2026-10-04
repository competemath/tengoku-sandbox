-- Tengoku.EquationalTheories.CentralGroupoids: verified translations of equational_theories/CentralGroupoids.lean (1 theorem)
import Tengoku
import Tengoku.EquationalTheories.Deps.Magma
import Lean
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.EquationalTheories.Deps.MemoFinOp
import Tengoku.Seed.Data.Finite.Prod
import Tengoku.Seed.Data.Fintype.Perm
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 4000

set_option warn.classDefReducibility false

@[inherit_doc] infix:65 " ◇ " => Magma.op

-- [Emissary prelude] equations regenerated from the corpus's `equation N := law` declarations
universe uEq

-- [Emissary prelude] equational_theories.MemoFinOp — verbatim
namespace MemoFinOp

open Lean Meta Elab Term

elab "memoFinOp" fn:term:arg :term <= expectedType? => do
  let fn ← elabTermAndSynthesize fn expectedType?
  Term.synthesizeSyntheticMVarsNoPostponing
  if (← Term.logUnassignedUsingErrorInfos (← getMVars fn)) then throwAbortTerm
  let fn ← zetaReduce fn

  -- Type checking
  let type ← inferType fn
  let type ← instantiateMVars type
  unless type.isForall do
    throwError "expected a function, got {type}"
  let t := type.bindingDomain!
  unless t.isAppOfArity ``Fin 1 do
    throwError "expected a function of Fin n for some n"
  let nE ← instantiateMVars t.appArg!
  let expectedType := .forallE `a t (.forallE `b t t .default) .default
  unless (← isDefEq type expectedType ) do
    throwError "expected type {expectedType}, got {type}"

  -- Tabulation
  let table ← evalNat (mkApp2 (mkConst ``buildMemo) nE fn)
  return mkApp2 (mkConst ``opOfTable) nE (.lit (.natVal table))

end MemoFinOp

-- proof-side construction of the witnessing magma
private def ofMatrix {n : Nat} [Inhabited (Fin n)]
  (table : Array (Array (Fin n))) (x y : Fin n) : Fin n :=
  (table[x.val]!)[y.val]!

/-- A magma isomorphic to A2, given as an optable. -/
def MagmaA2T : Magma (Fin 9) where
  op := memoFinOp (ofMatrix #[ #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[3, 3, 3, 5, 4, 4, 4, 5, 5], #[6, 6, 6, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8], #[0, 0, 0, 1, 1, 1, 2, 2, 2], #[6, 6, 6, 5, 4, 4, 4, 5, 5], #[3, 3, 3, 8, 7, 7, 7, 8, 8]])

theorem MagmaA2T.Facts : ∃ (G : Type) (_ : Magma G),
    Equation168 G ∧ Equation1480 G ∧ Equation1483 G ∧ Equation1484 G ∧ Equation1485 G ∧
    Equation1486 G ∧ Equation1487 G ∧ Equation2052 G ∧ Equation2089 G ∧ Equation2126 G ∧
    Equation2162 G ∧ Equation2163 G ∧ Equation2164 G ∧
    ¬ Equation3461 G ∧ ¬ Equation3462 G ∧ ¬ Equation3463 G ∧ ¬ Equation3521 G ∧ ¬ Equation3522 G ∧
    ¬ Equation3523 G ∧ ¬ Equation3532 G ∧ ¬ Equation3533 G ∧ ¬ Equation3534 G ∧ ¬ Equation3535 G ∧
    ¬ Equation3864 G ∧ ¬ Equation3880 G ∧ ¬ Equation3883 G ∧ ¬ Equation3915 G ∧ ¬ Equation3921 G ∧
    ¬ Equation3952 G ∧ ¬ Equation3958 G ∧ ¬ Equation3989 G ∧ ¬ Equation3997 G ∧ ¬ Equation4001 G ∧
    ¬ Equation4268 G ∧ ¬ Equation4282 G ∧ ¬ Equation4314 G ∧ ¬ Equation4315 G ∧ ¬ Equation4339 G ∧
    ¬ Equation4357 G ∧ ¬ Equation4587 G ∧ ¬ Equation4606 G ∧ ¬ Equation4615 G ∧ ¬ Equation4645 G ∧
    ¬ Equation4666 G ∧ ¬ Equation4689 G
:=
  ⟨Fin 9, MagmaA2T, by decide⟩

end EquationalTheories
