-- Tengoku.EquationalTheories.Definability.Basic: verified translations of equational_theories/Definability/Basic.lean (2 theorems)
import Tengoku.Seed.ModelTheory.Definability
import Tengoku.Seed.Data.Rel
import Tengoku.Seed.Data.Set.Card
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

section definitions

open FirstOrder

variable {G β : Type*}

/-- The First Order language of expressions in Magmas: just a single binary operation
(represented here as the constant Unit.unit), and no relations.
-/

def MagmaLanguage : Language where
  Functions n := if n = 2 then Unit else Empty
  Relations _ := Empty

instance instMagmaLanguageUniq : Unique (MagmaLanguage.Functions 2) := by
  simpa [MagmaLanguage] using PUnit.instUnique

/-- Helper method to turn a 'normal' function that combines pairs into the correctly typed generic
  operation on MagmaLanguage functions. -/
def MagmaLanguage.onFunctions {motive : ℕ → Sort*} (f : motive 2) :
    ∀ {n}, MagmaLanguage.Functions n → motive n :=
  fun {n} f0 ↦
    if hn : n = 2 then
      hn ▸ f
    else
      isEmptyElim (show Empty by simpa [MagmaLanguage, hn] using f0)

/-- Like `MagmaLanguage.onFunctions` but for when the language has constants added. -/
def MagmaLanguage.onFunctions' {motive : ℕ → Sort*} {S : Type} (f : motive 2) (g : S → motive 0) :
    ∀ {n}, (MagmaLanguage[[S]]).Functions n → motive n :=
  fun {n} f0 ↦
    if hn : n = 2 then
      hn ▸ f
    else if hn₂ : n = 0 then
      (hn₂ ▸ f0).elim (isEmptyElim ∘ (by simpa [MagmaLanguage] using ·)) (hn₂ ▸ g)
    else
      isEmptyElim (show _ by
        simp [MagmaLanguage, hn, Language.withConstants, Language.sum] at f0
        exact f0.elim id fun h ↦ (Equiv.equivEmpty _) ((Nat.succ_pred_eq_of_ne_zero hn₂) ▸ h)
      )

namespace Magma

/-- The magma operation, as (Fin 2 → G) → G. -/
def FinArityOp (M : Magma G) : (Fin 2 → G) → G :=
  fun v ↦ M.op (v 0) (v 1)

/-- The graph of a magma operation, as a set of Fin 2 ⊕ Unit → G (which is equivalent to G × G × G). -/
def Graph (M : Magma G) : Set (Option (Fin 2) → G) :=
  M.FinArityOp.tupleGraph

/-- Magma.FOStructure gives the MagmaLanguage structure that corresponds to the Magma. -/
@[implicit_reducible]
def FOStructure (M : Magma G) : MagmaLanguage.Structure G where
  funMap :=
    @MagmaLanguage.onFunctions _ M.FinArityOp
  RelMap a :=
    isEmptyElim (show Empty from a)

theorem FOStructure_funMap {M : Magma G} (f : MagmaLanguage.Functions 2) :
    M.FOStructure.funMap f = M.FinArityOp
:= by
  rfl

theorem FOStructure_funMap' {M : Magma G} (f : MagmaLanguage[[(∅:Set _)]].Functions 2) :
    (@FirstOrder.Language.withConstantsStructure MagmaLanguage G M.FOStructure (∅:Set _)
      (FirstOrder.Language.paramsStructure G ∅)).funMap
    f = M.FinArityOp
:= by
  rcases f with f|f
  · exact rfl
  · exact isEmptyElim f

end Magma
end definitions

end EquationalTheories
