-- Tengoku.EquationalTheories.ManuallyProved.Equation1323: verified translations of equational_theories/ManuallyProved/Equation1323.lean (10 theorems)
import Tengoku.Seed.Algebra.Ring.NonZeroDivisors
import Tengoku.Seed.Data.Finset.Union
import Tengoku.Seed.Data.Set.Countable
import Tengoku.Seed.GroupTheory.FreeGroup.CyclicallyReduced
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Lean
import Tengoku.Seed.Order.Preorder.Chain
import Tengoku.Seed.Logic.Equiv.Finset
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace Eq1323

noncomputable section

section Ingredients

open symmDiff

variable {α : Type}

def FreeAbGrpExp2 (α : Type) : Type := Finset α

def FreeAbGrpExp2.mk : Finset α → FreeAbGrpExp2 α := id

def FreeAbGrpExp2.of (x : α) : FreeAbGrpExp2 α := FreeAbGrpExp2.mk {x}

def FreeAbGrpExp2.coords : FreeAbGrpExp2 α → Finset α := id

@[simp] theorem FreeAbGrpExp2.mk_coords (a : FreeAbGrpExp2 α) : FreeAbGrpExp2.mk a.coords = a
:= rfl

@[simp] theorem FreeAbGrpExp2.coords_mk (a : Finset α) : (FreeAbGrpExp2.mk a).coords = a
:= rfl

instance [DecidableEq α] : DecidableEq (FreeAbGrpExp2 α) := inferInstanceAs (DecidableEq (Finset α))

instance [Countable α] : Countable (FreeAbGrpExp2 α) := inferInstanceAs (Countable (Finset α))

instance [Infinite α] : Infinite (FreeAbGrpExp2 α) := inferInstanceAs (Infinite (Finset α))

instance [DecidableEq α] : Add (FreeAbGrpExp2 α) where
  add a b := FreeAbGrpExp2.mk (a.coords ∆ b.coords)

instance : Zero (FreeAbGrpExp2 α) where zero := ⟨∅, by simp⟩

instance : Neg (FreeAbGrpExp2 α) where neg := id

theorem FreeAbGrpExp2.add_def [DecidableEq α] (a b : FreeAbGrpExp2 α) :
  a + b = FreeAbGrpExp2.mk (a.coords ∆ b.coords)
:= rfl

theorem FreeAbGrpExp2.zero_def : (Zero.zero : FreeAbGrpExp2 α) = ⟨∅, by simp⟩
:= rfl

theorem FreeAbGrpExp2.neg_def (a : FreeAbGrpExp2 α) : -a = a
:= rfl

@[simp] theorem FreeAbGrpExp2.coords_0 : (0 : FreeAbGrpExp2 α).coords = ∅
:= rfl

@[simp] theorem FreeAbGrpExp2.mk_empty : (FreeAbGrpExp2.mk ∅ : FreeAbGrpExp2 α) = 0
:= rfl

theorem FreeAbGrpExp2.of_nonzero (x : α) : FreeAbGrpExp2.of x ≠ 0
:= Finset.singleton_ne_empty _

theorem FreeAbGrpExp2.of_injective : Function.Injective (FreeAbGrpExp2.of : α → FreeAbGrpExp2 α)
:=
  Finset.singleton_injective

@[simp] theorem FreeAbGrpExp2.of_injective' {x y : α} : x ≠ y → FreeAbGrpExp2.of x ≠ FreeAbGrpExp2.of y
:=
  mt (of_injective ·)

end Ingredients
end
end Eq1323

end EquationalTheories
