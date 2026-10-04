-- Tengoku.EquationalTheories.Subgraph: verified translations of equational_theories/Subgraph.lean (35 theorems)
import Tengoku.Seed.Tactic
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
import Tengoku.Seed.Logic.Basic
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

-- left unwrapped: this module opens an outside namespace block
open EquationalTheories

/- This is a subproject of the main project to completely describe a small subgraph of the entire
implication graph. The list of equations under consideration can be found at
https://teorth.github.io/equational_theories/blueprint/subgraph-eq.html

Implications here should be placed inside the "Subgraph" namespace.

-/

namespace Subgraph

theorem Equation2_implies_Equation7 (G: Type*) [Magma G] (h: Equation2 G) : Equation7 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation8 (G: Type*) [Magma G] (h: Equation2 G) : Equation8 G
:=
  fun _ ↦ h ..

theorem Equation2_implies_Equation23 (G: Type*) [Magma G] (h: Equation2 G) : Equation23 G
:=
  fun _ ↦ h ..

theorem Equation2_implies_Equation38 (G: Type*) [Magma G] (h: Equation2 G) : Equation38 G
:=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation39 (G: Type*) [Magma G] (h: Equation2 G) : Equation39 G
:=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation40 (G: Type*) [Magma G] (h: Equation2 G) : Equation40 G
:=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation41 (G: Type*) [Magma G] (h: Equation2 G) : Equation41 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation42 (G: Type*) [Magma G] (h: Equation2 G) : Equation42 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation43 (G: Type*) [Magma G] (h: Equation2 G) : Equation43 G
:=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation46 (G: Type*) [Magma G] (h: Equation2 G) : Equation46 G
:=
  fun _ _ _ _ ↦ h ..

theorem Equation2_implies_Equation168 (G: Type*) [Magma G] (h: Equation2 G) : Equation168 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation387 (G: Type*) [Magma G] (h: Equation2 G) : Equation387 G
:=
  fun _ _ ↦ h ..

theorem Equation2_implies_Equation1689 (G: Type*) [Magma G] (h: Equation2 G) : Equation1689 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation4512 (G: Type*) [Magma G] (h: Equation2 G) : Equation4512 G
:=
  fun _ _ _ ↦ h ..

theorem Equation2_implies_Equation4513 (G: Type*) [Magma G] (h: Equation2 G) : Equation4513 G
:=
  fun _ _ _ _ ↦ h ..

theorem Equation2_implies_Equation4522 (G: Type*) [Magma G] (h: Equation2 G) : Equation4522 G
:=
  fun _ _ _ _ _ ↦ h ..

theorem Equation2_implies_Equation4582 (G: Type*) [Magma G] (h: Equation2 G) : Equation4582 G
:=
  fun _ _ _ _ _ _ ↦ h ..

theorem Equation3_implies_Equation8 (G: Type*) [Magma G] (h: Equation3 G) : Equation8 G
:=
  fun x ↦ by repeat rw [← h]

theorem Equation3_implies_Equation23 (G: Type*) [Magma G] (h: Equation3 G) : Equation23 G
:=
  fun x ↦ by repeat rw [← h]

theorem Equation4_implies_Equation3 (G: Type*) [Magma G] (h: Equation4 G) : Equation3 G
:=
  fun _ ↦ by rw [← h]

theorem Equation4_implies_Equation8 (G: Type*) [Magma G] (h: Equation4 G) : Equation8 G
:=
  fun _ ↦ h ..

theorem Equation4_implies_Equation23 (G: Type*) [Magma G] (h: Equation4 G) : Equation23 G
:=
  Equation3_implies_Equation23 G fun _ ↦ h ..

theorem Equation4_implies_Equation42 (G: Type*) [Magma G] (h: Equation4 G) : Equation42 G
:=
  fun _ _ _ ↦ by repeat rw [← h]

theorem Equation4_implies_Equation4522 (G: Type*) [Magma G] (h: Equation4 G) : Equation4522 G
:=
  fun _ _ _ _ _ ↦ by repeat rw [← h]

theorem Equation5_implies_Equation3 (G: Type*) [Magma G] (h: Equation5 G) : Equation3 G
:=
  fun _ ↦ h ..

theorem Equation5_implies_Equation8 (G: Type*) [Magma G] (h: Equation5 G) : Equation8 G
:=
  fun _  ↦ by repeat rw [← h]

theorem Equation5_implies_Equation23 (G: Type*) [Magma G] (h: Equation5 G) : Equation23 G
:=
  fun _  ↦ by repeat rw [← h]

theorem Equation5_implies_Equation39 (G: Type*) [Magma G] (h: Equation5 G) : Equation39 G
:=
  fun _ _ ↦ by repeat rw [← h]

theorem Equation5_implies_Equation4512 (G: Type*) [Magma G] (h: Equation5 G) : Equation4512 G
:=
  fun _ _ _  ↦ by repeat rw [← h]

theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation6_implies_Equation3 (G: Type*) [Magma G] (h: Equation6 G) : Equation3 G
:=
  fun _ ↦ h ..

theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G
:=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation7_implies_Equation3 (G: Type*) [Magma G] (h: Equation7 G) : Equation3 G
:=
  fun _ ↦ h ..

theorem Equation7_implies_Equation41 (G: Type*) [Magma G] (h: Equation7 G) : Equation41 G
:=
  fun _ _ _ ↦ h ..

theorem Equation14_implies_Equation29 (G: Type*) [Magma G] (h: Equation14 G) : Equation29 G
:=
  fun x y ↦ (h x (y ◇ x)).trans (congrArg ((y ◇ x) ◇ ·) (h y x).symm)

end Subgraph
