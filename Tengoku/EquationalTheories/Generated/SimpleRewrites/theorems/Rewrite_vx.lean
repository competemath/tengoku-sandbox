-- Tengoku.EquationalTheories.Generated.SimpleRewrites.theorems.Rewrite_vx: verified translations of equational_theories/Generated/SimpleRewrites/theorems/Rewrite_vx.lean (3 theorems)
import Tengoku.Seed.Tactic
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
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace SimpleRewrites

theorem Equation3455_implies_Equation3450 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3450 G
:= λ x y z w u => h x y z w u x

theorem Equation3658_implies_Equation3653 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3653 G
:= λ x y z w u => h x y z w u x

theorem Equation4064_implies_Equation4059 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4059 G
:= λ x y z w u => h x y z w u x

end SimpleRewrites

end EquationalTheories
