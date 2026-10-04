-- Tengoku.EquationalTheories.Generated.Constant: verified translations of equational_theories/Generated/Constant.lean (1 theorem)
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
import Tengoku.Seed.Tactic
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

namespace Constant

theorem Equation4032_implies_Equation46 (G: Type*) [Magma G] (h: Equation4032 G) : Equation46 G
:=
  fun a b _ _ => by rw [h a b a, ← h]

end Constant

end EquationalTheories
