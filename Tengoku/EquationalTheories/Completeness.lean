-- Tengoku.EquationalTheories.Completeness: verified translations of equational_theories/Completeness.lean (1 theorem)
import Tengoku
import Tengoku.Data.FunLike.Basic
import Tengoku.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Data.List.NodupEquivFin
import Tengoku.Data.Set.Defs
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

lemma eq_app : ∀ α β (f g : α → β), f = g → ∀ x, f x = g x
:= fun _ _ _ _ a x ↦ congrFun a x

end EquationalTheories
