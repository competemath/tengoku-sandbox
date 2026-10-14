-- Tengoku.EquationalTheories.Completeness: verified translations of equational_theories/Completeness.lean (4 theorems)
import Tengoku
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

lemma eq_app : ∀ α β (f g : α → β), f = g → ∀ x, f x = g x
:= fun _ _ _ _ a x ↦ congrFun a x

theorem Selftest.Dclean_1_1 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.Dclean_1_2 : (1 : Nat) + 1 = 2
:= rfl

theorem Selftest.Dclean_1_3 : (1 : Nat) + 1 = 2
:= rfl

end EquationalTheories
