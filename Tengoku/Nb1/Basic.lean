import Tengoku

namespace Nb1

theorem good : 1 + 1 = 2 := rfl

end Nb1
scoped notation "ℓ" => 1
local infixl:65 " +' " => Nat.add
scoped[Nb1] prefix:80 "~" => Nat.succ
