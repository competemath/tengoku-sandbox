import Tengoku

namespace Camp

/-- doc -/
scoped prefix:80 "-" => Nat.succ -- the successor

scoped elab "resolve" : tactic => pure ()

theorem camp_one : 1 = 1 := rfl

end Camp

open scoped Camp

def camp_tail := -1
notation "ℓ" => 1
