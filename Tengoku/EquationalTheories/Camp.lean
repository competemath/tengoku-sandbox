import Tengoku

namespace Camp

/-- doc -/
prefix:80 "-" => Nat.succ -- the successor

elab "resolve" : tactic => pure ()

theorem camp_one : 1 = 1 := rfl

end Camp

def camp_tail := -1
