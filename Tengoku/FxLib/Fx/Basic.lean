import Tengoku

namespace Fx
namespace Mod

def complement (x : Nat) : Nat := x

/-- the complement -/
prefix:80 "-" => complement

lemma l : -1 = 1 := rfl

end Mod

lemma outside : -1 = 1 := rfl

end Fx
