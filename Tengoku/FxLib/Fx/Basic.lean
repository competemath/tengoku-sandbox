import Tengoku

namespace Fx
namespace Mod

def complement (x : Nat) : Nat := x

/-- the complement -/
scoped prefix:80 "-" => complement

lemma l : -1 = 1 := rfl

end Mod
open scoped Fx.Mod

lemma outside : -1 = 1 := rfl

end Fx
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
