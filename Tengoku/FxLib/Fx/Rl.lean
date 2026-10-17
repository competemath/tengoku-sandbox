import Tengoku

namespace Real

def tilde (x : Nat) : Nat := x

scoped prefix:80 "~" => tilde

end Real
open scoped Real

lemma useTilde : ~1 = 1 := rfl
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
