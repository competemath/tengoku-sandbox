import Tengoku

namespace Real

def tilde (x : Nat) : Nat := x

prefix:80 "~" => tilde

end Real

lemma useTilde : ~1 = 1 := rfl
