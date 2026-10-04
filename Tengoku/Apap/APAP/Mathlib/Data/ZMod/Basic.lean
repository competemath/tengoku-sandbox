module

public import Tengoku

public section

namespace ZMod
variable {M : Type*} {q : ℕ}

-- FIXME: The LHS has type `Fin (q + 1)`. See
@[simp↓] lemma val_mk (n : ℕ) (hn) : val (n := q + 1) (⟨n, hn⟩ : ZMod (q + 1)) = n := rfl

-- FIXME: The LHS has type `Fin (q + 1)`. See
@[simp] lemma mk_eq_natCast (n : ℕ) (hn) : ⟨n, hn⟩ = (n : ZMod (q + 1)) :=
  (Fin.natCast_eq_mk _).symm

end ZMod
