module

public import Tengoku.Apap.APAP.Mathlib.Data.ZMod.Basic
public import Tengoku

public section

namespace AddChar
variable {R M : Type*} [Semiring R] {q : ℕ} [AddCommMonoid M] [Module (ZMod q) M] {γ : AddChar M R}
  {r : ZMod q} {x : M}

variable (γ r x) in
lemma map_zmod_smul [NeZero q] : γ (r • x) = γ x ^ r.val := by
  obtain _ | q := q
  · simp_all
  obtain ⟨n, hn⟩ := r
  simp [Nat.cast_smul_eq_nsmul, map_nsmul_eq_pow]

end AddChar
