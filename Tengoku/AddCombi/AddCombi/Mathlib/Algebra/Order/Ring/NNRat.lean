module

public import Tengoku

public section

namespace NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat
