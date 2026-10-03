module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.AddOrd

/-!
# Negation reverses the order

That `x <= y` gives `-y <= -x`, with the strict form and the consequences for
sign. The bridge every later case analysis uses to reduce a negative case to a
positive one.

## Position in the development

Above `Dedekind.AddOrd`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

theorem neg_le_neg {x y : Cut} (hxy : x <= y) : -y <= -x := by
  apply le_of_add_le_add_right (z := y)
  have h0 : 0 <= -x + y := by
    have h : x + (-x) <= y + (-x) := add_le_add_right hxy (-x)
    rw [add_neg x] at h
    rw [add_comm y (-x)] at h
    exact h
  rw [neg_add y]
  exact h0

theorem neg_nonneg_of_nonpos {x : Cut} (hx : x <= 0) : 0 <= -x := by
  have h : -(0 : Cut) <= -x := neg_le_neg hx
  rw [neg_zero] at h
  exact h

theorem nonpos_of_not_nonneg {x : Cut} (h : Not (0 <= x)) : x <= 0 := by
  cases le_total x 0 with
  | inl hx0 => exact hx0
  | inr h0x => exact False.elim (h h0x)

theorem eq_zero_of_nonneg_of_nonpos {x : Cut} (h0x : 0 <= x) (hx0 : x <= 0) :
    x = 0 :=
  le_antisymm hx0 h0x

theorem neg_nonneg_of_not_nonneg {x : Cut} (h : Not (0 <= x)) : 0 <= -x :=
  neg_nonneg_of_nonpos (nonpos_of_not_nonneg h)

theorem nonneg_of_neg_nonpos {x : Cut} (h : -x <= 0) : 0 <= x := by
  have h' : -(0 : Cut) <= -(-x) := neg_le_neg h
  rw [neg_zero, neg_neg x] at h'
  exact h'

theorem nonpos_of_neg_nonneg {x : Cut} (h : 0 <= -x) : x <= 0 := by
  have h' : -(-x) <= -(0 : Cut) := neg_le_neg h
  rw [neg_zero, neg_neg x] at h'
  exact h'

theorem eq_zero_of_nonneg_of_neg_nonneg {x : Cut} (h0x : 0 <= x)
    (h0nx : 0 <= -x) :
    x = 0 :=
  eq_zero_of_nonneg_of_nonpos h0x (nonpos_of_neg_nonneg h0nx)

theorem neg_pos_of_neg {x : Cut} (hx : x < 0) : 0 < -x := by
  apply lt_of_le_of_not_le
  · exact neg_nonneg_of_nonpos hx.left
  · intro hnx0
    exact hx.right (nonneg_of_neg_nonpos hnx0)

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
