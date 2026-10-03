module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.AddOrd

/-!
# The additive group

Associativity, commutativity, the zero and the inverse assembled: the cuts
form an ordered additive group. Ten theorems collecting what the previous four
files established.

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

theorem eq_of_add_eq_add_left {x y z : Cut} (h : z + x = z + y) :
    x = y := by
  apply le_antisymm
  · exact le_of_add_le_add_left (by
      rw [h]
      exact le_refl (z + y))
  · exact le_of_add_le_add_left (by
      rw [h]
      exact le_refl (z + y))

theorem add_neg_cancel_right (x y : Cut) : (x + y) + (-y) = x := by
  rw [add_assoc x y (-y)]
  rw [add_neg y]
  rw [add_zero x]

theorem add_neg_eq_of_eq_add {a b d : Cut} (h : b = a + d) :
    a = b + (-d) := by
  rw [h]
  rw [add_neg_cancel_right a d]

theorem eq_add_of_eq_neg_add {a b d : Cut} (h : d = -a + b) :
    b = a + d := by
  rw [h]
  rw [← add_assoc a (-a) b]
  rw [add_neg a]
  rw [zero_add b]

theorem add_add_neg_swap (x y : Cut) : (x + y) + (-x) = y := by
  rw [add_comm x y]
  exact add_neg_cancel_right y x

theorem neg_add_distrib (x y : Cut) : -(x + y) = -x + -y := by
  apply eq_of_add_eq_add_left (z := x + y)
  rw [add_neg (x + y)]
  have hright : (x + y) + (-x + -y) = 0 := by
    rw [← add_assoc (x + y) (-x) (-y)]
    rw [add_add_neg_swap x y]
    rw [add_neg y]
  exact hright.symm

theorem neg_add_add_left (x y : Cut) : -(x + y) + x = -y := by
  rw [neg_add_distrib x y]
  rw [add_comm (-x) (-y)]
  rw [add_assoc (-y) (-x) x]
  rw [neg_add x]
  rw [add_zero (-y)]

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
