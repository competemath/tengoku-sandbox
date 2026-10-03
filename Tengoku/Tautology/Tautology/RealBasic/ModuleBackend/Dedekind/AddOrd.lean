module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Order
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Add
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Neg
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.AddInv

/-!
# Addition against the order

That addition preserves inclusion, and the cancellation that follows.
Compatibility of the order with addition, in the form the ordered field axioms
demand.

## Position in the development

Above `Dedekind.AddInv`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

theorem add_le_add_right {x y : Cut} (hxy : x <= y) (z : Cut) :
    x + z <= y + z := by
  intro q hq
  cases hq with
  | intro a ha =>
      cases ha.right with
      | intro b hb =>
          exact Exists.intro a
            (And.intro (hxy a ha.left)
              (Exists.intro b
                (And.intro hb.left hb.right)))

theorem add_le_add_left {x y : Cut} (hxy : x <= y) (z : Cut) :
    z + x <= z + y := by
  rw [add_comm z x]
  rw [add_comm z y]
  exact add_le_add_right hxy z

theorem add_le_add {w x y z : Cut} (hwx : w <= x) (hyz : y <= z) :
    w + y <= x + z := by
  exact le_trans (add_le_add_right hwx y) (add_le_add_left hyz x)

theorem add_nonneg {x y : Cut} (h0x : 0 <= x) (h0y : 0 <= y) :
    0 <= x + y := by
  have h : (0 : Cut) + 0 <= x + y := add_le_add h0x h0y
  rw [zero_add (0 : Cut)] at h
  exact h

theorem le_of_add_le_add_right {x y z : Cut} (h : x + z <= y + z) :
    x <= y := by
  have hcancel : (x + z) + (-z) <= (y + z) + (-z) :=
    add_le_add_right h (-z)
  have hx : (x + z) + (-z) = x := by
    rw [add_assoc x z (-z)]
    rw [add_neg z]
    rw [add_zero x]
  have hy : (y + z) + (-z) = y := by
    rw [add_assoc y z (-z)]
    rw [add_neg z]
    rw [add_zero y]
  rw [hx, hy] at hcancel
  exact hcancel

theorem le_of_add_le_add_left {x y z : Cut} (h : z + x <= z + y) :
    x <= y := by
  apply le_of_add_le_add_right (z := z)
  rw [add_comm x z]
  rw [add_comm y z]
  exact h

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
