import Tengoku.Tautology.Tautology.RealBootstrap.SignAlgebra

/-!
# The strict order

What `lt` obeys: irreflexivity, asymmetry, the mixed transitivities with `le`,
and compatibility with addition. The bundle axiomatises `le` and totality;
strict order was defined in `Tautology.RealBootstrap.Base` as `le` plus the
failure of the converse, so everything here is derived rather than assumed, and
the proofs run through totality wherever a case split is needed.

## Position and role

Implementation module over an arbitrary ordered field, and the last file before
positivity of one becomes available in `Tautology.RealBootstrap.PositiveOne`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem lt_of_le_of_not_le {x y : alpha}
    (hxy : F.le x y) (hyx : Not (F.le y x)) : F.lt x y :=
  (F.lt_def (x := x) (y := y)).mpr (And.intro hxy hyx)

theorem le_of_lt {x y : alpha} (hxy : F.lt x y) : F.le x y :=
  ((F.lt_def (x := x) (y := y)).mp hxy).left

theorem not_le_of_lt {x y : alpha} (hxy : F.lt x y) : Not (F.le y x) :=
  ((F.lt_def (x := x) (y := y)).mp hxy).right

theorem le_of_not_lt {x y : alpha}
    (h : Not (F.lt x y)) :
    F.le y x := by
  cases F.le_total y x with
  | inl hyx => exact hyx
  | inr hxy =>
      by_cases hyx : F.le y x
      · exact hyx
      · exact False.elim (h (lt_of_le_of_not_le F hxy hyx))

theorem lt_irrefl (x : alpha) : Not (F.lt x x) := by
  intro h
  exact (not_le_of_lt F h) (F.le_refl x)

theorem lt_asymm {x y : alpha} (hxy : F.lt x y) : Not (F.lt y x) := by
  intro hyx
  exact (not_le_of_lt F hxy) (le_of_lt F hyx)

theorem ne_of_lt {x y : alpha} (hxy : F.lt x y) : Not (x = y) := by
  intro h
  rw [h] at hxy
  exact lt_irrefl F y hxy

theorem pos_ne_zero {x : alpha}
    (hx : F.lt F.zero x) :
    Not (x = F.zero) := by
  intro h
  exact ne_of_lt F hx h.symm

theorem lt_of_le_of_lt {x y z : alpha}
    (hxy : F.le x y) (hyz : F.lt y z) : F.lt x z := by
  apply lt_of_le_of_not_le F
  · exact F.le_trans hxy (le_of_lt F hyz)
  · intro hzx
    have hzy : F.le z y := F.le_trans hzx hxy
    exact (not_le_of_lt F hyz) hzy

theorem lt_of_lt_of_le {x y z : alpha}
    (hxy : F.lt x y) (hyz : F.le y z) : F.lt x z := by
  apply lt_of_le_of_not_le F
  · exact F.le_trans (le_of_lt F hxy) hyz
  · intro hzx
    have hyx : F.le y x := F.le_trans hyz hzx
    exact (not_le_of_lt F hxy) hyx

theorem le_of_add_le_add_right {x y z : alpha}
    (h : F.le (F.add x z) (F.add y z)) : F.le x y := by
  have h' := F.add_le_add_right h (F.neg z)
  rwa [add_neg_cancel_right F x z, add_neg_cancel_right F y z] at h'

theorem add_lt_add_right {x y : alpha}
    (hxy : F.lt x y) (z : alpha) :
    F.lt (F.add x z) (F.add y z) := by
  apply lt_of_le_of_not_le F
  · exact F.add_le_add_right (le_of_lt F hxy) z
  · intro hrev
    exact (not_le_of_lt F hxy)
      (le_of_add_le_add_right F hrev)

theorem add_lt_add_left {x y : alpha}
    (hxy : F.lt x y) (z : alpha) :
    F.lt (F.add z x) (F.add z y) := by
  rw [F.add_comm z x, F.add_comm z y]
  exact add_lt_add_right F hxy z

theorem lt_trans {x y z : alpha}
    (hxy : F.lt x y) (hyz : F.lt y z) : F.lt x z := by
  apply lt_of_le_of_not_le F
  · exact F.le_trans (le_of_lt F hxy) (le_of_lt F hyz)
  · intro hzx
    have hzy : F.le z y := F.le_trans hzx (le_of_lt F hxy)
    exact (not_le_of_lt F hyz) hzy

theorem add_lt_add {w x y z : alpha}
    (hwx : F.lt w x) (hyz : F.lt y z) :
    F.lt (F.add w y) (F.add x z) :=
  lt_trans F (add_lt_add_right F hwx y) (add_lt_add_left F hyz x)

end IsOrderedFieldBaseLike
end Tautology
