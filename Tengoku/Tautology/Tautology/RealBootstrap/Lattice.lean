import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra

/-!
# Binary maximum and minimum

`max` and `min` defined by a case split on the total order, with the
characterising inequalities. Totality is what makes the definitions total
without any decidability assumption.

Worth knowing before searching: the names `max` and `min` are declared again in
four places -- `Tautology.RealCompactness.HeineBorel`,
`Tautology.RealCompactness.ClosedInterval.FiniteToLebesgue`,
`Tautology.RealSequence.Principles.FromNestedCauchy` and
`Tautology.RealTheory.Order`. None of them is a rival definition: each is a
short-name alias forwarding to the `max2` and `min2` of this file, and each
reaches this file, the first three by importing it directly and the fourth
through the waist. A bare-name grep for `max` or `min` therefore finds the
aliases rather than the uses, and says nothing about how widely the definitions
here are consumed.

## Position and role

Implementation module over an arbitrary ordered field, used by
`Tautology.RealBootstrap.SupremumTools` and by the interval arguments above.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The larger of `x` and `y`: `y` when `x ≤ y`, `x` otherwise, by a classical
case split on the order. The suffix `2` leaves the bare name free, since the
waist module `Tautology.RealTheory.Order` re-exports this definition as `max`.
-/
noncomputable def max2 (x y : alpha) : alpha := by
  classical
  exact if F.le x y then y else x

/-- The smaller of `x` and `y`: `x` when `x ≤ y`, `y` otherwise, the
companion of `max2` under the same case split. -/
noncomputable def min2 (x y : alpha) : alpha := by
  classical
  exact if F.le x y then x else y

theorem le_max2_left (x y : alpha) :
    F.le x (max2 F x y) := by
  unfold max2
  by_cases hxy : F.le x y
  · simp [hxy]
  · simp [hxy]
    exact F.le_refl x

theorem le_max2_right (x y : alpha) :
    F.le y (max2 F x y) := by
  unfold max2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact F.le_refl y
  · simp [hxy]
    cases F.le_total y x with
    | inl hyx => exact hyx
    | inr hxy' => exact False.elim (hxy hxy')

theorem max2_le {x y z : alpha}
    (hxz : F.le x z)
    (hyz : F.le y z) :
    F.le (max2 F x y) z := by
  unfold max2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact hyz
  · simp [hxy]
    exact hxz

theorem min2_le_left (x y : alpha) :
    F.le (min2 F x y) x := by
  unfold min2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact F.le_refl x
  · simp [hxy]
    cases F.le_total y x with
    | inl hyx => exact hyx
    | inr hxy' => exact False.elim (hxy hxy')

theorem min2_le_right (x y : alpha) :
    F.le (min2 F x y) y := by
  unfold min2
  by_cases hxy : F.le x y
  · simp [hxy]
  · simp [hxy]
    exact F.le_refl y

theorem le_min2 {x y z : alpha}
    (hzx : F.le z x)
    (hzy : F.le z y) :
    F.le z (min2 F x y) := by
  unfold min2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact hzx
  · simp [hxy]
    exact hzy

theorem max2_comm (x y : alpha) :
    max2 F x y = max2 F y x := by
  apply F.le_antisymm
  · exact max2_le F (le_max2_right F y x) (le_max2_left F y x)
  · exact max2_le F (le_max2_right F x y) (le_max2_left F x y)

theorem min2_comm (x y : alpha) :
    min2 F x y = min2 F y x := by
  apply F.le_antisymm
  · exact le_min2 F (min2_le_right F x y) (min2_le_left F x y)
  · exact le_min2 F (min2_le_right F y x) (min2_le_left F y x)

theorem min2_pos {x y : alpha}
    (hx : F.lt F.zero x)
    (hy : F.lt F.zero y) :
    F.lt F.zero (min2 F x y) := by
  unfold min2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact hx
  · simp [hxy]
    exact hy

theorem lt_min2 {x y z : alpha}
    (hzx : F.lt z x)
    (hzy : F.lt z y) :
    F.lt z (min2 F x y) := by
  unfold min2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact hzx
  · simp [hxy]
    exact hzy

theorem max2_lt {x y z : alpha}
    (hxz : F.lt x z)
    (hyz : F.lt y z) :
    F.lt (max2 F x y) z := by
  unfold max2
  by_cases hxy : F.le x y
  · simp [hxy]
    exact hyz
  · simp [hxy]
    exact hxz

end IsOrderedFieldBaseLike
end Tautology
