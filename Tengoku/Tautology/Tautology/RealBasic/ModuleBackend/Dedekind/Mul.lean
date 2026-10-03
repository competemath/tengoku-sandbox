module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.NegOrd
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.MulNonneg

/-!
# Multiplication in general

The nonnegative product of `Dedekind.MulNonneg` extended to all cuts by
cases on the signs of the factors, with the sign of the result read off
`Dedekind.NegOrd`.

Four cases, each reducing to the nonnegative one by negating a factor and
correcting the sign. The definition is therefore not a formula but a case
split, which is why the associativity and distributivity proofs below are
themselves case splits.

## Position in the development

Above `Dedekind.MulNonneg` and `Dedekind.NegOrd`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

/-- Product of two arbitrary cuts, by cases on the signs of the factors:
`mulNonneg` when both are nonnegative, and otherwise a nonpositive factor
replaced by its negation with the outcome corrected by a sign. The four
`mul_of_*` lemmas below are the computation rules of this split. -/
noncomputable def mul (x y : Cut) : Cut := by
  classical
  exact
    if h0x : 0 <= x then
      if h0y : 0 <= y then
        mulNonneg x y h0x h0y
      else
        -(mulNonneg x (-y) h0x (neg_nonneg_of_not_nonneg h0y))
    else
      if h0y : 0 <= y then
        -(mulNonneg (-x) y (neg_nonneg_of_not_nonneg h0x) h0y)
      else
        mulNonneg (-x) (-y)
          (neg_nonneg_of_not_nonneg h0x) (neg_nonneg_of_not_nonneg h0y)

noncomputable instance instMulCut : Mul Cut where
  mul := mul

theorem mul_of_nonneg_of_nonneg {x y : Cut} (h0x : 0 <= x) (h0y : 0 <= y) :
    x * y = mulNonneg x y h0x h0y := by
  classical
  change mul x y = mulNonneg x y h0x h0y
  unfold mul
  simp [h0x, h0y]

theorem mul_of_nonneg_of_not_nonneg {x y : Cut} (h0x : 0 <= x)
    (hny : Not (0 <= y)) :
    x * y = -(mulNonneg x (-y) h0x (neg_nonneg_of_not_nonneg hny)) := by
  classical
  change mul x y = -(mulNonneg x (-y) h0x (neg_nonneg_of_not_nonneg hny))
  unfold mul
  simp [h0x, hny]

theorem mul_of_not_nonneg_of_nonneg {x y : Cut} (hnx : Not (0 <= x))
    (h0y : 0 <= y) :
    x * y = -(mulNonneg (-x) y (neg_nonneg_of_not_nonneg hnx) h0y) := by
  classical
  change mul x y = -(mulNonneg (-x) y (neg_nonneg_of_not_nonneg hnx) h0y)
  unfold mul
  simp [hnx, h0y]

theorem mul_of_not_nonneg_of_not_nonneg {x y : Cut}
    (hnx : Not (0 <= x)) (hny : Not (0 <= y)) :
    x * y =
      mulNonneg (-x) (-y)
        (neg_nonneg_of_not_nonneg hnx) (neg_nonneg_of_not_nonneg hny) := by
  classical
  change mul x y =
    mulNonneg (-x) (-y)
      (neg_nonneg_of_not_nonneg hnx) (neg_nonneg_of_not_nonneg hny)
  unfold mul
  simp [hnx, hny]

theorem zero_mul (x : Cut) : 0 * x = 0 := by
  by_cases h0x : 0 <= x
  · rw [mul_of_nonneg_of_nonneg (Cut.le_refl 0) h0x]
    exact mulNonneg_zero_left x h0x
  · rw [mul_of_nonneg_of_not_nonneg (Cut.le_refl 0) h0x]
    rw [mulNonneg_zero_left (-x) (neg_nonneg_of_not_nonneg h0x)]
    exact neg_zero

theorem mul_one (x : Cut) : x * 1 = x := by
  by_cases h0x : 0 <= x
  · rw [mul_of_nonneg_of_nonneg h0x Cut.zero_le_one]
    exact mulNonneg_one_right x h0x
  · rw [mul_of_not_nonneg_of_nonneg h0x Cut.zero_le_one]
    rw [mulNonneg_one_right (-x) (neg_nonneg_of_not_nonneg h0x)]
    exact neg_neg x

theorem mul_comm (x y : Cut) : x * y = y * x := by
  by_cases h0x : 0 <= x
  · by_cases h0y : 0 <= y
    · rw [mul_of_nonneg_of_nonneg h0x h0y]
      rw [mul_of_nonneg_of_nonneg h0y h0x]
      exact mulNonneg_comm x y h0x h0y
    · rw [mul_of_nonneg_of_not_nonneg h0x h0y]
      rw [mul_of_not_nonneg_of_nonneg h0y h0x]
      rw [mulNonneg_comm x (-y) h0x (neg_nonneg_of_not_nonneg h0y)]
  · by_cases h0y : 0 <= y
    · rw [mul_of_not_nonneg_of_nonneg h0x h0y]
      rw [mul_of_nonneg_of_not_nonneg h0y h0x]
      rw [mulNonneg_comm (-x) y (neg_nonneg_of_not_nonneg h0x) h0y]
    · rw [mul_of_not_nonneg_of_not_nonneg h0x h0y]
      rw [mul_of_not_nonneg_of_not_nonneg h0y h0x]
      exact mulNonneg_comm (-x) (-y)
        (neg_nonneg_of_not_nonneg h0x) (neg_nonneg_of_not_nonneg h0y)

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
