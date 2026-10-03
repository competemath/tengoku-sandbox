module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Order
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Add
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Neg
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Archi

/-!
# Additive inverses

That `x + (-x)` is the cut of zero. Two theorems, and the harder inclusion
needs the Archimedean property of the rationals -- to show a negative rational
is a member one must find a gap of that size between `x` and its complement,
and only Archimedes supplies it.

This is why `Dedekind.Archi` sits below this file rather than being a late
consequence: the additive group structure already needs it.

## Position in the development

Above `Dedekind.Add`, `Dedekind.Neg` and `Dedekind.Archi`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

/-- The additive inverse law. The inclusion from `0` is the hard direction:
a negative rational `q` can be written as a member of `x` plus a member of
`-x` only because `exists_inner_outer_gap_lt` supplies a gap between the
members and the nonmembers of `x` of width below `-q`. -/
theorem add_neg (x : Cut) : x + (-x) = 0 := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            cases hb.left with
            | intro r hr =>
                have har : a <= r := by
                  have hnlt : Not (r < a) := by
                    intro hra
                    exact hr.left (x.downward hra ha.left)
                  exact _root_.Rat.not_lt.mp hnlt
                have hbneg : a + b < a + -r :=
                  (_root_.Rat.add_lt_add_left (a := b) (b := -r) (c := a)).mpr
                    hr.right
                have hqneg : q < a + -r :=
                  by
                    rw [hb.right]
                    exact hbneg
                have haneg : a + -r <= 0 := by
                  have h : a + -r <= r + -r :=
                    (_root_.Rat.add_le_add_right (a := a) (b := r) (c := -r)).mpr har
                  rw [_root_.Rat.add_neg_cancel] at h
                  exact h
                exact Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le hqneg haneg
  · intro hq0
    have hnegq : 0 < -q := by
      simpa [_root_.Rat.neg_zero] using
        (_root_.Rat.neg_lt_neg (a := q) (b := 0) hq0)
    cases exists_inner_outer_gap_lt x hnegq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            have hq_negdiff : q < -(b - a) :=
              (_root_.Rat.lt_neg_iff (a := b - a) (b := q)).mp hb.right
            have hq_diff : q < a - b := by
              rw [_root_.Rat.neg_sub] at hq_negdiff
              exact hq_negdiff
            have hq_add : q < -b + a := by
              rw [_root_.Rat.sub_eq_add_neg] at hq_diff
              rw [_root_.Rat.add_comm] at hq_diff
              exact hq_diff
            have hq_sub : q - a < -b :=
              (_root_.Rat.sub_lt_iff (a := q) (b := -b) (c := a)).mpr hq_add
            have heq : a + (q - a) = q := by
              rw [_root_.Rat.sub_eq_add_neg]
              rw [_root_.Rat.add_comm q (-a)]
              rw [← _root_.Rat.add_assoc]
              rw [_root_.Rat.add_neg_cancel]
              rw [_root_.Rat.zero_add]
            exact Exists.intro a
              (And.intro ha.left
                (Exists.intro (q - a)
                  (And.intro
                    (Exists.intro b (And.intro hb.left hq_sub))
                    heq.symm)))

theorem neg_add (x : Cut) : -x + x = 0 := by
  rw [add_comm (-x) x]
  exact add_neg x

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
