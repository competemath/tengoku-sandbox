module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Add

/-!
# Negation of cuts

Negation cannot be pointwise. The members of `-x` are the rationals whose
negations are strictly above every member of `x`, and the strictness is
forced: taking the complement directly would produce a set with a greatest
element at a rational point, which is not a cut.

This asymmetry between addition and negation is the first place the
representation costs something, and it recurs wherever an operation has to
look at the upper half of a cut through the lower one.

## Position in the development

Above `Dedekind.Add`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind

namespace Cut

/-- Additive inverse: a rational belongs to `-x` when it lies strictly below
the negation of some rational outside `x`. The definition reads `x` through
its nonmembers because the pointwise negation of the member set is not
downward closed and would carry a greatest element at rational points. -/
def neg (x : Cut) : Cut where
  mem q := Exists (fun r : Rat => And (Not (x.mem r)) (q < -r))
  nonempty := by
    cases x.proper with
    | intro r hxr =>
        exact Exists.intro (-r - 1)
          (Exists.intro r
            (And.intro hxr
              (Tautology.RealBasic.ModuleBackend.Rat.sub_one_lt (-r))))
  proper := by
    cases x.nonempty with
    | intro a hxa =>
        refine Exists.intro (-a) ?_
        intro hq
        cases hq with
        | intro r hr =>
            have hra : r < a :=
              (_root_.Rat.neg_lt_neg_iff (a := a) (b := r)).mp hr.right
            exact hr.left (x.downward hra hxa)
  downward := by
    intro p q hpq hq
    cases hq with
    | intro r hr =>
        exact Exists.intro r
          (And.intro hr.left
            (Tautology.RealBasic.ModuleBackend.Rat.lt_trans hpq hr.right))
  no_greatest := by
    intro q hq
    cases hq with
    | intro r hr =>
        cases Tautology.RealBasic.ModuleBackend.Rat.exists_between
            hr.right with
        | intro s hs =>
            exact Exists.intro s
              (And.intro
                (Exists.intro r (And.intro hr.left hs.right))
                hs.left)

instance : Neg Cut where
  neg := neg

theorem neg_neg (x : Cut) : -(-x) = x := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | intro r hr =>
        cases Tautology.RealBasic.ModuleBackend.Rat.exists_between
            hr.right with
        | intro s hs =>
            have hrs : r < -s :=
              (_root_.Rat.lt_neg_iff (a := s) (b := r)).mp hs.right
            have hxs : x.mem s := by
              by_cases h : x.mem s
              · exact h
              · exact False.elim (hr.left (Exists.intro s (And.intro h hrs)))
            exact x.downward hs.left hxs
  · intro hxq
    cases x.no_greatest hxq with
    | intro r hr =>
        refine Exists.intro (-r) ?_
        constructor
        · intro hneg
          cases hneg with
          | intro s hs =>
              have hsr : s < r :=
                (_root_.Rat.neg_lt_neg_iff (a := r) (b := s)).mp hs.right
              exact hs.left (x.downward hsr hr.left)
        · simpa [_root_.Rat.neg_neg] using hr.right

instance : Sub Cut where
  sub x y := x + (-y)

end Cut

end Dedekind
end ModuleBackend
end RealBasic
end Tautology
