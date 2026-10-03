module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Order

/-!
# Addition of cuts

Addition is pointwise on members: a rational belongs to `x + y` when it is a
sum of a member of `x` and a member of `y`. That the result is again a cut --
downward closed and without a greatest element -- is what this file checks.

Addition is the easy operation on cuts, and the only one that needs no case
analysis on signs. Everything about multiplication further down is harder for
exactly the reason addition is not: sums of members stay members whatever the
signs, products do not.

## Position in the development

Above `Dedekind.Order`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind

namespace Cut

/-- Sum of two cuts: a rational belongs to `x + y` when it splits as a member
of `x` plus a member of `y`. Sums of members stay below the boundary whatever
the signs of the operands, so all four cut conditions hold without any case
analysis. -/
def add (x y : Cut) : Cut where
  mem q :=
    Exists fun a : Rat =>
      And (x.mem a)
        (Exists fun b : Rat => And (y.mem b) (q = a + b))
  nonempty := by
    cases x.nonempty with
    | intro a ha =>
        cases y.nonempty with
        | intro b hb =>
            exact Exists.intro (a + b)
              (Exists.intro a
                (And.intro ha
                  (Exists.intro b (And.intro hb rfl))))
  proper := by
    cases x.proper with
    | intro ux hux =>
        cases y.proper with
        | intro uy huy =>
            refine Exists.intro (ux + uy) ?_
            intro hq
            cases hq with
            | intro a ha =>
                cases ha.right with
                | intro b hb =>
                    have haux : a <= ux :=
                      Cut.le_of_mem_of_not_mem ha.left hux
                    have hbuy : b <= uy :=
                      Cut.le_of_mem_of_not_mem hb.left huy
                    have hax : a < ux := by
                      cases Tautology.RealBasic.ModuleBackend.Rat.le_cases haux with
                      | inl hlt => exact hlt
                      | inr heq =>
                          have hxux : x.mem ux := by
                            rw [← heq]
                            exact ha.left
                          exact False.elim (hux hxux)
                    have hby : b < uy := by
                      cases Tautology.RealBasic.ModuleBackend.Rat.le_cases hbuy with
                      | inl hlt => exact hlt
                      | inr heq =>
                          have hyuy : y.mem uy := by
                            rw [← heq]
                            exact hb.left
                          exact False.elim (huy hyuy)
                    have hab : a + b < ux + uy :=
                      Tautology.RealBasic.ModuleBackend.Rat.add_lt_add hax hby
                    rw [← hb.right] at hab
                    exact _root_.Rat.lt_irrefl hab
  downward := by
    intro p q hpq hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            have hpab : p < a + b := by
              rw [← hb.right]
              exact hpq
            have hpa : p - b < a :=
              (_root_.Rat.sub_lt_iff
                (a := p) (b := a) (c := b)).mpr hpab
            have heq : (p - b) + b = p := by
              rw [_root_.Rat.sub_eq_add_neg]
              rw [_root_.Rat.add_assoc]
              rw [_root_.Rat.neg_add_cancel]
              rw [_root_.Rat.add_zero]
            exact Exists.intro (p - b)
              (And.intro (x.downward hpa ha.left)
                (Exists.intro b (And.intro hb.left heq.symm)))
  no_greatest := by
    intro q hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            cases x.no_greatest ha.left with
            | intro a' ha' =>
                refine Exists.intro (a' + b) ?_
                constructor
                · exact Exists.intro a'
                    (And.intro ha'.left
                      (Exists.intro b (And.intro hb.left rfl)))
                · rw [hb.right]
                  exact (_root_.Rat.add_lt_add_right
                    (a := a) (b := a') (c := b)).mpr ha'.right

instance : Add Cut where
  add := add

theorem add_comm (x y : Cut) : x + y = y + x := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            refine Exists.intro b ?_
            refine And.intro hb.left ?_
            refine Exists.intro a ?_
            refine And.intro ha.left ?_
            rw [_root_.Rat.add_comm]
            exact hb.right
  · intro hq
    cases hq with
    | intro b hb =>
        cases hb.right with
        | intro a ha =>
            refine Exists.intro a ?_
            refine And.intro ha.left ?_
            refine Exists.intro b ?_
            refine And.intro hb.left ?_
            rw [_root_.Rat.add_comm]
            exact ha.right

theorem add_assoc (x y z : Cut) :
    (x + y) + z = x + (y + z) := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | intro s hs =>
        cases hs.right with
        | intro c hc =>
            cases hs.left with
            | intro a ha =>
                cases ha.right with
                | intro b hb =>
                    refine Exists.intro a ?_
                    refine And.intro ha.left ?_
                    refine Exists.intro (b + c) ?_
                    constructor
                    · exact Exists.intro b
                        (And.intro hb.left
                          (Exists.intro c (And.intro hc.left rfl)))
                    · calc
                        q = s + c := hc.right
                        _ = (a + b) + c := by rw [hb.right]
                        _ = a + (b + c) := by rw [_root_.Rat.add_assoc]
  · intro hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro t ht =>
            cases ht.left with
            | intro b hb =>
                cases hb.right with
                | intro c hc =>
                    refine Exists.intro (a + b) ?_
                    constructor
                    · exact Exists.intro a
                        (And.intro ha.left
                          (Exists.intro b (And.intro hb.left rfl)))
                    · exact Exists.intro c
                        (And.intro hc.left (by
                          calc
                            q = a + t := ht.right
                            _ = a + (b + c) := by rw [hc.right]
                            _ = (a + b) + c := by rw [← _root_.Rat.add_assoc]))

theorem add_zero (x : Cut) :
    x + 0 = x := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | intro a ha =>
        cases ha.right with
        | intro b hb =>
            have hb0 : b < 0 := (Cut.mem_zero (q := b)).mp hb.left
            have hab : a + b < a + 0 :=
              (_root_.Rat.add_lt_add_left
                (a := b) (b := 0) (c := a)).mpr hb0
            have hqa : q < a := by
              rw [hb.right]
              rw [_root_.Rat.add_zero] at hab
              exact hab
            exact x.downward hqa ha.left
  · intro hxq
    cases x.no_greatest hxq with
    | intro r hr =>
        have hb0 : q - r < 0 := by
          apply (_root_.Rat.sub_lt_iff
            (a := q) (b := 0) (c := r)).mpr
          rw [_root_.Rat.zero_add]
          exact hr.right
        have heq : r + (q - r) = q := by
          rw [_root_.Rat.sub_eq_add_neg]
          rw [_root_.Rat.add_comm q (-r)]
          rw [← _root_.Rat.add_assoc]
          rw [_root_.Rat.add_neg_cancel]
          rw [_root_.Rat.zero_add]
        exact Exists.intro r
          (And.intro hr.left
            (Exists.intro (q - r)
              (And.intro ((Cut.mem_zero (q := q - r)).mpr hb0)
                heq.symm)))

theorem zero_add (x : Cut) : 0 + x = x := by
  rw [add_comm (0 : Cut) x]
  exact add_zero x

end Cut

end Dedekind
end ModuleBackend
end RealBasic
end Tautology
