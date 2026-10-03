import Tengoku.Tautology.Tautology.RealTopology.Closed

/-!
# Half-open intervals and rays

The interval shapes that `Tautology.RealTopology.Basic` and
`Tautology.RealTopology.Closed` do not already provide: the two half-open
intervals and the four rays, with their endpoint membership, nonemptiness and
containment facts, and the openness of the two open rays.

Vocabulary rather than theory -- every proof unfolds a pointwise definition.
Worth noting anyway: openness of a ray is witnessed by an interval of unit
span, `(x - 1, cut)`, so not even an Archimedean principle is needed, and the
containment lemmas take non-strict endpoint hypotheses on purpose, with
strictness transported through the moving point instead.

## Position and role

Implementation module. `Tautology.RealConnectedness.Connected` uses the open
rays to cut a set into a separation and proves all four rays are interval sets;
`Tautology.RealConnectedness.OpenIntervalClassification` uses the open rays as
the unbounded shapes; the rest of the library reaches the endpoint and
containment facts through the facade `Tautology.RealTheory.Topology`. Stated
over an arbitrary ordered field; completeness plays no part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The half-open interval `[left, right)`, containing its left endpoint but
not its right one. Nonemptiness here needs the strict `left < right`, whereas
`ClosedInterval` is nonempty already at `left ≤ right` -- which is why the two
membership halves live in separate theorems below. -/
def LeftClosedRightOpenInterval (left right : alpha) : alpha -> Prop :=
  fun x => And (F.le left x) (F.lt x right)

/-- The half-open interval `(left, right]`, the mirror image of
`LeftClosedRightOpenInterval`: open at its left endpoint, closed at its
right. -/
def LeftOpenRightClosedInterval (left right : alpha) : alpha -> Prop :=
  fun x => And (F.lt left x) (F.le x right)

/-- The ray strictly below `cut`, `{x | x < cut}`. These four rays are the
unbounded shapes of the interval vocabulary; `RealConnectedness` cuts a set
at a point into the traces of the two open rays to build its separations,
proves all four rays are interval sets, and takes the open rays as the
unbounded cases of its classification of open interval sets. -/
def OpenLowerRay (cut : alpha) : alpha -> Prop :=
  fun x => F.lt x cut

/-- The ray strictly above `cut`, `{x | cut < x}`; the companion of
`OpenLowerRay` on the other side. -/
def OpenUpperRay (cut : alpha) : alpha -> Prop :=
  fun x => F.lt cut x

/-- The ray below `cut` with the endpoint included; the closed counterpart
of `OpenLowerRay`. -/
def ClosedLowerRay (cut : alpha) : alpha -> Prop :=
  fun x => F.le x cut

/-- The ray above `cut` with the endpoint included; the closed counterpart
of `OpenUpperRay`. -/
def ClosedUpperRay (cut : alpha) : alpha -> Prop :=
  fun x => F.le cut x

/-- The lower ray is open over any ordered field: at a point `x < cut` the
witness interval is `(x - 1, cut)`. The unit reach comes from `sub_one_lt`
alone -- no Archimedean property is involved, since openness here is
witnessed by an interval rather than by a radius. -/
theorem openLowerRay_isOpen (cut : alpha) :
    IsOpen F (OpenLowerRay F cut) := by
  intro x hx
  refine Exists.intro (F.sub x F.one) ?_
  refine Exists.intro cut ?_
  exact
    And.intro (sub_one_lt F x)
      (And.intro hx
        (fun y hy => hy.right))

/-- The upper-ray companion of `openLowerRay_isOpen`, witnessed at
`cut < x` by the interval `(cut, x + 1)`. -/
theorem openUpperRay_isOpen (cut : alpha) :
    IsOpen F (OpenUpperRay F cut) := by
  intro x hx
  refine Exists.intro cut ?_
  refine Exists.intro (F.add x F.one) ?_
  exact
    And.intro hx
      (And.intro (lt_add_one F x)
        (fun y hy => hy.left))

theorem closedInterval_left_mem {left right : alpha}
    (h : F.le left right) :
    ClosedInterval F left right left :=
  And.intro (F.le_refl left) h

theorem closedInterval_right_mem {left right : alpha}
    (h : F.le left right) :
    ClosedInterval F left right right :=
  And.intro h (F.le_refl right)

theorem leftClosedRightOpen_left_mem {left right : alpha}
    (h : F.lt left right) :
    LeftClosedRightOpenInterval F left right left :=
  And.intro (F.le_refl left) h

theorem leftOpenRightClosed_right_mem {left right : alpha}
    (h : F.lt left right) :
    LeftOpenRightClosedInterval F left right right :=
  And.intro h (F.le_refl right)

theorem closedInterval_nonempty {left right : alpha}
    (h : F.le left right) :
    Exists (ClosedInterval F left right) :=
  Exists.intro left (closedInterval_left_mem F h)

theorem leftClosedRightOpen_nonempty {left right : alpha}
    (h : F.lt left right) :
    Exists (LeftClosedRightOpenInterval F left right) :=
  Exists.intro left (leftClosedRightOpen_left_mem F h)

theorem leftOpenRightClosed_nonempty {left right : alpha}
    (h : F.lt left right) :
    Exists (LeftOpenRightClosedInterval F left right) :=
  Exists.intro right (leftOpenRightClosed_right_mem F h)

theorem openInterval_subset_closedInterval (left right : alpha) :
    SetPred.Subset (OpenInterval F left right)
      (ClosedInterval F left right) := by
  intro x hx
  exact And.intro (le_of_lt F hx.left) (le_of_lt F hx.right)

theorem leftClosedRightOpen_subset_closedInterval (left right : alpha) :
    SetPred.Subset (LeftClosedRightOpenInterval F left right)
      (ClosedInterval F left right) := by
  intro x hx
  exact And.intro hx.left (le_of_lt F hx.right)

theorem leftOpenRightClosed_subset_closedInterval (left right : alpha) :
    SetPred.Subset (LeftOpenRightClosedInterval F left right)
      (ClosedInterval F left right) := by
  intro x hx
  exact And.intro (le_of_lt F hx.left) hx.right

/-- Endpoints may be widened at will: `[a, b]` sits inside `[c, d]` as soon
as each new endpoint reaches past an old one, `c ≤ a` and `b ≤ d`. Both
hypotheses are weak, so degenerate intervals are covered too. -/
theorem closedInterval_subset {a b c d : alpha}
    (hca : F.le c a)
    (hbd : F.le b d) :
    SetPred.Subset (ClosedInterval F a b)
      (ClosedInterval F c d) := by
  intro x hx
  exact And.intro
    (F.le_trans hca hx.left)
    (F.le_trans hx.right hbd)

/-- The open-interval version of `closedInterval_subset`, and the hypotheses
stay weak (`c ≤ a`, `b ≤ d`) even though the intervals are open: the
strictness passes through the moving point, which satisfies `c ≤ a < x` and
`x < b ≤ d`. -/
theorem openInterval_subset {a b c d : alpha}
    (hca : F.le c a)
    (hbd : F.le b d) :
    SetPred.Subset (OpenInterval F a b)
      (OpenInterval F c d) := by
  intro x hx
  exact And.intro
    (lt_of_le_of_lt F hca hx.left)
    (lt_of_lt_of_le F hx.right hbd)

end IsOrderedFieldBaseLike
end Tautology
