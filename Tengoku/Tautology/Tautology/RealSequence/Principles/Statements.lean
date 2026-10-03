import Tengoku.Tautology.Tautology.RealSequence.Basic

/-!
# The completeness principles, declared

The nodes of the completeness route graph and nothing else. Three principles,
each a `structure ... : Prop` over an arbitrary ordered field: monotone
convergence, the nested-interval principle in two fields (a common point for
any nested chain, and uniqueness when the lengths tend to zero), and the Cauchy
criterion. The two auxiliary predicates `NestedClosedIntervals` and
`IntervalLengthsToZero` say what a nested chain is and when it closes down.

Every implication between these nodes is proved in its own file of
`RealSequence/Principles/`, named for its direction, and takes its source node
as an explicit hypothesis. What the graph then shows is that the implications
are not equally cheap: reaching the Cauchy criterion from monotone convergence
is free, reaching it from nested intervals costs an Archimedean hypothesis and
five times the work, and the direct edge from the Cauchy criterion back to
nested intervals delivers only the uniqueness field, so the assemblies route
around it.

## Position and role

Declaration module, the base of the route graph. It is stated entirely at
ordered-field level: no completeness appears here, because completeness is what
the graph is *about* -- it enters only at the three `FromSup*` entry points.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The vocabulary of the nested-interval node: a descending chain of closed
intervals `[a n, b n]`, presented through its two endpoint sequences. Each
interval is nonempty (`a n ≤ b n`), the left endpoints do not decrease and
the right endpoints do not increase, so `[a m, b m]` sits inside `[a n, b n]`
whenever `n ≤ m`; the nesting is carried by the monotonicity of the endpoints
rather than by interval inclusion. -/
def NestedClosedIntervals (a b : Nat -> alpha) : Prop :=
  And
    (forall n : Nat, F.le (a n) (b n))
    (And
      (forall n m : Nat, n <= m -> F.le (a n) (a m))
      (forall n m : Nat, n <= m -> F.le (b m) (b n)))

/-- The side condition under which a nested family has at most one common
point: the lengths `b n - a n` tend to zero, in the sense of `SeqTendsto`. It
is stated against the two endpoint sequences alone rather than bundled with
`NestedClosedIntervals`, because the uniqueness argument consumes the nesting
only through the nonnegativity of the lengths. -/
def IntervalLengthsToZero (a b : Nat -> alpha) : Prop :=
  SeqTendsto F (fun n : Nat => F.sub (b n) (a n)) F.zero

/-- A node of the graph: every sequence that is monotone and bounded on the
matching side converges, with the increasing and decreasing directions held
as two fields so that a consumer can run one half alone (`FromMonotoneNested`
uses only the increasing half, on the left endpoints of a nested family). It
is also the node both of whose incoming edges are priced: the crossing from
the nested-interval node takes a dyadic Archimedean principle, the one from
the Cauchy node a linear one. -/
structure MonotoneConvergencePrinciple : Prop where
  increasing :
    forall u : Nat -> alpha,
      MonotoneIncreasing F u ->
        SeqBoundedAbove F u ->
          Exists (fun l : alpha => SeqTendsto F u l)
  decreasing :
    forall u : Nat -> alpha,
      MonotoneDecreasing F u ->
        SeqBoundedBelow F u ->
          Exists (fun l : alpha => SeqTendsto F u l)

/-- A node of the graph: every descending chain of closed intervals has a
common point, and exactly one when the lengths tend to zero. The two fields
differ in kind -- producing the point is where completeness gets spent,
whichever entry or edge supplies it, while uniqueness under shrinking lengths
is ordered-field reasoning (`NestedBasic.common_points_equal`) -- and the
split shows in the graph: the edge from the Cauchy node delivers the
uniqueness field only. -/
structure NestedIntervalPrinciple : Prop where
  exists_point :
    forall a b : Nat -> alpha,
      NestedClosedIntervals F a b ->
        Exists (fun x : alpha =>
          forall n : Nat,
            And (F.le (a n) x) (F.le x (b n)))
  unique_point_of_lengths_zero :
    forall a b : Nat -> alpha,
      NestedClosedIntervals F a b ->
        IntervalLengthsToZero F a b ->
          Exists
            (fun x : alpha =>
              And
                (forall n : Nat,
                  And (F.le (a n) x) (F.le x (b n)))
                (forall y : alpha,
                  (forall n : Nat,
                    And (F.le (a n) y) (F.le y (b n))) ->
                      y = x))

/-- A node of the graph: every Cauchy sequence converges. The crossing into
it from the monotone node runs at ordered-field level with no extra
hypothesis, and that is the crossing every assembled route uses for its last
step; the other one in, from the nested-interval node, is proved with an
inverse-natural Archimedean principle riding on it. -/
structure CauchyCriterionPrinciple : Prop where
  converges :
    forall u : Nat -> alpha,
      SeqCauchy F u ->
        Exists (fun l : alpha => SeqTendsto F u l)

end IsOrderedFieldBaseLike
end Tautology
