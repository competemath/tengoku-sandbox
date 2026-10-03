import Tengoku.Tautology.Tautology.RealConnectedness.ConnectedComponents

/-!
# Every open set is a countable disjoint union of open intervals

The classical structure theorem for open subsets of the line, in the form this
library uses it: over a Dedekind-complete ordered field, every open set carries
an `OpenIntervalDecomposition` -- a countable collection of nonempty open
interval sets, pairwise disjoint, whose union is the set.

The mathematics is already done in
`Tautology.RealConnectedness.ConnectedComponents`; this module repackages it.
The collection is taken to be the image of the internal-rational parameters
under "component at", so countability comes from the image of a countable set,
and two parameters naming the same component collapse into one member of the
image. That is the point of the collection being a set of predicates rather
than an indexed family: the redundancy in the parameters is folded away by
taking the image, which is why the disjointness field can speak of members that
are unequal as predicates.

`IsOpenIntervalSet` bundles open, connected and interval-set. Over a complete
field those three are not independent -- `connected_iff_intervalSet` of
`Tautology.RealConnectedness.Connected` ties two of them together -- but the
bundle is what a consumer wants to receive in one piece.

## Position and role

Implementation module with no new construction and no new appeal to
completeness; both definitions are ordered-field vocabulary and the
single theorem inherits its completeness from the module below.
`Tautology.RealConnectedness.OpenIntervalClassification` refines a single
member of such a decomposition into one of four concrete shapes, and
`Tautology.RealTheory.Topology` specialises the results to the selected
carrier.
-/

namespace Tautology

namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- An open interval set that is also connected: the conjunction of the three
properties a member of a decomposition must carry. Over a complete field the
three are not independent -- connected and interval set are equivalent there
-- so the bundle is convenience: each consumer reads off the property it
needs without re-deriving the others. -/
def IsOpenIntervalSet (I : alpha -> Prop) : Prop :=
  And (IsOpen F I) (And (IsConnected F I) (IsIntervalSet F I))

/-- A decomposition of `U` into countably many open interval sets: the family
is a countable set `K` of predicates, each member is a nonempty open interval
set inside `U`, distinct members are disjoint, and every point of `U` lies in
exactly one member. Disjointness is demanded only of members that are
distinct as predicates, which is what lets a family produced as an image
identify equal components instead of listing them twice. -/
structure OpenIntervalDecomposition
    (U : alpha -> Prop)
    (K : (alpha -> Prop) -> Prop) : Prop where
  countable : Foundation.Cardinal.CountableSet K
  subset : forall I : alpha -> Prop, K I -> SetPred.Subset I U
  nonempty : forall I : alpha -> Prop, K I -> SetPred.Nonempty I
  interval :
    forall I : alpha -> Prop, K I -> IsOpenIntervalSet F I
  pairwise_disjoint :
    forall I J : alpha -> Prop,
      K I -> K J -> Not (I = J) -> SetPred.Disjoint I J
  union_eq :
    forall x : alpha,
      U x <->
        Exists (fun I : alpha -> Prop => And (K I) (I x))

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
