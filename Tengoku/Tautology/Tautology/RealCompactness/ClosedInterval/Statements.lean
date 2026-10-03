import Tengoku.Tautology.Tautology.RealCompactness.Compact
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean

/-!
# The compactness graph, declared

The vocabulary of the whole route graph and nothing else -- no proof appears in
this file. Read it first; every other file in
`RealCompactness/ClosedInterval/` implements or assembles something declared
here.

Nodes are `structure ... : Prop`: the two Bolzano-Weierstrass forms, sequential
and accumulation; the two closed-interval forms, finite subcover and Lebesgue
number; and `LindelofPrinciple`, which is an *input* node rather than something
this region proves -- the theorem lives in `Tautology.RealTopology.Lindelof`
and is wrapped into this shape by
`Tautology.RealCompactness.ClosedInterval.Routes` and `...Selected`.

Edges are `def ... : Prop`, and the whole point of the arrangement is that
**each edge carries its own price in its statement**:

* sequential to accumulation -- free;
* accumulation to sequential -- an inverse-natural Archimedean principle;
* finite subcover to Lebesgue number -- a universe bump to `max u 1`;
* Lebesgue number to finite subcover -- a linear Archimedean principle;
* sequential to finite subcover -- Lindelöf;
* finite subcover to sequential -- an inverse-natural Archimedean principle and
  the same universe bump.

Only two edges touch `max u 1`, and both for concrete reasons recorded in their
own modules. The packages (`BolzanoWeierstrassPackage`, `CompactnessPackage`,
`BWCompactnessBridge`, `CompactnessPrinciples`) exist so that a consumer can
receive a whole family of principles as one value.

## Position and role

Declaration module, the base of the route graph. It sits directly on the
predicates of `Tautology.RealCompactness.Compact`, stays entirely at
ordered-field level, and mentions neither completeness nor any Archimedean
principle in its own right -- every such cost is written onto an edge.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- `delta` is a Lebesgue number for the family `U` on `S`: it is positive, and
for every point of `S` some single member of the family already contains every
point of `S` within distance `delta` of that point, distance being the order
metric `dist` of `Tautology.RealTopology.Basic`. The member is chosen after the
centre, so it may change from point to point, and nothing is demanded of points
outside `S`. -/
def IsLebesgueNumber {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop)
    (delta : alpha) : Prop :=
  And (F.lt F.zero delta)
    (forall x : alpha,
      S x ->
        Exists
          (fun i : iota =>
            forall y : alpha,
              S y -> F.lt (dist F y x) delta -> U i y))

/-- The family has a Lebesgue number on `S`: some positive `delta` works.
The existential wrapper around `IsLebesgueNumber`, so that the Lebesgue
principle below can be stated without naming a radius. -/
def HasLebesgueNumber {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop) : Prop :=
  Exists (fun delta : alpha => IsLebesgueNumber F U S delta)

/-- A node of the graph: every sequence bounded on both sides, in the sense
of `SeqBounded`, has a convergent subsequence, presented the way
`HasConvergentSubsequence` presents one -- a strictly increasing index
function together with a limit for the reindexed sequence. Being a
propositional record, the node can be carried as a value and fed to the
edges below. -/
structure BolzanoWeierstrassSequentialPrinciple : Prop where
  convergent_subsequence :
    forall u : Nat -> alpha,
      SeqBounded F u ->
        Exists (fun l : alpha => HasConvergentSubsequence F u l)

/-- The companion node, in accumulation-point form: every set that is
bounded and that no list exhausts, in the sense of
`Foundation.Cardinal.ListInfinite`, has an accumulation point -- a point,
not required to belong to the set, every positive ball around which meets
the set in a point other than itself. The no-list hypothesis is what makes
the principle true in this form, since a bounded set small enough to be
listed can consist of isolated points. -/
structure BolzanoWeierstrassAccumulationPrinciple : Prop where
  accumulation_point :
    forall S : alpha -> Prop,
      SetBounded F S ->
        Foundation.Cardinal.ListInfinite S ->
          Exists (fun x : alpha => AccumulationPoint F S x)

/-- Both Bolzano-Weierstrass nodes in one value, so that a route which has
reached either form can deliver both once the edge between them has been
travelled. -/
structure BolzanoWeierstrassPackage : Prop where
  sequential : BolzanoWeierstrassSequentialPrinciple F
  accumulation : BolzanoWeierstrassAccumulationPrinciple F

/-- The edge from the sequential node to the accumulation node. It is a bare
implication, with no hypothesis beyond the node it starts from, which is why
this direction is travelled for free wherever the sequential node is
reached. -/
def BWSequentialToAccumulation : Prop :=
  BolzanoWeierstrassSequentialPrinciple F ->
    BolzanoWeierstrassAccumulationPrinciple F

/-- The edge back from the accumulation node to the sequential node. It
takes the inverse-natural Archimedean principle as an explicit hypothesis:
turning an accumulation point into a convergent subsequence means placing
terms inside balls of radii `1 / (n + 1)`, and only that principle makes
those radii eventually small. This is the one place in the
Bolzano-Weierstrass pair where more than ordered-field structure
enters. -/
def BWAccumulationToSequential : Prop :=
  InvNatArchimedeanPrinciple F ->
    BolzanoWeierstrassAccumulationPrinciple F ->
      BolzanoWeierstrassSequentialPrinciple F

/-- The two Bolzano-Weierstrass edges bundled, one field per direction.
Holding this value says the two nodes are equivalent for this field, modulo
the Archimedean hypothesis riding on the accumulation-to-sequential
direction. -/
structure BolzanoWeierstrassEquivalence : Prop where
  seq_to_acc : BWSequentialToAccumulation F
  acc_to_seq : BWAccumulationToSequential F

/-- A node of the graph: every family of open sets covering a closed
interval `[left, right]`, degenerate ones included since only `left ≤ right`
is demanded, has a finite subcover in the sense of `FiniteSubcover` -- a
plain list of indices whose members still cover. The index type is
universally quantified at this structure's universe, so a principle at `u`
sees covers by families living in `Type u`. -/
structure ClosedIntervalCompactnessPrinciple : Prop where
  finite_subcover :
    forall {iota : Type u} (left right : alpha)
      (U : iota -> alpha -> Prop),
        F.le left right ->
          (forall i : iota, IsOpen F (U i)) ->
            Covers U (ClosedInterval F left right) ->
              FiniteSubcover U (ClosedInterval F left right)

/-- The companion compactness node, in Lebesgue-number form: every open
cover of a closed interval has a Lebesgue number on it. It is carried as a
node of its own rather than read off the finite-subcover one because the
passage between the two is a pair of edges with separate costs, recorded in
`FiniteSubcoverToLebesgue` and `LebesgueToFiniteSubcover` below. -/
structure ClosedIntervalLebesguePrinciple : Prop where
  lebesgue_number :
    forall {iota : Type u} (left right : alpha)
      (U : iota -> alpha -> Prop),
        F.le left right ->
          (forall i : iota, IsOpen F (U i)) ->
            Covers U (ClosedInterval F left right) ->
              HasLebesgueNumber F U (ClosedInterval F left right)

/-- Both compactness nodes in one value. As with the Bolzano-Weierstrass
package, the point of the bundling is delivery: a consumer can take the
pair without knowing which edge produced each half. -/
structure CompactnessPackage : Prop where
  finite_subcover : ClosedIntervalCompactnessPrinciple.{u} F
  lebesgue_number : ClosedIntervalLebesguePrinciple.{u} F

/-- The edge from the finite-subcover node to the Lebesgue node, the first
of two edges whose compactness hypothesis sits at `max u 1`, a universe
above the conclusion. The reason is in how the edge runs: the given cover
is refined into a second cover whose members carry their own inner and
outer endpoints, and it is that refined family the compactness hypothesis
is applied to, its index type landing at `max u 1`. No Archimedean
assumption rides on this edge. -/
def FiniteSubcoverToLebesgue : Prop :=
  ClosedIntervalCompactnessPrinciple.{max u 1} F ->
    ClosedIntervalLebesguePrinciple.{u} F

/-- The edge back from the Lebesgue node to the finite-subcover node,
stated at one universe throughout, unlike its reverse. Its extra hypothesis
is the linear Archimedean principle: the proof grids the interval with mesh
half the Lebesgue number, and only that principle bounds the number of grid
points the interval's length needs. -/
def LebesgueToFiniteSubcover : Prop :=
  LinearArchimedeanPrinciple F ->
    ClosedIntervalLebesguePrinciple.{u} F ->
      ClosedIntervalCompactnessPrinciple.{u} F

/-- The two compactness edges bundled, one field per direction. The two
directions are not symmetric in cost: one raises a universe, the other
needs the linear Archimedean principle. -/
structure CompactnessEquivalence : Prop where
  finite_to_lebesgue : FiniteSubcoverToLebesgue.{u} F
  lebesgue_to_finite : LebesgueToFiniteSubcover.{u} F

/-- A node that feeds the graph from outside it: every open cover of every
set has a countable subcover, in the index-marking sense of
`CountableSubcover`. Over a Dedekind-complete field this is the theorem of
`Tautology.RealTopology.Lindelof`; the node is declared here because the
sequential-to-finite-subcover edge below runs on it. -/
structure LindelofPrinciple : Prop where
  countable_subcover :
    forall {iota : Type u} {S : alpha -> Prop}
      {U : iota -> alpha -> Prop},
        (forall i : iota, IsOpen F (U i)) ->
          Covers U S ->
            CountableSubcover U S

/-- The edge from the sequential Bolzano-Weierstrass node into the
compactness half of the graph. Its extra hypothesis is the Lindelöf node:
the proof first thins the cover to a countable one and enumerates it, then
lets a bounded sequence of not-yet-covered points converge, so that some
cover member around the limit is forced to contain a later term whose
index the enumeration has already supplied. Stated at a single universe:
the conclusion sees covers exactly at the level the Lindelöf hypothesis
does. -/
def BWSequentialToFiniteSubcover : Prop :=
  LindelofPrinciple.{u} F ->
    BolzanoWeierstrassSequentialPrinciple F ->
      ClosedIntervalCompactnessPrinciple.{u} F

/-- The edge back from the compactness half to the sequential
Bolzano-Weierstrass node, the second edge whose compactness hypothesis sits
at `max u 1`. There the reason is the cover the proof builds when no point
is a cluster of the sequence: it is indexed by the field's own carrier,
lifted to that universe, one ball per point. The inverse-natural
Archimedean hypothesis is consumed at the last step, converting the cluster
point this produces into a genuinely convergent subsequence. -/
def FiniteSubcoverToBWSequential : Prop :=
  InvNatArchimedeanPrinciple F ->
    ClosedIntervalCompactnessPrinciple.{max u 1} F ->
      BolzanoWeierstrassSequentialPrinciple F

/-- The two edges joining the Bolzano-Weierstrass half of the graph to the
compactness half, bundled. Both directions hold for the field once their
hypotheses are met, independently of how either endpoint was first
reached, which is why the bridge is packaged without mentioning any
route. -/
structure BWCompactnessBridge : Prop where
  bw_to_compact : BWSequentialToFiniteSubcover.{u} F
  compact_to_bw : FiniteSubcoverToBWSequential.{u} F

/-- The whole graph in one value: both Bolzano-Weierstrass nodes, both
compactness nodes, and the bridge between the two families. This is the
bundle the entry points build towards and `Routes` manufactures, and the
single value a consumer takes. -/
structure CompactnessPrinciples : Prop where
  bolzano_weierstrass : BolzanoWeierstrassPackage F
  compactness : CompactnessPackage.{u} F
  bridge : BWCompactnessBridge.{u} F

end IsOrderedFieldBaseLike
end Tautology
