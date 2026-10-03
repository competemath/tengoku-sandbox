import Tengoku.Tautology.Tautology.RealTopology.Subspace
import Tengoku.Tautology.Tautology.RealSequence.Subsequence

/-!
# What compactness means for a subset

Vocabulary only: no theorem in this file. It fixes the predicates the rest of
the region argues about -- boundedness of a set and of a sequence, convergent
subsequences, accumulation points, finite subcovers, and the three compactness
notions -- together with the universally quantified statement forms and the
packages that bundle them.

Two shape decisions to read off the definitions. A finite subcover is presented
as a `List iota` of indices, so the data can be taken apart, in contrast with
`RealTopology.Basic.Subcover`, which marks indices by a predicate because there
only the property matters. And both `IsSequentiallyCompact` and
`IsLimitPointCompact` require the limit or accumulation point to lie back in
the set, which builds the cost of closedness into the definition -- the
equivalences with "closed and bounded" are not free, and this is where the
price is written down.

`IsCompact.{u}` pins the index type of a cover to a single universe `u`. That
rigidity is why covers indexed by points of the field have to be lifted through
`ULift.{u,0}` in `Tautology.RealCompactness.HeineBorel`, and it is the same
constraint that shows up as `max u 1` on two edges of the route graph.

## Position and role

Implementation module, the base of the region.
`Tautology.RealCompactness.ClosedInterval.Statements` builds its principles on
these predicates. Stated over an arbitrary ordered field; neither completeness
nor an Archimedean principle appears anywhere in the file.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The set fits inside a single interval: there are endpoint witnesses
`left` and `right` with `left ≤ x ≤ right` for every member. Boundedness is
stated through two endpoints, the presentation `ClosedInterval` uses, rather
than through a centre and a radius. -/
def SetBounded (S : alpha -> Prop) : Prop :=
  Exists
    (fun left : alpha =>
      Exists
        (fun right : alpha =>
          forall x : alpha, S x -> And (F.le left x) (F.le x right)))

/-- The sequence version of `SetBounded`: one pair of endpoints bounds every
term, uniformly in `n`. It is phrased directly on the sequence rather than as
boundedness of its range, so a caller never has to form the range first. -/
def SeqBounded (u : Nat -> alpha) : Prop :=
  Exists
    (fun left : alpha =>
      Exists
        (fun right : alpha =>
          forall n : Nat, And (F.le left (u n)) (F.le (u n) right)))

/-- The sequence `u` has a subsequence converging to the given limit `l`:
there is a strictly increasing index map, in the sense of `SubsequenceIndex`,
whose reindexing of `u` tends to `l`. The limit is a parameter rather than an
existential, so this is the "converges to this `l`" form that
`IsSequentiallyCompact` hands back together with the fact that `l` stays in
the set. -/
def HasConvergentSubsequence (u : Nat -> alpha) (l : alpha) : Prop :=
  Exists
    (fun phi : Nat -> Nat =>
      And (SubsequenceIndex phi)
        (SeqTendsto F (subsequence u phi) l))

/-- `x` is an accumulation point of `S`: every positive radius admits a point
of `S`, other than `x` itself, within that distance of `x`. Membership of `x`
in `S` is neither demanded nor implied, and distance is the order metric
`dist` of `Tautology.RealTopology.Basic`. -/
def AccumulationPoint (S : alpha -> Prop) (x : alpha) : Prop :=
  forall eps : alpha,
    F.lt F.zero eps ->
      Exists
        (fun y : alpha =>
          And (S y)
            (And (Not (y = x)) (F.lt (dist F y x) eps)))

/-- A finite subcover presented as a list of indices: every point of `S` lies
in some family member whose index is on the list. Finiteness is carried by the
`List`, unlike the predicate-marking `Subcover` of
`Tautology.RealTopology.Basic`, because a subcover here is data to be extracted
by a proof, not a property to be checked of one. -/
def ListSubcover {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop)
    (js : List iota) : Prop :=
  forall x : alpha, S x -> Exists (fun i : iota => And (List.Mem i js) (U i x))

/-- The family `U` admits a finite subcover of `S`: some index list works. This
is the conclusion shape of the whole region: `IsCompact` below and the
closed-interval principle of
`Tautology.RealCompactness.ClosedInterval.Statements` both end in it. -/
def FiniteSubcover {iota : Type u}
    (U : iota -> alpha -> Prop) (S : alpha -> Prop) : Prop :=
  Exists (fun js : List iota => ListSubcover U S js)

/-- `S` is compact: every open cover admits a finite subcover, the index type
of the cover ranging over every type of the single universe `u`. That rigidity,
one fixed universe for all index types at once, is why proofs that index a
cover by the points of the field itself have to lift through `ULift`, as the
two converse directions in `Tautology.RealCompactness.HeineBorel` do. -/
def IsCompact (S : alpha -> Prop) : Prop :=
  forall {iota : Type u} (U : iota -> alpha -> Prop),
    (forall i : iota, IsOpen F (U i)) ->
      Covers U S -> FiniteSubcover U S

/-- `S` is sequentially compact: every sequence valued in `S` has a
subsequence converging to a limit that itself lies in `S`. Demanding the
limit inside `S` builds closedness into the notion, which is what lets the
equivalences stated below single out exactly the closed bounded sets. -/
def IsSequentiallyCompact (S : alpha -> Prop) : Prop :=
  forall u : Nat -> alpha,
    (forall n : Nat, S (u n)) ->
      Exists
        (fun l : alpha =>
          And (S l) (HasConvergentSubsequence F u l))

/-- `S` is limit point compact: every subset of `S` that is infinite, in the
sense of `Foundation.Cardinal.ListInfinite` that no list exhausts it, has an
accumulation point. The point is required to lie in `S` itself, not merely
in the subset, which is the half of the statement that will cost closedness
of `S` later. -/
def IsLimitPointCompact (S : alpha -> Prop) : Prop :=
  forall A : alpha -> Prop,
    SetPred.Subset A S ->
      Foundation.Cardinal.ListInfinite A ->
        Exists
          (fun x : alpha =>
            And (S x) (AccumulationPoint F A x))

/-- The Heine-Borel statement as a `Prop`: the compact subsets of the line are
exactly the closed bounded ones. It is a definition and not a theorem because
it serves as a field of the packages below; the content is supplied by
`Tautology.RealCompactness.HeineBorel`, and only the closed-and-bounded
direction of it needs completeness. -/
def CompactIffClosedBoundedStatement : Prop :=
  forall S : alpha -> Prop,
    IsCompact.{u} F S <-> And (IsClosed F S) (SetBounded F S)

/-- The sequentially compact subsets are exactly the closed bounded ones, as a
`Prop` for packaging. `Tautology.RealCompactness.SequentialCompactness`
discharges it: the direction from closed-and-bounded needs Bolzano-Weierstrass
alone, while extracting closedness and boundedness from sequential compactness
costs one Archimedean principle each. -/
def SequentialCompactIffClosedBoundedStatement : Prop :=
  forall S : alpha -> Prop,
    IsSequentiallyCompact F S <-> And (IsClosed F S) (SetBounded F S)

/-- Compactness and sequential compactness agree, as a `Prop` for packaging.
`Tautology.RealCompactness.CompactSequential` proves it by showing each side
equivalent to closed-and-bounded, rather than by a direct passage between
the two notions. -/
def CompactIffSequentialCompactStatement : Prop :=
  forall S : alpha -> Prop,
    IsCompact.{u} F S <-> IsSequentiallyCompact F S

/-- The limit point compact subsets are exactly the closed bounded ones, as a
`Prop` for packaging. `Tautology.RealCompactness.LimitPointCompact` discharges
it, the return direction from the accumulation half of Bolzano-Weierstrass
alone and the forward one routed through sequential compactness. -/
def LimitPointCompactIffClosedBoundedStatement : Prop :=
  forall S : alpha -> Prop,
    IsLimitPointCompact F S <-> And (IsClosed F S) (SetBounded F S)

/-- Compactness and limit point compactness agree, as a `Prop` for packaging.
`Tautology.RealCompactness.LimitPointCompact` obtains both directions by
factoring through closed-and-bounded, so the hypothesis budget is the union of
the two characterizations: the closed-interval principle for the compact side,
the Bolzano-Weierstrass principles for the limit point side. -/
def CompactIffLimitPointCompactStatement : Prop :=
  forall S : alpha -> Prop,
    IsCompact.{u} F S <-> IsLimitPointCompact F S

/-- Sequential and limit point compactness agree, as a `Prop` for packaging,
discharged in `Tautology.RealCompactness.LimitPointCompact`: the limit point to
sequential direction is the direct one, the other runs through
closed-and-bounded. -/
def SequentialCompactIffLimitPointCompactStatement : Prop :=
  forall S : alpha -> Prop,
    IsSequentiallyCompact F S <-> IsLimitPointCompact F S

/-- The compactness half of the general theory, bundled: closed-and-bounded
characterizes compactness, characterizes sequential compactness, and the two
compactness notions agree. Carrying the three statements as one term is what
lets a downstream module assume "the compactness theory of this field"
without listing principles. -/
structure RealSubsetCompactnessPackage : Prop where
  compact_iff_closed_bounded : CompactIffClosedBoundedStatement.{u} F
  sequential_iff_closed_bounded :
    SequentialCompactIffClosedBoundedStatement F
  compact_iff_sequential :
    CompactIffSequentialCompactStatement.{u} F

/-- The limit point half of the general theory, bundled: closed-and-bounded
characterizes limit point compactness, and it agrees with both compactness
and sequential compactness. -/
structure RealSubsetLimitPointCompactnessPackage : Prop where
  limit_point_iff_closed_bounded :
    LimitPointCompactIffClosedBoundedStatement F
  compact_iff_limit_point :
    CompactIffLimitPointCompactStatement.{u} F
  sequential_iff_limit_point :
    SequentialCompactIffLimitPointCompactStatement F

/-- The six equivalences of the general theory in one structure: the three
notions, compact, sequentially compact and limit point compact, are
interchangeable, and each is exactly closed-and-bounded. This is the
full public face of the region, the term `Tautology.RealTheory.Compactness`
re-exports for the selected real line. -/
structure RealSubsetCompactnessInterface : Prop where
  compact_iff_closed_bounded : CompactIffClosedBoundedStatement.{u} F
  sequential_iff_closed_bounded :
    SequentialCompactIffClosedBoundedStatement F
  limit_point_iff_closed_bounded :
    LimitPointCompactIffClosedBoundedStatement F
  compact_iff_sequential :
    CompactIffSequentialCompactStatement.{u} F
  compact_iff_limit_point :
    CompactIffLimitPointCompactStatement.{u} F
  sequential_iff_limit_point :
    SequentialCompactIffLimitPointCompactStatement F

end IsOrderedFieldBaseLike
end Tautology
