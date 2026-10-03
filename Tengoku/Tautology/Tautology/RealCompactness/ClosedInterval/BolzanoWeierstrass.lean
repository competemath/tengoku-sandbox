import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.FromNestedSequential
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.SeqToAccum
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.AccumToSeq

/-!
# The Bolzano-Weierstrass half of the graph, packaged

Not an edge but an assembly layer. It bundles the inputs the two
Bolzano-Weierstrass nodes need -- the nested-interval principle and a dyadic
Archimedean principle for the entry, an inverse-natural Archimedean principle
for the accumulation-to-sequential edge -- and forwards the entry and both
edges into a single equivalence and package.

Nothing is proved here beyond the assembly; every component comes from
`Tautology.RealCompactness.ClosedInterval.FromNestedSequential`,
`...SeqToAccum` and `...AccumToSeq`. Completeness does not enter: the
nested-interval principle arrives as an explicit hypothesis, which is what
keeps the whole file at ordered-field level.

## Position and role

Assembly module, consumed by
`Tautology.RealCompactness.ClosedInterval.Selected` for the equivalence.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace BolzanoWeierstrass

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The three principles the Bolzano-Weierstrass results of this region are
stated against: the nested interval principle and the dyadic Archimedean
principle, which feed the entry from `FromNestedSequential`, and the
inverse-natural Archimedean principle, which the accumulation-to-sequential
edge demands. Bundled so a consumer can hand the whole context over at
once. -/
structure Inputs : Prop where
  nested : NestedIntervalPrinciple F
  dyadic : DyadicArchimedeanPrinciple F
  invNat : InvNatArchimedeanPrinciple F

/-- The hypothesis-free edge across the Bolzano-Weierstrass half of the
graph, forwarding to `SeqToAccum.target`: the sequential principle implies
the accumulation principle over any ordered field. -/
def seq_to_accumulation : BWSequentialToAccumulation F :=
  SeqToAccum.target F

/-- The edge back, forwarding to `AccumToSeq.target`: the accumulation
principle plus the inverse-natural Archimedean principle gives the
sequential one. Unlike its converse, this direction carries a hypothesis,
and it rides inside the edge statement itself. -/
def accumulation_to_seq : BWAccumulationToSequential F :=
  AccumToSeq.target F

/-- Both directions bundled: the two Bolzano-Weierstrass principles are
equivalent, one direction for free and the other at the cost of the
inverse-natural Archimedean principle. -/
def equivalence : BolzanoWeierstrassEquivalence F where
  seq_to_acc := seq_to_accumulation F
  acc_to_seq := accumulation_to_seq F

end BolzanoWeierstrass
end Compactness
end IsOrderedFieldBaseLike
end Tautology
