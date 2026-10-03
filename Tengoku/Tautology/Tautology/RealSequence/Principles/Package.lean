import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# The three principles as one value

A single structure bundling the nested-interval, monotone-convergence and
Cauchy principles, so that an assembly can hand over everything a consumer
might need in one place rather than three. The counterpart of
`CompactnessPrinciples` of
`Tautology.RealCompactness.ClosedInterval.Statements`.

Pure declaration module.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The three nodes of the completeness graph in one value, so that a route
which has entered at any node can deliver all three once its crossings have
been travelled, and a consumer can receive the whole family without knowing
which entry produced it. -/
structure CompletenessPrinciples : Prop where
  nested : F.NestedIntervalPrinciple
  monotone : F.MonotoneConvergencePrinciple
  cauchy : F.CauchyCriterionPrinciple

end IsOrderedFieldBaseLike
end Tautology
