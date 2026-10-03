import Tengoku.Tautology.Tautology.RealCompactness.HeineBorel
import Tengoku.Tautology.Tautology.RealCompactness.SequentialCompactness

/-!
# The compact and sequentially compact notions agree

A two-declaration bridge: compactness and sequential compactness of a subset
are equivalent, and the whole subset-level theory is packaged for delivery.

Both directions go through "closed and bounded" rather than passing between the
two notions directly, so this file adds no argument of its own -- it composes
`Tautology.RealCompactness.HeineBorel` with
`Tautology.RealCompactness.SequentialCompactness`. Consequently it inherits the
union of their hypotheses: the closed-interval principle on the compactness
side, the Bolzano-Weierstrass principle and both Archimedean principles on the
sequential side.

## Position and role

Implementation module, the exit of the subset-level half of the region. The
facade `Tautology.RealTheory.Compactness` specialises the package to the
selected carrier.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Compactness and sequential compactness agree on the line. Both
directions run through the closed-and-bounded characterization, so the
closed-interval principle enters with the compact side and the
Bolzano-Weierstrass and Archimedean inputs with the sequential one. -/
theorem compact_iff_sequentialCompact
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (S : alpha -> Prop) :
    IsCompact.{u} F S <-> IsSequentiallyCompact F S := by
  constructor
  · intro hcompact
    have hclosedBounded :
        And (IsClosed F S) (SetBounded F S) :=
      (compact_iff_closed_bounded F hclosedIntervalCompact S).mp hcompact
    exact
      (sequentialCompact_iff_closed_bounded F
        harch hinvNat hBW S).mpr hclosedBounded
  · intro hseq
    have hclosedBounded :
        And (IsClosed F S) (SetBounded F S) :=
      (sequentialCompact_iff_closed_bounded F
        harch hinvNat hBW S).mp hseq
    show IsCompact.{u} F S
    exact
      (compact_iff_closed_bounded F hclosedIntervalCompact S).mpr
        hclosedBounded

/-- The compactness side of the theory assembled: the three equivalences
not involving limit point compactness, from the closed-interval principle,
both Archimedean principles, and the sequential half of
Bolzano-Weierstrass. -/
def realSubsetCompactnessPackage
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F) :
    RealSubsetCompactnessPackage.{u} F where
  compact_iff_closed_bounded :=
    compact_iff_closed_bounded F hclosedIntervalCompact
  sequential_iff_closed_bounded :=
    sequentialCompact_iff_closed_bounded F harch hinvNat hBW
  compact_iff_sequential :=
    compact_iff_sequentialCompact F
      hclosedIntervalCompact harch hinvNat hBW

end IsOrderedFieldBaseLike
end Tautology
