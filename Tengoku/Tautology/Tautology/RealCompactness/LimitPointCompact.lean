import Tengoku.Tautology.Tautology.RealBootstrap.Lattice
import Tengoku.Tautology.Tautology.RealCompactness.CompactSequential
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.AccumToSeq

/-!
# Limit-point compactness joins the other two

The third notion and its two bridges: limit-point compact is again equivalent
to closed and bounded, and hence to both compact and sequentially compact.

The substantial direction is that a limit-point compact set is sequentially
compact, and it does not re-derive its machinery. It reuses the apparatus of
the route graph's accumulation-to-sequential edge in
`Tautology.RealCompactness.ClosedInterval.AccumToSeq` -- frequent values, the
range set, the index-selection functions -- so the same argument serves both a
graph edge and a subset-level theorem. If some value recurs infinitely often
the constant subsequence works; otherwise the range is infinite, has an
accumulation point, and the selection functions thin the sequence towards it.

Pulling an accumulation point back into a closed set is done by taking the
radius to be the smaller of the two gaps to the ends of the witnessing
interval.

## Position and role

Implementation module. Its hypotheses are the accumulation form of
Bolzano-Weierstrass for one direction and, through sequential compactness, the
two Archimedean principles for the other; the compactness bridge additionally
consumes the closed-interval principle. All of them are supplied at the
selected carrier by `Tautology.RealCompactness.ClosedInterval.Selected`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem setBounded_mono {A S : alpha -> Prop}
    (hAS : SetPred.Subset A S)
    (hbdd : SetBounded F S) :
    SetBounded F A := by
  cases hbdd with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          exact Exists.intro left
            (Exists.intro right
              (fun x hxA => hright x (hAS x hxA)))

/-- An accumulation point of a subset of a closed set stays inside the
closed set. The complement of `S` is open, so a point `x` outside `S` owns
a witness interval; taking the radius to be the smaller of the two gaps to
that interval's endpoints forces the accumulated point inside the interval,
where the subset has no members. -/
theorem accumulation_mem_of_closed_subset
    {A S : alpha -> Prop} {x : alpha}
    (hclosed : IsClosed F S)
    (hAS : SetPred.Subset A S)
    (hacc : AccumulationPoint F A x) :
    S x := by
  classical
  by_cases hxS : S x
  · exact hxS
  · cases hclosed x hxS with
    | intro left hleft =>
        cases hleft with
        | intro right hright =>
            let leftGap := F.sub x left
            let rightGap := F.sub right x
            let eps := min2 F leftGap rightGap
            have hleftGap : F.lt F.zero leftGap :=
              sub_pos_of_lt F hright.left
            have hrightGap : F.lt F.zero rightGap :=
              sub_pos_of_lt F hright.right.left
            have heps : F.lt F.zero eps :=
              min2_pos F hleftGap hrightGap
            cases hacc eps heps with
            | intro y hy =>
                have hyclose : F.lt (abs F (F.sub y x)) eps := by
                  simpa [dist] using hy.right.right
                have hepsLeft : F.le eps leftGap :=
                  min2_le_left F leftGap rightGap
                have hepsRight : F.le eps rightGap :=
                  min2_le_right F leftGap rightGap
                have hsubLeft :
                    F.le left (F.sub x eps) := by
                  have hraw :
                      F.le (F.sub x leftGap) (F.sub x eps) :=
                    sub_le_sub_of_le_of_le F (F.le_refl x) hepsLeft
                  rwa [sub_self_sub F x left] at hraw
                have hyLeft0 :
                    F.lt (F.sub x eps) y :=
                  abs_sub_lt_left F hyclose
                have hyLeft : F.lt left y :=
                  lt_of_le_of_lt F hsubLeft hyLeft0
                have haddRight :
                    F.le (F.add x eps) right := by
                  have hraw := F.add_le_add_right hepsRight x
                  have hrightEq :
                      F.add rightGap x = right := by
                    dsimp [rightGap]
                    exact sub_add_cancel F right x
                  rwa [F.add_comm eps x, hrightEq] at hraw
                have hyRight0 :
                    F.lt y (F.add x eps) :=
                  abs_sub_lt_right F hyclose
                have hyRight : F.lt y right :=
                  lt_of_lt_of_le F hyRight0 haddRight
                have hyCompl :
                    SetPred.Compl S y :=
                  hright.right.right y (And.intro hyLeft hyRight)
                exact False.elim (hyCompl (hAS y hy.left))

/-- A closed bounded set is limit point compact, from the accumulation half
of Bolzano-Weierstrass: the subset inherits boundedness, the principle
returns an accumulation point of it, and closedness of the surrounding set
retains that point. -/
theorem limitPointCompact_of_closed_bounded
    (haccum : BolzanoWeierstrassAccumulationPrinciple F)
    {S : alpha -> Prop}
    (hclosed : IsClosed F S)
    (hbdd : SetBounded F S) :
    IsLimitPointCompact F S := by
  intro A hAS hInf
  have hA_bdd : SetBounded F A :=
    setBounded_mono F hAS hbdd
  cases haccum.accumulation_point A hA_bdd hInf with
  | intro x hacc =>
      exact Exists.intro x
        (And.intro
          (accumulation_mem_of_closed_subset F hclosed hAS hacc)
          hacc)

/-- Limit point compactness yields sequential compactness, by the two-case
argument: a value recurring arbitrarily far out gives a subsequence constant at
it, and when no value does, the range is infinite, so it has an accumulation
point, which the machinery of
`Tautology.RealCompactness.ClosedInterval.AccumToSeq` converts into a
convergent subsequence. That conversion spends the inverse Archimedean
principle, matching the hypothesis the same edge carries in the route graph. -/
theorem sequentiallyCompact_of_limitPointCompact
    (hinvNat : InvNatArchimedeanPrinciple F)
    {S : alpha -> Prop}
    (hlimpt : IsLimitPointCompact F S) :
    IsSequentiallyCompact F S := by
  intro u huS
  classical
  by_cases hfreq :
      Exists
        (fun x : alpha =>
          Compactness.AccumToSeq.ValueFrequent u x)
  · cases hfreq with
    | intro x hx =>
        cases hx 0 with
        | intro n hn =>
            have hxS : S x := by
              rw [<- hn.right]
              exact huS n
            exact Exists.intro x
              (And.intro hxS
                (Exists.intro
                  (Compactness.AccumToSeq.frequentIndex hx)
                  (And.intro
                    (Compactness.AccumToSeq.frequentIndex_subsequence hx)
                    (Compactness.AccumToSeq.frequent_subsequence_tendsto F hx))))
  · have hnone :
        forall x : alpha,
          Not (Compactness.AccumToSeq.ValueFrequent u x) := by
      intro x hx
      exact hfreq (Exists.intro x hx)
    let R := Compactness.AccumToSeq.RangeSet u
    have hRinf : Foundation.Cardinal.ListInfinite R :=
      Compactness.AccumToSeq.range_listInfinite_of_no_frequent hnone
    have hRS : SetPred.Subset R S := by
      intro x hx
      cases hx with
      | intro n hn =>
          rw [hn]
          exact huS n
    cases hlimpt R hRS hRinf with
    | intro l hl =>
        exact Exists.intro l
          (And.intro hl.left
            (Exists.intro
              (Compactness.AccumToSeq.closeIndex F hl.right)
              (And.intro
                (Compactness.AccumToSeq.closeIndex_subsequence F hl.right)
                (Compactness.AccumToSeq.closeSubsequence_tendsto F
                  hinvNat hl.right))))

/-- The characterization of limit point compactness on the line. From
closed-and-bounded it is the accumulation half of Bolzano-Weierstrass
alone; the converse is routed through sequential compactness, and so
carries that route's Archimedean hypotheses. -/
theorem limitPointCompact_iff_closed_bounded
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (haccum : BolzanoWeierstrassAccumulationPrinciple F)
    (S : alpha -> Prop) :
    IsLimitPointCompact F S <-> And (IsClosed F S) (SetBounded F S) := by
  constructor
  · intro hlimpt
    have hseq : IsSequentiallyCompact F S :=
      sequentiallyCompact_of_limitPointCompact F hinvNat hlimpt
    exact
      (sequentialCompact_iff_closed_bounded F
        harch hinvNat hBW S).mp hseq
  · intro h
    exact limitPointCompact_of_closed_bounded F haccum h.left h.right

/-- Compactness and limit point compactness agree, both directions obtained
from the two closed-and-bounded characterizations: the closed-interval
principle is spent on the compact side, the Bolzano-Weierstrass and
Archimedean inputs on the limit point side. -/
theorem compact_iff_limitPointCompact
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (haccum : BolzanoWeierstrassAccumulationPrinciple F)
    (S : alpha -> Prop) :
    IsCompact.{u} F S <-> IsLimitPointCompact F S := by
  constructor
  · intro hcompact
    have hclosedBounded :
        And (IsClosed F S) (SetBounded F S) :=
      (compact_iff_closed_bounded F hclosedIntervalCompact S).mp hcompact
    exact
      (limitPointCompact_iff_closed_bounded F
        harch hinvNat hBW haccum S).mpr hclosedBounded
  · intro hlimpt
    have hclosedBounded :
        And (IsClosed F S) (SetBounded F S) :=
      (limitPointCompact_iff_closed_bounded F
        harch hinvNat hBW haccum S).mp hlimpt
    show IsCompact.{u} F S
    exact
      (compact_iff_closed_bounded F hclosedIntervalCompact S).mpr
        hclosedBounded

/-- Sequential and limit point compactness agree: the direction from limit
point compactness is the direct two-case argument, the other factors
through closed-and-bounded. -/
theorem sequentialCompact_iff_limitPointCompact
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (haccum : BolzanoWeierstrassAccumulationPrinciple F)
    (S : alpha -> Prop) :
    IsSequentiallyCompact F S <-> IsLimitPointCompact F S := by
  constructor
  · intro hseq
    have hclosedBounded :
        And (IsClosed F S) (SetBounded F S) :=
      (sequentialCompact_iff_closed_bounded F
        harch hinvNat hBW S).mp hseq
    exact
      (limitPointCompact_iff_closed_bounded F
        harch hinvNat hBW haccum S).mpr hclosedBounded
  · intro hlimpt
    exact sequentiallyCompact_of_limitPointCompact F hinvNat hlimpt

/-- The limit point side of the theory assembled: the three equivalences
involving limit point compactness, from the five inputs -- the
closed-interval principle, both Archimedean principles, and the two halves
of Bolzano-Weierstrass. -/
def realSubsetLimitPointCompactnessPackage
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (haccum : BolzanoWeierstrassAccumulationPrinciple F) :
    RealSubsetLimitPointCompactnessPackage.{u} F where
  limit_point_iff_closed_bounded :=
    limitPointCompact_iff_closed_bounded F harch hinvNat hBW haccum
  compact_iff_limit_point :=
    compact_iff_limitPointCompact F
      hclosedIntervalCompact harch hinvNat hBW haccum
  sequential_iff_limit_point :=
    sequentialCompact_iff_limitPointCompact F
      harch hinvNat hBW haccum

/-- The whole general theory assembled under one interface: compactness,
sequential compactness and limit point compactness are interchangeable, and
each is exactly closed-and-bounded. Built from the same five principles, this
is the term `Tautology.RealTheory.Compactness` specializes to the selected real
line. -/
def realSubsetCompactnessInterface
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (harch : LinearArchimedeanPrinciple F)
    (hinvNat : InvNatArchimedeanPrinciple F)
    (hBW : BolzanoWeierstrassSequentialPrinciple F)
    (haccum : BolzanoWeierstrassAccumulationPrinciple F) :
    RealSubsetCompactnessInterface.{u} F where
  compact_iff_closed_bounded :=
    compact_iff_closed_bounded F hclosedIntervalCompact
  sequential_iff_closed_bounded :=
    sequentialCompact_iff_closed_bounded F harch hinvNat hBW
  limit_point_iff_closed_bounded :=
    limitPointCompact_iff_closed_bounded F harch hinvNat hBW haccum
  compact_iff_sequential :=
    compact_iff_sequentialCompact F
      hclosedIntervalCompact harch hinvNat hBW
  compact_iff_limit_point :=
    compact_iff_limitPointCompact F
      hclosedIntervalCompact harch hinvNat hBW haccum
  sequential_iff_limit_point :=
    sequentialCompact_iff_limitPointCompact F
      harch hinvNat hBW haccum

end IsOrderedFieldBaseLike
end Tautology
