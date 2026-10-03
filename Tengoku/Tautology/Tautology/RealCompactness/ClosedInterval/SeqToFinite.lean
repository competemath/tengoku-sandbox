import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealTopology.Sequential

/-!
# Edge: sequential Bolzano-Weierstrass gives finite subcovers

The crossing from the sequence family to the cover family, and it runs on a
`LindelofPrinciple` hypothesis. The reason is a mismatch of shape: a cover may
be indexed by anything at all, while a sequential argument can only race
against a countable skeleton. Lindelöf converts the cover into a countable
enumeration, and only then do finite prefixes make sense.

If no prefix of that enumeration covers the interval, each prefix leaves a
point uncovered; those points form a sequence, its convergent subsequence has a
limit in the interval, and the limit is covered by some slot of the
enumeration. Openness places a whole interval around the limit inside that
slot, the subsequence eventually enters it, and comparing indices shows the
slot was already in a prefix the point was supposed to avoid.

## Position and role

Edge module implementing `BWSequentialToFiniteSubcover`, exporting `target`.
The selected route travels this edge;
`Tautology.RealCompactness.ClosedInterval.Routes` and `...Selected` both
consume it. No completeness and no Archimedean principle enter here.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace SeqToFinite

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The bridge edge proved by this file: the sequential Bolzano-Weierstrass
principle yields finite subcovers of closed intervals, given the Lindelof
principle as extra hypothesis. The hypothesis is the price of bringing an
arbitrarily indexed cover within reach of a sequential argument: Lindelof
first exchanges the cover for a countable enumerated one, and the prefixes
of that enumeration are the finite lists the proof plays off. -/
def Target : Prop :=
  IsOrderedFieldBaseLike.BWSequentialToFiniteSubcover.{u} F

/-- The indices an enumeration has offered up to stage `N`, most recent
first, with empty slots contributing nothing. These prefixes form the
increasing family of candidate finite subcovers the proof races against. -/
def optionPrefix {iota : Type u}
    (e : Nat -> Option iota) : Nat -> List iota
  | 0 =>
      match e 0 with
      | some i => [i]
      | none => []
  | n + 1 =>
      match e (n + 1) with
      | some i => i :: optionPrefix e n
      | none => optionPrefix e n

theorem mem_optionPrefix_of_enum_le {iota : Type u}
    {e : Nat -> Option iota} {j N : Nat} {i : iota}
    (hjn : j <= N) (hej : e j = some i) :
    List.Mem i (optionPrefix e N) := by
  induction N generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      dsimp [optionPrefix]
      rw [hej]
      exact List.Mem.head []
  | succ N ih =>
      by_cases hjlast : j = N + 1
      · subst hjlast
        dsimp [optionPrefix]
        rw [hej]
        exact List.Mem.head _
      · have hjN : j <= N := by omega
        have hmem : List.Mem i (optionPrefix e N) :=
          ih hjN hej
        dsimp [optionPrefix]
        cases hlast : e (N + 1) with
        | none =>
            exact hmem
        | some k =>
            exact List.Mem.tail _ hmem

theorem not_listSubcover_exists_point {iota : Type u}
    {U : iota -> alpha -> Prop} {S : alpha -> Prop}
    {js : List iota}
    (hnot : Not (ListSubcover U S js)) :
    Exists
      (fun x : alpha =>
        And (S x)
          (forall i : iota, List.Mem i js -> Not (U i x))) := by
  classical
  by_cases hex :
      Exists
        (fun x : alpha =>
          And (S x)
            (forall i : iota, List.Mem i js -> Not (U i x)))
  · exact hex
  · have hsub : ListSubcover U S js := by
      intro x hxS
      by_cases hhit :
          Exists (fun i : iota => And (List.Mem i js) (U i x))
      · exact hhit
      · have hbad :
            Exists
              (fun y : alpha =>
                And (S y)
                  (forall i : iota, List.Mem i js -> Not (U i y))) := by
          refine Exists.intro x ?_
          constructor
          · exact hxS
          · intro i hi hUi
            exact hhit (Exists.intro i (And.intro hi hUi))
        exact False.elim (hex hbad)
    exact False.elim (hnot hsub)

/-- A point of the interval that no member of the `N`-th prefix covers,
chosen classically from the assumption that the prefix is not a subcover.
The run of these witnesses is the sequence the sequential principle is
applied to. -/
noncomputable def badPrefixPoint {iota : Type u}
    {U : iota -> alpha -> Prop} {S : alpha -> Prop}
    {e : Nat -> Option iota}
    (hnoPrefix :
      forall N : Nat, Not (ListSubcover U S (optionPrefix e N)))
    (N : Nat) : alpha :=
  Classical.choose (not_listSubcover_exists_point (hnoPrefix N))

theorem badPrefixPoint_mem {iota : Type u}
    {U : iota -> alpha -> Prop} {S : alpha -> Prop}
    {e : Nat -> Option iota}
    (hnoPrefix :
      forall N : Nat, Not (ListSubcover U S (optionPrefix e N)))
    (N : Nat) :
    S (badPrefixPoint hnoPrefix N) :=
  (Classical.choose_spec
    (not_listSubcover_exists_point (hnoPrefix N))).left

theorem badPrefixPoint_avoids {iota : Type u}
    {U : iota -> alpha -> Prop} {S : alpha -> Prop}
    {e : Nat -> Option iota}
    (hnoPrefix :
      forall N : Nat, Not (ListSubcover U S (optionPrefix e N)))
    (N : Nat) (i : iota)
    (hi : List.Mem i (optionPrefix e N)) :
    Not (U i (badPrefixPoint hnoPrefix N)) :=
  (Classical.choose_spec
    (not_listSubcover_exists_point (hnoPrefix N))).right i hi

/-- A convergent sequence of points of a closed interval has its limit in
the interval, because eventual bounds pass to the limit. This closedness is
what lands the subsequential limit back inside the interval that has to be
covered. -/
theorem limit_in_closed_interval
    {left right : alpha}
    {uSeq : Nat -> alpha} {l : alpha}
    (hlim : SeqTendsto F uSeq l)
    (hterms : forall n : Nat, ClosedInterval F left right (uSeq n)) :
    ClosedInterval F left right l := by
  constructor
  · exact
      seqTendsto_le_of_eventually_le F
        (seqTendsto_const F left) hlim
        (Eventually.of_forall (fun n => (hterms n).left))
  · exact
      seqTendsto_le_of_eventually_le F
        hlim (seqTendsto_const F right)
        (Eventually.of_forall (fun n => (hterms n).right))

theorem point_in_open_interval_of_tendsto {uSeq : Nat -> alpha}
    {l left right : alpha}
    (hlim : SeqTendsto F uSeq l)
    (hleft : F.lt left l)
    (hright : F.lt l right) :
    Eventually
      (fun n : Nat => F.OpenInterval left right (uSeq n)) := by
  exact
    Tautology.IsOrderedFieldBaseLike.point_in_open_interval_of_tendsto
      F hlim hleft hright

/-- The edge as a principle. If no prefix of the enumerated countable
subcover already covered, the bad prefix points would form a sequence in
the interval; a convergent subsequence of it would have its limit in the
interval, covered by some enumerated slot, and the subsequence would
eventually sit inside that member while the slot lies deep in the prefix
by then -- so that prefix would have covered after all. -/
theorem finiteSubcoverFromSequential
    (hlind : LindelofPrinciple.{u} F)
    (hseq : BolzanoWeierstrassSequentialPrinciple F) :
    ClosedIntervalCompactnessPrinciple.{u} F where
  finite_subcover := by
    classical
    intro iota left right U hle hopen hcover
    by_cases hfinite :
        FiniteSubcover U (ClosedInterval F left right)
    · exact hfinite
    · cases hlind.countable_subcover hopen hcover with
      | intro J hJ =>
          cases hJ.left with
          | intro e henumerates =>
              have hnoPrefix :
                  forall N : Nat,
                    Not
                      (ListSubcover U (ClosedInterval F left right)
                        (optionPrefix e N)) := by
                intro N hprefix
                exact hfinite
                  (Exists.intro (optionPrefix e N) hprefix)
              let uSeq : Nat -> alpha :=
                fun N => badPrefixPoint hnoPrefix N
              have hterms :
                  forall N : Nat,
                    ClosedInterval F left right (uSeq N) := by
                intro N
                exact badPrefixPoint_mem hnoPrefix N
              have hbdd : SeqBounded F uSeq := by
                refine Exists.intro left ?_
                refine Exists.intro right ?_
                intro N
                exact hterms N
              cases hseq.convergent_subsequence uSeq hbdd with
              | intro l hl =>
                  cases hl with
                  | intro phi hphi_lim =>
                      have hphi := hphi_lim.left
                      have hlim := hphi_lim.right
                      have hl_interval :
                          ClosedInterval F left right l :=
                        limit_in_closed_interval F hlim
                          (fun n => hterms (phi n))
                      cases hJ.right l hl_interval with
                      | intro i hi =>
                          have hJi : J i := hi.left
                          have hUi_l : U i l := hi.right
                          cases henumerates i hJi with
                          | intro j hej =>
                              cases hopen i l hUi_l with
                              | intro a ha =>
                                  cases ha with
                                  | intro b hb =>
                                      have hinside := hb.right.right
                                      have hinsideEventual :
                                          Eventually
                                            (fun n : Nat =>
                                              F.OpenInterval a b
                                                (subsequence uSeq phi n)) :=
                                        point_in_open_interval_of_tendsto F
                                          hlim hb.left hb.right.left
                                      cases hinsideEventual with
                                      | intro N hN =>
                                          let k := Nat.max N j
                                          have hNk : N <= k :=
                                            Nat.le_max_left N j
                                          have hjk : j <= k :=
                                            Nat.le_max_right N j
                                          have hphi_ge : k <= phi k :=
                                            subsequenceIndex_ge_self hphi k
                                          have hj_phi : j <= phi k :=
                                            Nat.le_trans hjk hphi_ge
                                          have hi_prefix :
                                              List.Mem i
                                                (optionPrefix e (phi k)) :=
                                            mem_optionPrefix_of_enum_le
                                              hj_phi hej
                                          have hopen_at :
                                              U i (uSeq (phi k)) := by
                                            have hinterval_sub :=
                                              hN k hNk
                                            dsimp [subsequence] at hinterval_sub
                                            exact hinside
                                              (uSeq (phi k)) hinterval_sub
                                          exact False.elim
                                            ((badPrefixPoint_avoids
                                                hnoPrefix (phi k) i hi_prefix)
                                              hopen_at)

/-- The exported edge `BWSequentialToFiniteSubcover`, Lindelof hypothesis
included; `Routes.pureBridge` forwards to it. -/
theorem target : Target.{u} F := by
  intro hlind hseq
  exact finiteSubcoverFromSequential F hlind hseq

end SeqToFinite
end Compactness
end IsOrderedFieldBaseLike
end Tautology
