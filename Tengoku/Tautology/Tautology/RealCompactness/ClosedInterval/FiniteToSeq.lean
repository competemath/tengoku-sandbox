import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.AccumToSeq
import Tengoku.Tautology.Tautology.RealSequence.Order

/-!
# Edge: finite subcovers give sequential Bolzano-Weierstrass

The return crossing, carrying two hypotheses of quite different kinds.

The mathematical one is `InvNatArchimedeanPrinciple`, needed for the same
reason as in `Tautology.RealCompactness.ClosedInterval.AccumToSeq`: once a
cluster point is found, thinning towards it needs the radii to reach zero, and
this file reuses that module's radius vocabulary rather than duplicating it.

The other is not mathematical at all. The compactness hypothesis is taken at
the raised universe `max v 1`, because the cover built in the proof is indexed
by the points of the line themselves -- one avoidance interval per point -- and
those have to be lifted into the universe the hypothesis quantifies over. This
is the same rigidity `Tautology.RealCompactness.Compact` records for
`IsCompact.{u}`.

Given a bounded sequence with no cluster point, every point owns an interval
the sequence enters only finitely often; compactness reduces that cover to a
finite subfamily, and past the largest of the finitely many thresholds the
sequence has nowhere left to be.

## Position and role

Edge module implementing `FiniteSubcoverToBWSequential`, exporting `target`.
Consumed by the bridge in `Tautology.RealCompactness.ClosedInterval.Routes`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace FiniteToSeq

universe v

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The reverse bridge edge proved by this file: closed-interval compactness
yields the sequential Bolzano-Weierstrass principle, under two additions.
The inverse-natural Archimedean principle is needed to squeeze the
extracted subsequence to a limit; and the compactness hypothesis is taken
at the lifted universe `max v 1`, because the cover the proof builds is
indexed by the points of the line themselves and must be lifted through
`ULift` to fit an index universe the hypothesis quantifies over. -/
def Target : Prop :=
  IsOrderedFieldBaseLike.FiniteSubcoverToBWSequential.{v} F

/-- `l` is approached by `u` arbitrarily late: within every radius, some
term far enough out is close to `l`. The convergence-shaped notion the
proof works through, exchanged for a genuine convergent subsequence only
at the very end. -/
def SeqClusterAt (u : Nat -> alpha) (l : alpha) : Prop :=
  forall eps : alpha,
    F.lt F.zero eps ->
      forall N : Nat,
        Exists
          (fun n : Nat =>
            And (N <= n) (F.lt (dist F (u n) l) eps))

theorem not_cluster_eventually_far {u : Nat -> alpha} {l : alpha}
    (hnot : Not (SeqClusterAt F u l)) :
    Exists
      (fun eps : alpha =>
        And (F.lt F.zero eps)
          (Exists
            (fun N : Nat =>
              forall n : Nat,
                N <= n ->
                  Not (F.lt (dist F (u n) l) eps)))) := by
  classical
  by_cases hex :
      Exists
        (fun eps : alpha =>
          And (F.lt F.zero eps)
            (Exists
              (fun N : Nat =>
                forall n : Nat,
                  N <= n ->
                    Not (F.lt (dist F (u n) l) eps))))
  · exact hex
  · have hcluster : SeqClusterAt F u l := by
      intro eps heps N
      by_cases hN :
          Exists
            (fun n : Nat =>
              And (N <= n) (F.lt (dist F (u n) l) eps))
      · exact hN
      · have hbad :
            Exists
              (fun eps : alpha =>
                And (F.lt F.zero eps)
                  (Exists
                    (fun N : Nat =>
                      forall n : Nat,
                        N <= n ->
                          Not (F.lt (dist F (u n) l) eps)))) := by
          refine Exists.intro eps ?_
          constructor
          · exact heps
          · refine Exists.intro N ?_
            intro n hn hclose
            exact hN (Exists.intro n (And.intro hn hclose))
        exact False.elim (hex hbad)
    exact False.elim (hnot hcluster)

/-- When `x` is not a cluster point of `u`, a positive radius that the tail
of `u` never comes within, chosen classically together with `avoidStart`
from the failure of clustering. -/
noncomputable def avoidRadius {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) : alpha :=
  Classical.choose (not_cluster_eventually_far F (hnone x))

theorem avoidRadius_pos {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) :
    F.lt F.zero (avoidRadius F hnone x) :=
  (Classical.choose_spec
    (not_cluster_eventually_far F (hnone x))).left

/-- The stage from which the avoidance holds: beyond it no term of `u`
comes within `avoidRadius` of `x`. -/
noncomputable def avoidStart {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) : Nat :=
  Classical.choose
    (Classical.choose_spec
      (not_cluster_eventually_far F (hnone x))).right

theorem avoid_far {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) {n : Nat}
    (hn : avoidStart F hnone x <= n) :
    Not (F.lt (dist F (u n) x) (avoidRadius F hnone x)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (not_cluster_eventually_far F (hnone x))).right) n hn

/-- The open interval of radius `avoidRadius` around `x`, the member the
cover built in `cluster_exists_from_compactness` assigns to `x`. That no
tail term visits it is exactly what makes a finite subcover of these
intervals contradictory. -/
def AvoidOpen {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) : alpha -> Prop :=
  F.OpenInterval
    (F.sub x (avoidRadius F hnone x))
    (F.add x (avoidRadius F hnone x))

theorem openInterval_isOpen (a b : alpha) :
    F.IsOpen (F.OpenInterval a b) :=
  Tautology.IsOrderedFieldBaseLike.open_interval F a b
theorem avoidOpen_isOpen {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) :
    F.IsOpen (AvoidOpen F hnone x) :=
  openInterval_isOpen F
    (F.sub x (avoidRadius F hnone x))
    (F.add x (avoidRadius F hnone x))

theorem center_mem_avoidOpen {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    (x : alpha) :
    AvoidOpen F hnone x x := by
  unfold AvoidOpen
  constructor
  · exact sub_lt_self_of_pos F (avoidRadius_pos F hnone x)
  · have h := F.add_lt_add_left (avoidRadius_pos F hnone x) x
    rwa [F.add_zero] at h

theorem dist_lt_of_mem_avoidOpen {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    {x y : alpha}
    (hy : AvoidOpen F hnone x y) :
    F.lt (dist F y x) (avoidRadius F hnone x) := by
  unfold AvoidOpen at hy
  dsimp [dist]
  exact abs_sub_lt_of_bounds F hy.left hy.right

theorem not_mem_avoidOpen_after {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x))
    {x : alpha} {n : Nat}
    (hn : avoidStart F hnone x <= n) :
    Not (AvoidOpen F hnone x (u n)) := by
  intro hmem
  exact avoid_far F hnone x hn
    (dist_lt_of_mem_avoidOpen F hnone hmem)

/-- The latest avoidance stage among a list of points: the plain companion
of `liftedListMaxAvoidStart`, taken before the universe lift. -/
noncomputable def listMaxAvoidStart {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x)) :
    List alpha -> Nat
  | [] => 0
  | x :: xs => Nat.max (avoidStart F hnone x) (listMaxAvoidStart hnone xs)

theorem avoidStart_le_listMax {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x)) :
    forall {x : alpha} {xs : List alpha},
      List.Mem x xs -> avoidStart F hnone x <= listMaxAvoidStart F hnone xs := by
  intro x xs h
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      cases h with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          exact Nat.le_trans (ih htail)
            (Nat.le_max_right _ _)

/-- The latest avoidance stage among a lifted list of centres. The finite
subcover returns finitely many centres; past this bound, every one of
their neighbourhoods has been left by `u` for good. -/
noncomputable def liftedListMaxAvoidStart {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x)) :
    List (ULift.{max v 1, 0} alpha) -> Nat
  | [] => 0
  | x :: xs =>
      Nat.max (avoidStart F hnone x.down)
        (liftedListMaxAvoidStart hnone xs)

theorem avoidStart_le_liftedListMax {u : Nat -> alpha}
    (hnone : forall x : alpha, Not (SeqClusterAt F u x)) :
    forall {x : ULift.{max v 1, 0} alpha}
      {xs : List (ULift.{max v 1, 0} alpha)},
        List.Mem x xs ->
          avoidStart F hnone x.down <= liftedListMaxAvoidStart F hnone xs := by
  intro x xs h
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      cases h with
      | head =>
          exact Nat.le_max_left _ _
      | tail _ htail =>
          exact Nat.le_trans (ih htail)
            (Nat.le_max_right _ _)

/-- The heart of the edge: a bounded sequence in a compact interval has a
cluster point. If nothing clustered, each point would carry its
avoid-neighbourhood, these would cover the interval, compactness would
keep finitely many, and past the latest of their start stages no term of
`u` could lie in the interval at all. -/
theorem cluster_exists_from_compactness
    (hcompact : ClosedIntervalCompactnessPrinciple.{max v 1} F)
    {u : Nat -> alpha}
    (hbdd : SeqBounded F u) :
    Exists (fun l : alpha => SeqClusterAt F u l) := by
  classical
  by_cases hex : Exists (fun l : alpha => SeqClusterAt F u l)
  · exact hex
  · have hnone : forall x : alpha, Not (SeqClusterAt F u x) := by
      intro x hx
      exact hex (Exists.intro x hx)
    cases hbdd with
    | intro left hleft =>
        cases hleft with
        | intro right hbounds =>
            have hle : F.le left right :=
              F.le_trans (hbounds 0).left (hbounds 0).right
            let V : ULift.{max v 1, 0} alpha -> alpha -> Prop :=
              fun x => AvoidOpen F hnone x.down
            have hVopen :
                forall x : ULift.{max v 1, 0} alpha,
                  F.IsOpen (V x) := by
              intro x
              exact avoidOpen_isOpen F hnone x.down
            have hVcover :
                Covers.{max v 1} V (F.ClosedInterval left right) := by
              intro x _hx
              exact Exists.intro (ULift.up x)
                (center_mem_avoidOpen F hnone x)
            cases hcompact.finite_subcover left right V hle hVopen hVcover with
            | intro centers hcenters =>
                let N := liftedListMaxAvoidStart F hnone centers
                cases hcenters (u N) (hbounds N) with
                | intro c hc =>
                    have hNc :
                        avoidStart F hnone c.down <= N :=
                      avoidStart_le_liftedListMax F hnone hc.left
                    exact False.elim
                      ((not_mem_avoidOpen_after F hnone hNc) hc.right)

/-- The extraction for a cluster point: stage `k + 1` sits beyond stage `k`
and inside the `k`-th radius around it, the radius being the inverse of
`k + 1` borrowed from `AccumToSeq`. -/
noncomputable def clusterIndex {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt F u l) : Nat -> Nat
  | 0 =>
      Classical.choose
        (hcluster (AccumToSeq.invSuccRadius F 0)
          (AccumToSeq.invSuccRadius_pos F 0) 0)
  | k + 1 =>
      Classical.choose
        (hcluster (AccumToSeq.invSuccRadius F (k + 1))
          (AccumToSeq.invSuccRadius_pos F (k + 1))
          (clusterIndex hcluster k + 1))

theorem clusterIndex_step {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt F u l)
    (k : Nat) :
    clusterIndex F hcluster k < clusterIndex F hcluster (k + 1) := by
  have hle :
      clusterIndex F hcluster k + 1 <= clusterIndex F hcluster (k + 1) :=
    (Classical.choose_spec
      (hcluster (AccumToSeq.invSuccRadius F (k + 1))
        (AccumToSeq.invSuccRadius_pos F (k + 1))
        (clusterIndex F hcluster k + 1))).left
  omega

theorem clusterIndex_subsequence {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt F u l) :
    SubsequenceIndex (clusterIndex F hcluster) :=
  clusterIndex_step F hcluster

theorem clusterIndex_close {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt F u l)
    (k : Nat) :
    F.lt (dist F (u (clusterIndex F hcluster k)) l)
      (AccumToSeq.invSuccRadius F k) := by
  cases k with
  | zero =>
      exact
        (Classical.choose_spec
          (hcluster (AccumToSeq.invSuccRadius F 0)
            (AccumToSeq.invSuccRadius_pos F 0) 0)).right
  | succ k =>
      exact
        (Classical.choose_spec
          (hcluster (AccumToSeq.invSuccRadius F (k + 1))
            (AccumToSeq.invSuccRadius_pos F (k + 1))
            (clusterIndex F hcluster k + 1))).right

/-- The extracted subsequence converges to the cluster point. The
inverse-natural Archimedean principle enters here, exactly as in
`AccumToSeq.closeSubsequence_tendsto`: the radii eventually sit below any
given `eps`, and each term was chosen inside its own. -/
theorem clusterSubsequence_tendsto
    (hinvNat : F.InvNatArchimedeanPrinciple)
    {u : Nat -> alpha} {l : alpha}
    (hcluster : SeqClusterAt F u l) :
    SeqTendsto F (subsequence u (clusterIndex F hcluster)) l := by
  intro eps heps
  cases hinvNat.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hclose :
          F.lt (dist F (u (clusterIndex F hcluster n)) l)
            (AccumToSeq.invSuccRadius F n) :=
        clusterIndex_close F hcluster n
      have hradius_le :
          F.le (AccumToSeq.invSuccRadius F n)
            (AccumToSeq.invSuccRadius F N) :=
        AccumToSeq.invSuccRadius_antitone F hn
      have hlt_eps :
          F.lt (AccumToSeq.invSuccRadius F n) eps :=
        lt_of_le_of_lt F hradius_le hN
      dsimp [subsequence, dist]
      exact lt_trans F hclose hlt_eps

/-- The edge as a principle, assembled from its two halves: compactness
produces a cluster point of the bounded sequence, and the Archimedean
squeeze turns the cluster point into a convergent subsequence. -/
theorem sequentialPrinciple
    (hinvNat : F.InvNatArchimedeanPrinciple)
    (hcompact : ClosedIntervalCompactnessPrinciple.{max v 1} F) :
    BolzanoWeierstrassSequentialPrinciple F where
  convergent_subsequence := by
    intro u hbdd
    cases cluster_exists_from_compactness F hcompact hbdd with
    | intro l hcluster =>
        refine Exists.intro l ?_
        refine Exists.intro (clusterIndex F hcluster) ?_
        constructor
        · exact clusterIndex_subsequence F hcluster
        · exact clusterSubsequence_tendsto F hinvNat hcluster

/-- The exported edge `FiniteSubcoverToBWSequential`, with both its extra
hypotheses -- the inverse-natural Archimedean principle and compactness at
the lifted universe `max v 1`. `Routes.pureBridge` forwards to it. -/
theorem target : Target.{v} F := by
  intro hinvNat hcompact
  exact sequentialPrinciple F hinvNat hcompact

end FiniteToSeq
end Compactness
end IsOrderedFieldBaseLike
end Tautology
