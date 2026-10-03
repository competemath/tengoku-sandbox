import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealBootstrap.Lattice
import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Edge: nested intervals give the Cauchy criterion

The most expensive edge of the completeness graph -- thirty-nine declarations
against the four of `Tautology.RealSequence.Principles.FromMonotoneNested` --
and the size is the information. Turning a Cauchy sequence into a nested chain
means building the chain from scratch: a local max and min vocabulary, a radius
band around a late enough index, and running endpoints that tighten as the
index grows.

Its hypothesis is an `InvNatArchimedeanPrinciple`, used at one point only, to
drive the band widths to zero so that the chain has lengths tending to zero and
the nested principle returns a genuine limit.

## Position and role

Edge module of the completeness route graph, exporting `cauchyCriterion`. The
graph is assembled in `Tautology.RealSequence.Principles.Routes`; this edge is
not on the path chosen by `Tautology.RealSequence.Principles.Selected`, which
reaches the Cauchy criterion through monotone convergence instead -- a route
that needs no Archimedean hypothesis at that step and eight declarations rather
than thirty-nine.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

namespace FromNestedCauchy

/-- The pointwise maximum, `RealBootstrap.Lattice.max2` under the short name
the recursive definitions below are written with. The six order facts that
follow restate the lattice lemmas under the same short names. -/
noncomputable def max (x y : alpha) : alpha :=
  max2 F x y

/-- The pointwise minimum, the mirror of `max`: `RealBootstrap.Lattice.min2`
under the name the band construction recurses with. -/
noncomputable def min (x y : alpha) : alpha :=
  min2 F x y

theorem le_max_left (x y : alpha) :
    F.le x (max F x y) :=
  le_max2_left F x y

theorem le_max_right (x y : alpha) :
    F.le y (max F x y) :=
  le_max2_right F x y

theorem max_le {x y z : alpha}
    (hx : F.le x z) (hy : F.le y z) :
    F.le (max F x y) z :=
  max2_le F hx hy

theorem min_le_left (x y : alpha) :
    F.le (min F x y) x :=
  min2_le_left F x y

theorem min_le_right (x y : alpha) :
    F.le (min F x y) y :=
  min2_le_right F x y

theorem le_min {x y z : alpha}
    (hx : F.le z x) (hy : F.le z y) :
    F.le z (min F x y) :=
  le_min2 F hx hy

/-- The working tolerance at stage `k`: one half of the reciprocal
`1 / (k + 1)`. The factor one half is what makes the band built on this
radius exactly `1 / (k + 1)` wide (`band_length`), the quantity the
inverse-natural Archimedean principle eventually forces below any given
bound. -/
def radius (k : Nat) : alpha :=
  half F (F.inv (nat F (k + 1)))

theorem radius_pos (k : Nat) :
    F.lt F.zero (radius F k) := by
  unfold radius
  exact half_pos F
    (inv_pos F (nat_succ_pos F k))

/-- The stage-`k` threshold of the Cauchy sequence `u`: the index chosen
from the Cauchy property at tolerance `radius F k`. Chosen classically, so
nothing is known about it beyond `cauchyIndex_spec`. -/
noncomputable def cauchyIndex {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) : Nat :=
  Classical.choose (hu (radius F k) (radius_pos F k))

/-- The specification of the chosen threshold: past it, any two terms of `u`
differ by less than the stage's radius. This is the raw Cauchy property,
repackaged as everything the band construction may use. -/
theorem cauchyIndex_spec {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    forall n m : Nat,
      cauchyIndex F hu k <= n ->
        cauchyIndex F hu k <= m ->
          F.lt (abs F (F.sub (u n) (u m))) (radius F k) :=
  Classical.choose_spec (hu (radius F k) (radius_pos F k))

/-- The lower wall of the stage-`k` band: the anchor term
`u (cauchyIndex F hu k)` shifted down by the radius. -/
noncomputable def bandLower {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) : alpha :=
  F.sub (u (cauchyIndex F hu k)) (radius F k)

/-- The upper wall of the stage-`k` band: the same anchor term shifted up
by the radius. -/
noncomputable def bandUpper {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) : alpha :=
  F.add (u (cauchyIndex F hu k)) (radius F k)

/-- Past the stage-`k` threshold every term of `u` lies between that band's
walls, the per-stage form of tail containment before the running endpoints
merge the stages. -/
theorem band_tail_mem {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k n : Nat)
    (hn : cauchyIndex F hu k <= n) :
    And
      (F.le (bandLower F hu k) (u n))
      (F.le (u n) (bandUpper F hu k)) := by
  have hclose :=
    cauchyIndex_spec F hu k n (cauchyIndex F hu k) hn
      (Nat.le_refl (cauchyIndex F hu k))
  constructor
  · exact le_of_lt F (abs_sub_lt_left F hclose)
  · exact le_of_lt F (abs_sub_lt_right F hclose)

/-- The left endpoint at stage `k`: the running maximum of the band lower
walls up to `k`. Taking maxima is what makes these endpoints increase, one
of the two monotonicity halves of nesting. -/
noncomputable def lower {u : Nat -> alpha}
    (hu : F.SeqCauchy u) : Nat -> alpha
  | 0 => bandLower F hu 0
  | k + 1 => max F (lower hu k) (bandLower F hu (k + 1))

/-- The right endpoint at stage `k`: the running minimum of the band upper
walls up to `k`, the antitone half of nesting. -/
noncomputable def upper {u : Nat -> alpha}
    (hu : F.SeqCauchy u) : Nat -> alpha
  | 0 => bandUpper F hu 0
  | k + 1 => min F (upper hu k) (bandUpper F hu (k + 1))

/-- The largest stage threshold up to `k`: an index beyond which the terms
of `u` lie in every band at once. The convergence argument starts from this
index. -/
noncomputable def tailIndex {u : Nat -> alpha}
    (hu : F.SeqCauchy u) : Nat -> Nat
  | 0 => cauchyIndex F hu 0
  | k + 1 => Nat.max (tailIndex hu k) (cauchyIndex F hu (k + 1))

theorem lower_zero {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    lower F hu 0 = bandLower F hu 0 :=
  rfl

theorem upper_zero {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    upper F hu 0 = bandUpper F hu 0 :=
  rfl

theorem lower_succ {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    lower F hu (k + 1) =
      max F (lower F hu k) (bandLower F hu (k + 1)) :=
  rfl

theorem upper_succ {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    upper F hu (k + 1) =
      min F (upper F hu k) (bandUpper F hu (k + 1)) :=
  rfl

/-- Past `tailIndex F hu k` every term of `u` lies between the stage-`k`
running endpoints. Merging the per-stage containments under one running
index is what lets a single threshold serve all bands up to `k`. -/
theorem tail_mem_interval {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    forall k : Nat,
      forall n : Nat,
        tailIndex F hu k <= n ->
          And
            (F.le (lower F hu k) (u n))
            (F.le (u n) (upper F hu k)) := by
  intro k
  induction k with
  | zero =>
      intro n hn
      exact band_tail_mem F hu 0 n hn
  | succ k ih =>
      intro n hn
      have htail_prev : tailIndex F hu k <= n :=
        Nat.le_trans (Nat.le_max_left (tailIndex F hu k)
          (cauchyIndex F hu (k + 1))) hn
      have htail_band : cauchyIndex F hu (k + 1) <= n :=
        Nat.le_trans (Nat.le_max_right (tailIndex F hu k)
          (cauchyIndex F hu (k + 1))) hn
      have hprev := ih n htail_prev
      have hband := band_tail_mem F hu (k + 1) n htail_band
      constructor
      · rw [lower_succ]
        exact max_le F hprev.left hband.left
      · rw [upper_succ]
        exact le_min F hprev.right hband.right

/-- The stage-`k` interval is genuinely ordered, witnessed by any term
beyond `tailIndex F hu k`: the running endpoints bracket actual terms of
the sequence. -/
theorem interval_order {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (lower F hu k) (upper F hu k) := by
  have hmem := tail_mem_interval F hu k (tailIndex F hu k)
    (Nat.le_refl (tailIndex F hu k))
  exact F.le_trans hmem.left hmem.right

theorem lower_step_le {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (lower F hu k) (lower F hu (k + 1)) := by
  rw [lower_succ]
  exact le_max_left F (lower F hu k) (bandLower F hu (k + 1))

theorem upper_step_le {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (upper F hu (k + 1)) (upper F hu k) := by
  rw [upper_succ]
  exact min_le_left F (upper F hu k) (bandUpper F hu (k + 1))

/-- The left endpoints increase with the stage, one of the monotonicity
clauses `NestedClosedIntervals` demands, by induction along `n <= m` from
the one-step behaviour of the running maximum. -/
theorem lower_mono {u : Nat -> alpha}
    (hu : F.SeqCauchy u) {n m : Nat} (hnm : n <= m) :
    F.le (lower F hu n) (lower F hu m) := by
  induction hnm with
  | refl =>
      exact F.le_refl (lower F hu n)
  | step h ih =>
      exact F.le_trans ih (lower_step_le F hu _)

/-- The right endpoints decrease with the stage, the other monotonicity
clause of nesting, by the same induction along `n <= m`. -/
theorem upper_antitone {u : Nat -> alpha}
    (hu : F.SeqCauchy u) {n m : Nat} (hnm : n <= m) :
    F.le (upper F hu m) (upper F hu n) := by
  induction hnm with
  | refl =>
      exact F.le_refl (upper F hu n)
  | step h ih =>
      exact F.le_trans (upper_step_le F hu _) ih

theorem bandLower_le_lower {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (bandLower F hu k) (lower F hu k) := by
  induction k with
  | zero =>
      rw [lower_zero]
      exact F.le_refl (bandLower F hu 0)
  | succ k ih =>
      rw [lower_succ]
      exact le_max_right F (lower F hu k) (bandLower F hu (k + 1))

theorem upper_le_bandUpper {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (upper F hu k) (bandUpper F hu k) := by
  induction k with
  | zero =>
      rw [upper_zero]
      exact F.le_refl (bandUpper F hu 0)
  | succ k ih =>
      rw [upper_succ]
      exact min_le_right F (upper F hu k) (bandUpper F hu (k + 1))

/-- The stage-`k` band is exactly `1 / (k + 1)` wide: the anchor term
cancels and the two radii reassemble into the reciprocal. This is where
taking the radius as one half of the reciprocal pays off. -/
theorem band_length {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.sub (bandUpper F hu k) (bandLower F hu k) =
      F.inv (nat F (k + 1)) := by
  let c := u (cauchyIndex F hu k)
  let r := radius F k
  have hrr : F.add r r = F.inv (nat F (k + 1)) := by
    unfold r radius
    exact half_add_half F (F.inv (nat F (k + 1)))
  have hmain :
      F.sub (F.add c r) (F.sub c r) = F.add r r := by
    have hright :
        F.add (F.add r r) (F.sub c r) = F.add c r := by
      calc
        F.add (F.add r r) (F.sub c r) =
            F.add r (F.add r (F.sub c r)) := by
              rw [F.add_assoc]
        _ = F.add r (F.add (F.sub c r) r) := by
              rw [F.add_comm r (F.sub c r)]
        _ = F.add r c := by
              rw [sub_add_cancel F c r]
        _ = F.add c r := by rw [F.add_comm r c]
    apply add_right_cancel F (a := F.sub c r)
    calc
      F.add (F.sub (F.add c r) (F.sub c r)) (F.sub c r) =
          F.add c r := sub_add_cancel F (F.add c r) (F.sub c r)
      _ = F.add (F.add r r) (F.sub c r) := hright.symm
  unfold bandUpper bandLower
  change F.sub (F.add c r) (F.sub c r) = F.inv (nat F (k + 1))
  rw [hmain, hrr]

/-- The width of the stage-`k` interval between the running endpoints, the
quantity the nesting argument has to drive to zero. -/
noncomputable def length {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) : alpha :=
  F.sub (upper F hu k) (lower F hu k)

/-- The constructed interval is no wider than the stage's band: the running
maximum sits above the band's lower wall and the running minimum below its
upper wall. -/
theorem length_le_band_length {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le (length F hu k)
      (F.sub (bandUpper F hu k) (bandLower F hu k)) := by
  unfold length
  exact sub_le_sub_of_le_of_le F
    (upper_le_bandUpper F hu k)
    (bandLower_le_lower F hu k)

theorem length_nonneg {u : Nat -> alpha}
    (hu : F.SeqCauchy u) (k : Nat) :
    F.le F.zero (length F hu k) := by
  unfold length
  exact sub_nonneg_of_le F (interval_order F hu k)

/-- The running endpoints form a nested family of closed intervals in the
vocabulary of the nested node. This is the first of the two inputs the node
is applied to, the second being the vanishing of lengths. -/
theorem nested_intervals {u : Nat -> alpha}
    (hu : F.SeqCauchy u) :
    F.NestedClosedIntervals (lower F hu) (upper F hu) := by
  constructor
  · exact interval_order F hu
  · constructor
    · intro n m hnm
      exact lower_mono F hu hnm
    · intro n m hnm
      exact upper_antitone F hu hnm

/-- Under the inverse-natural Archimedean principle the interval widths tend
to zero: widths only shrink as stages advance, and the stage-`N` interval
is at most `1 / (N + 1)` wide, which that principle forces below any given
bound. This is the single place where the edge's Archimedean hypothesis
enters. -/
theorem length_tendsto_zero {u : Nat -> alpha}
    (hu : F.SeqCauchy u)
    (hinvNat : F.InvNatArchimedeanPrinciple) :
    F.IntervalLengthsToZero (lower F hu) (upper F hu) := by
  intro eps heps
  cases hinvNat.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hlen_le_N :
          F.le (length F hu n) (length F hu N) := by
        unfold length
        exact sub_le_sub_of_le_of_le F
          (upper_antitone F hu hn)
          (lower_mono F hu hn)
      have hlenN_le_inv :
          F.le (length F hu N) (F.inv (nat F (N + 1))) := by
        have h := length_le_band_length F hu N
        rwa [band_length F hu N] at h
      have hlen_lt : F.lt (length F hu n) eps :=
        lt_of_le_of_lt F
          (F.le_trans hlen_le_N hlenN_le_inv) hN
      have hnonneg := length_nonneg F hu n
      change
        F.lt (abs F (F.sub (length F hu n) F.zero)) eps
      rwa [sub_zero F (length F hu n), abs_of_nonneg F hnonneg]

theorem interval_points_close {a b x y eps : alpha}
    (hx : And (F.le a x) (F.le x b))
    (hy : And (F.le a y) (F.le y b))
    (hlen : F.lt (F.sub b a) eps) :
    F.lt (abs F (F.sub x y)) eps :=
  NestedBasic.interval_points_close F hx hy hlen

/-- Any point common to all the constructed intervals is the limit of `u`:
past the stage-`K` tail index the terms and the point share an interval
whose width is below `eps`. -/
theorem tendsto_nested_point {u : Nat -> alpha} {l : alpha}
    (hu : F.SeqCauchy u)
    (hinvNat : F.InvNatArchimedeanPrinciple)
    (hl :
      forall n : Nat,
        And (F.le (lower F hu n) l) (F.le l (upper F hu n))) :
    F.SeqTendsto u l := by
  intro eps heps
  have hlen := length_tendsto_zero F hu hinvNat eps heps
  cases hlen with
  | intro K hK =>
      refine Exists.intro (tailIndex F hu K) ?_
      intro n hn
      have htail := tail_mem_interval F hu K n hn
      have hlenK_close := hK K (Nat.le_refl K)
      have hlenK : F.lt (length F hu K) eps := by
        have hnonneg := length_nonneg F hu K
        change
          F.lt (abs F (F.sub (length F hu K) F.zero)) eps
          at hlenK_close
        rwa [sub_zero F (length F hu K), abs_of_nonneg F hnonneg]
          at hlenK_close
      exact interval_points_close F htail (hl K) hlenK

/-- The edge from the nested-interval node to the Cauchy node, with the
inverse-natural Archimedean principle as its price. The proof wraps a
Cauchy sequence in the family of running bands and hands the node that
family together with its vanishing widths; the common point is drawn from
the node's uniqueness clause, whose membership half is all the convergence
argument reads. The Archimedean hypothesis is consumed once, in
`length_tendsto_zero`, and without some such principle the reciprocals
`1 / (k + 1)` need not form a null sequence. -/
theorem cauchyCriterion
    (hnested : F.NestedIntervalPrinciple)
    (hinvNat : F.InvNatArchimedeanPrinciple) :
    F.CauchyCriterionPrinciple where
  converges := by
    intro u hu
    have hnest : F.NestedClosedIntervals (lower F hu) (upper F hu) :=
      nested_intervals F hu
    have hlen : F.IntervalLengthsToZero (lower F hu) (upper F hu) :=
      length_tendsto_zero F hu hinvNat
    cases hnested.unique_point_of_lengths_zero
        (lower F hu) (upper F hu) hnest hlen with
    | intro l hl =>
        exact Exists.intro l
          (tendsto_nested_point F hu hinvNat hl.left)

end FromNestedCauchy
end IsOrderedFieldBaseLike
end Tautology
