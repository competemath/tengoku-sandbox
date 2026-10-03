import Tengoku.Tautology.Tautology.RealTopology.ClosureAlgebra
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealBootstrap.Lattice

/-!
# Closure by sequences, and the Archimedean boundary

The sequential face of the topology: a point lies in the closure of `S` exactly
when some sequence in `S` converges to it, and a set is closed exactly when it
contains the limit of every convergent sequence drawn from it. The witness is
`closureApproachSeq`, which picks at step `n` a point of `S` inside the
interval of radius `1 / (n + 1)` around the point.

## Where the hypothesis comes from

This module is the one place in `RealTopology` where reading "namespace switch
marks the use of completeness" gives the wrong answer. Everything here stays in
`namespace IsOrderedFieldBaseLike`, yet the direction that builds a sequence
needs to know that `1 / (n + 1)` eventually drops below any positive bound.
That is an Archimedean fact, and the module takes it as an explicit hypothesis
`(A : F.InvNatArchimedeanPrinciple)` instead of deriving it or moving to the
complete-field namespace. So the region carries two independent boundaries:
completeness, marked by namespace, in `Tautology.RealTopology.RationalBasis`
and `Tautology.RealTopology.Lindelof`; Archimedean, marked by hypothesis, here.

The opposite direction is free of hypotheses: a convergent sequence eventually
enters any open set containing its limit, with the tolerance read off the
endpoints of the interval witness.

## Position and role

Implementation module, built on `Tautology.RealTopology.ClosureAlgebra` and the
sequence vocabulary of `RealSequence`. `Tautology.RealTopology.IntervalClosure`
continues from here.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem add_sub_right (x y : alpha) :
    F.add x (F.sub y x) = y := by
  rw [F.add_comm x (F.sub y x)]
  exact sub_add_cancel F y x

/-- A sequence converging to `x` is eventually inside every open set
containing `x`. This is the bridge from the epsilon-delta definition of
`SeqTendsto` to the open-set language of this region: the tolerance is the
smaller of the two distances from `x` to the endpoints of the interval
witnessing openness. -/
theorem seqTendsto_eventually_mem_open
    {u : Nat -> alpha} {x : alpha} {U : alpha -> Prop}
    (hu : SeqTendsto F u x)
    (hUopen : IsOpen F U)
    (hxU : U x) :
    Eventually (fun n : Nat => U (u n)) := by
  cases hUopen x hxU with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          let dl := F.sub x left
          let dr := F.sub right x
          let eps := min2 F dl dr
          have hdl : F.lt F.zero dl := by
            unfold dl
            exact sub_pos_of_lt F hright.left
          have hdr : F.lt F.zero dr := by
            unfold dr
            exact sub_pos_of_lt F hright.right.left
          have heps : F.lt F.zero eps := min2_pos F hdl hdr
          have hevent := hu eps heps
          apply Eventually.mono ?_ hevent
          intro n hn
          have hleft_close : F.lt (F.sub x eps) (u n) :=
            abs_sub_lt_left F hn
          have hright_close : F.lt (u n) (F.add x eps) :=
            abs_sub_lt_right F hn
          have heps_dl : F.le eps dl := min2_le_left F dl dr
          have heps_dr : F.le eps dr := min2_le_right F dl dr
          have hleft_le :
              F.le left (F.sub x eps) := by
            have hsub :
                F.le (F.sub x dl) (F.sub x eps) :=
              sub_le_sub_of_le_of_le F (F.le_refl x) heps_dl
            rwa [show F.sub x dl = left by
              unfold dl
              exact sub_self_sub F x left] at hsub
          have hright_le :
              F.le (F.add x eps) right := by
            have hadd : F.le (F.add x eps) (F.add x dr) :=
              add_le_add_left F heps_dr x
            rwa [show F.add x dr = right by
              unfold dr
              exact add_sub_right F x right] at hadd
          exact hright.right.right (u n)
            (And.intro
              (lt_of_le_of_lt F hleft_le hleft_close)
              (lt_of_lt_of_le F hright_close hright_le))

/-- The open-interval specialisation of `seqTendsto_eventually_mem_open`:
the terms eventually land in any open interval straddling the limit. This
plain form, with no openness hypothesis in sight, is what the sequential
compactness route and the Lee--Vyborny exceptional-set argument consume. -/
theorem point_in_open_interval_of_tendsto {u : Nat -> alpha}
    {l left right : alpha}
    (hlim : SeqTendsto F u l)
    (hleft : F.lt left l)
    (hright : F.lt l right) :
    Eventually (fun n : Nat => OpenInterval F left right (u n)) := by
  exact
    seqTendsto_eventually_mem_open F hlim
      (open_interval F left right)
      (And.intro hleft hright)

/-- The limit of a sequence taking values in `S` is a closure point of `S`.
This direction of the sequential characterisation uses nothing but the
ordered-field structure; only the converse needs the Archimedean
hypothesis. -/
theorem closurePoint_of_seqTendsto
    {S : alpha -> Prop} {u : Nat -> alpha} {x : alpha}
    (hS : forall n : Nat, S (u n))
    (hu : SeqTendsto F u x) :
    ClosurePoint F S x := by
  intro U hUopen hxU
  cases seqTendsto_eventually_mem_open F hu hUopen hxU with
  | intro N hN =>
      exact Exists.intro (u N)
        (And.intro (hS N) (hN N (Nat.le_refl N)))

/-- A sequence in `S` aimed at a closure point `x` of `S`: stage `n` picks,
by classical choice, a point of `S` inside the open interval of radius
`1 / (n + 1)` about `x`. The closure condition is exactly what guarantees
such a point exists at every stage. -/
noncomputable def closureApproachSeq
    {S : alpha -> Prop} {x : alpha}
    (hx : ClosurePoint F S x) : Nat -> alpha := by
  classical
  exact fun n : Nat =>
    let r := F.inv (nat F (n + 1))
    let U := OpenInterval F (F.sub x r) (F.add x r)
    Classical.choose
      (hx U
        (open_interval F (F.sub x r) (F.add x r))
        (And.intro
          (sub_lt_self_of_pos F (inv_pos F (nat_succ_pos F n)))
          (lt_add_of_pos F (inv_pos F (nat_succ_pos F n)))))

/-- What `closureApproachSeq` returns at stage `n`: a point of `S`, sitting
inside the radius-`1 / (n + 1)` interval about `x` that the stage was asked
to hit. -/
theorem closureApproachSeq_spec
    {S : alpha -> Prop} {x : alpha}
    (hx : ClosurePoint F S x)
    (n : Nat) :
    And (S (closureApproachSeq F hx n))
      (OpenInterval F
        (F.sub x (F.inv (nat F (n + 1))))
        (F.add x (F.inv (nat F (n + 1))))
        (closureApproachSeq F hx n)) := by
  unfold closureApproachSeq
  exact
    Classical.choose_spec
      (hx
        (OpenInterval F
          (F.sub x (F.inv (nat F (n + 1))))
          (F.add x (F.inv (nat F (n + 1)))))
        (open_interval F
          (F.sub x (F.inv (nat F (n + 1))))
          (F.add x (F.inv (nat F (n + 1)))))
        (And.intro
          (sub_lt_self_of_pos F (inv_pos F (nat_succ_pos F n)))
          (lt_add_of_pos F (inv_pos F (nat_succ_pos F n)))))

/-- The approach sequence converges to `x`. This is the one step in the file
that needs more than the ordered-field structure: the hypothesis `A` says
inverses of naturals eventually fall below any given `eps`, so the radii
`1 / (n + 1)` eventually do. -/
theorem closureApproachSeq_tendsto
    {S : alpha -> Prop} {x : alpha}
    (A : F.InvNatArchimedeanPrinciple)
    (hx : ClosurePoint F S x) :
    SeqTendsto F (closureApproachSeq F hx) x := by
  intro eps heps
  cases A.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      let rn := F.inv (nat F (n + 1))
      have hNn :
          F.le (nat F (N + 1)) (nat F (n + 1)) :=
        nat_le_nat_of_le F (Nat.succ_le_succ hn)
      have hrn_le :
          F.le rn (F.inv (nat F (N + 1))) := by
        unfold rn
        exact inv_le_inv_of_le_pos F
          (nat_succ_pos F N) (nat_succ_pos F n) hNn
      have hrn_lt_eps : F.lt rn eps :=
        lt_of_le_of_lt F hrn_le hN
      have hspec := closureApproachSeq_spec F hx n
      have hleft_le :
          F.le (F.sub x eps) (F.sub x rn) :=
        sub_le_sub_of_le_of_le F
          (F.le_refl x) (le_of_lt F hrn_lt_eps)
      have hright_le :
          F.le (F.add x rn) (F.add x eps) :=
        add_le_add_left F (le_of_lt F hrn_lt_eps) x
      exact abs_sub_lt_of_bounds F
        (lt_of_le_of_lt F hleft_le hspec.right.left)
        (lt_of_lt_of_le F hspec.right.right hright_le)

/-- Every closure point of `S` is the limit of some sequence taking values
in `S` -- the converse direction of the sequential characterisation, again
under the Archimedean hypothesis, with `closureApproachSeq` as the
witness sequence. -/
theorem exists_seqTendsto_of_closurePoint
    {S : alpha -> Prop} {x : alpha}
    (A : F.InvNatArchimedeanPrinciple)
    (hx : ClosurePoint F S x) :
    Exists
      (fun u : Nat -> alpha =>
        And (forall n : Nat, S (u n)) (SeqTendsto F u x)) :=
  Exists.intro (closureApproachSeq F hx)
    (And.intro
      (fun n => (closureApproachSeq_spec F hx n).left)
      (closureApproachSeq_tendsto F A hx))

/-- Closure points of `S` are exactly the limits of sequences from `S`.
Stated for any ordered field carrying `F.InvNatArchimedeanPrinciple`;
Dedekind completeness never enters, the Archimedean hypothesis is all the
converse direction uses. -/
theorem closurePoint_iff_exists_seqTendsto
    {S : alpha -> Prop} {x : alpha}
    (A : F.InvNatArchimedeanPrinciple) :
    ClosurePoint F S x <->
      Exists
        (fun u : Nat -> alpha =>
          And (forall n : Nat, S (u n)) (SeqTendsto F u x)) := by
  constructor
  · intro hx
    exact exists_seqTendsto_of_closurePoint F A hx
  · intro hx
    cases hx with
    | intro u hu =>
        exact closurePoint_of_seqTendsto F hu.left hu.right

/-- A closed set contains the limits of all its sequences. Needs no
Archimedean hypothesis: it composes the hypothesis-free direction
`closurePoint_of_seqTendsto` with `closure_subset_of_closed`. -/
theorem mem_of_closed_of_seqTendsto
    {S : alpha -> Prop} {u : Nat -> alpha} {x : alpha}
    (hclosed : IsClosed F S)
    (hS : forall n : Nat, S (u n))
    (hu : SeqTendsto F u x) :
    S x :=
  closure_subset_of_closed F hclosed x
    (closurePoint_of_seqTendsto F hS hu)

/-- Closed sets are exactly the sequentially closed ones. The direction from
closedness to sequential closedness is hypothesis-free; the other direction
goes through `exists_seqTendsto_of_closurePoint` and therefore needs the
Archimedean principle `A`. -/
theorem closed_iff_seq_limits
    {S : alpha -> Prop}
    (A : F.InvNatArchimedeanPrinciple) :
    IsClosed F S <->
      forall u : Nat -> alpha,
        forall x : alpha,
          (forall n : Nat, S (u n)) ->
            SeqTendsto F u x -> S x := by
  constructor
  · intro hclosed u x hS hu
    exact mem_of_closed_of_seqTendsto F hclosed hS hu
  · intro hseq
    apply closed_of_closure_subset F
    intro x hx
    cases exists_seqTendsto_of_closurePoint F A hx with
    | intro u hu =>
        exact hseq u x hu.left hu.right

end IsOrderedFieldBaseLike
end Tautology
