import Tengoku.Tautology.Tautology.RealSequence.Subsequence
import Tengoku.Tautology.Tautology.RealSequence.Limsup.CompleteCore
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean

/-!
# Upper and lower limits, as predicates

The characterisation half of the upper and lower limits, and the file is
organised so that almost all of it stays at ordered-field level. `IsLimsup` and
`IsLiminf` are epsilon-characterisations, not references to a constructed
value, so the comparison and arithmetic results -- extremality, the sum and
difference inequalities, the mixed liminf-limsup ones -- can be proved without
any completeness at all.

Completeness appears only at the end, in the bridge theorems that say the
values built in `Tautology.RealSequence.Limsup.CompleteCore` satisfy those
predicates, and in the two packaged statements identifying limsup and liminf as
the largest and smallest cluster values.

An Archimedean hypothesis enters at one place, and asymmetrically: that a
cluster value is at most the upper limit needs nothing, while producing a
subsequence converging to the upper limit needs radii `1 / (k + 1)` to reach
zero. The ordered-field versions take that hypothesis explicitly; the
complete-field versions discharge it from the bundle.

## Position and role

Implementation module, sitting on `Tautology.RealSequence.Limsup.CompleteCore`
for the values and on the sequence vocabulary below it for everything else. The
habit of treating limsup as an interface, touching the constructed value only
at the last moment, is what keeps the boundary visible.
-/

namespace Tautology

/-- `P` holds arbitrarily far out: past every cutoff `N` there is an `n` with
`N <= n` and `P n`. The dual of the `Eventually` of `Tautology.Nat.Eventually`,
with the inner universal quantifier flipped to an existential; the limsup and
liminf predicates below each pair one `Eventually` clause with one `Frequently`
clause. -/
def Frequently (P : Nat -> Prop) : Prop :=
  forall N : Nat, Exists (fun n : Nat => And (N <= n) (P n))

namespace Frequently

theorem mono {P Q : Nat -> Prop}
    (hPQ : forall n : Nat, P n -> Q n)
    (hP : Frequently P) :
    Frequently Q := by
  intro N
  cases hP N with
  | intro n hn =>
      exact Exists.intro n (And.intro hn.left (hPQ n hn.right))

end Frequently

namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- `x` is a cluster value of `u`: some strictly increasing reindexing, in the
`SubsequenceIndex` sense of `Tautology.RealSequence.Subsequence`, makes the
reindexed sequence converge to `x`, convergence being `SeqTendsto` of
`Tautology.RealSequence.Basic`. A predicate over an arbitrary ordered field,
asserting membership rather than existence; producing cluster values is the
business of the Archimedean theorem and the Dedekind-complete layer at the end
of this module. -/
def SeqClusterValue (u : Nat -> alpha) (x : alpha) : Prop :=
  Exists
    (fun phi : Nat -> Nat =>
      And (SubsequenceIndex phi)
        (SeqTendsto F (subsequence u phi) x))

/-- `L` is a limit superior of `u`, as a predicate in the epsilonic style:
eventually `u n` lies strictly below `L + eps`, and at arbitrarily large
indices it climbs strictly above `L - eps`. Deliberately stated without
constructing anything, so that it makes sense over any ordered field, where
at most one value can satisfy it; existence is supplied only where the tail
suprema exist, by `limsup_isLimsup` at the end of this module. -/
def IsLimsup (u : Nat -> alpha) (L : alpha) : Prop :=
  And
    (forall eps : alpha,
      F.lt F.zero eps ->
        Eventually (fun n : Nat => F.lt (u n) (F.add L eps)))
    (forall eps : alpha,
      F.lt F.zero eps ->
        Frequently (fun n : Nat => F.lt (F.sub L eps) (u n)))

/-- `l` is a limit inferior of `u`: eventually `u n` lies strictly above
`l - eps`, and at arbitrarily large indices it dips strictly below `l + eps`.
The exact mirror of `IsLimsup`, the mirroring being made formal by
`limsup_neg_of_liminf` and `liminf_neg_of_limsup` below. -/
def IsLiminf (u : Nat -> alpha) (l : alpha) : Prop :=
  And
    (forall eps : alpha,
      F.lt F.zero eps ->
        Eventually (fun n : Nat => F.lt (F.sub l eps) (u n)))
    (forall eps : alpha,
      F.lt F.zero eps ->
        Frequently (fun n : Nat => F.lt (u n) (F.add l eps)))

theorem eventually_subsequence_of_eventually
    {P : Nat -> Prop} {phi : Nat -> Nat}
    (hphi : SubsequenceIndex phi)
    (hP : Eventually P) :
    Eventually (fun k : Nat => P (phi k)) := by
  cases hP with
  | intro N hN =>
      refine Exists.intro N ?_
      intro k hk
      have hkphi : k <= phi k :=
        subsequenceIndex_ge_self hphi k
      exact hN (phi k) (Nat.le_trans hk hkphi)

/-- If `x <= y + eps` for every positive `eps`, then `x <= y`. The
positive-epsilon dichotomy for an ordered field, proved by testing
`eps = (x - y) / 2` and contradicting strictness; no completeness or
Archimedean assumption enters. -/
theorem le_of_forall_pos_le_add {x y : alpha}
    (h : forall eps : alpha,
      F.lt F.zero eps -> F.le x (F.add y eps)) :
    F.le x y := by
  by_cases hxy : F.le x y
  · exact hxy
  · have hyx : F.le y x := by
      cases F.le_total y x with
      | inl hle => exact hle
      | inr hle => exact False.elim (hxy hle)
    have hyx_lt : F.lt y x :=
      lt_of_le_of_not_le F hyx hxy
    let eps := half F (F.sub x y)
    have hgap : F.lt F.zero (F.sub x y) :=
      sub_pos_of_lt F hyx_lt
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    have hx_le : F.le x (F.add y eps) := h eps heps
    have hy_eps_lt_x : F.lt (F.add y eps) x := by
      have hhalf : F.lt eps (F.sub x y) :=
        half_lt_self F hgap
      have h := add_lt_add_right F hhalf y
      rwa [F.add_comm eps y, sub_add_cancel F x y] at h
    exact False.elim ((not_le_of_lt F hy_eps_lt_x) hx_le)

theorem le_of_forall_pos_sub_le {x y : alpha}
    (h : forall eps : alpha,
      F.lt F.zero eps -> F.le (F.sub x eps) y) :
    F.le x y := by
  apply le_of_forall_pos_le_add F
  intro eps heps
  have h' := F.add_le_add_right (h eps heps) eps
  rw [sub_add_cancel F x eps] at h'
  exact h'

/-- A limsup witness is below any eventual upper bound: if `u n < B + eps`
holds eventually for every positive `eps`, then `L <= B`. This is the
closure property that makes the limsup the least eventual upper bound, and
every inequality of this module about sums and differences is routed through
it. -/
theorem limsup_le_of_eventually_lt_add
    {u : Nat -> alpha} {L B : alpha}
    (hL : IsLimsup F u L)
    (hB :
      forall eps : alpha,
        F.lt F.zero eps ->
          Eventually (fun n : Nat => F.lt (u n) (F.add B eps))) :
    F.le L B := by
  by_cases hLB : F.le L B
  · exact hLB
  · have hBL_le : F.le B L := by
      cases F.le_total B L with
      | inl hle => exact hle
      | inr hle => exact False.elim (hLB hle)
    have hBL : F.lt B L :=
      lt_of_le_of_not_le F hBL_le hLB
    let eps := half F (F.sub L B)
    have hgap : F.lt F.zero (F.sub L B) :=
      sub_pos_of_lt F hBL
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    cases hB eps heps with
    | intro N hN =>
        cases hL.right eps heps N with
        | intro n hn =>
            exact False.elim
              (not_between_sub_add_half F hn.right (hN n hn.left))

/-- The companion closure property, from the `Frequently` clause: any
threshold that `u` crosses arbitrarily far out is below the limsup witness,
in the form `B <= L` whenever `B - eps < u n` frequently for every positive
`eps`. Paired with `limsup_le_of_eventually_lt_add` this squeezes `L`
between the eventual upper bounds and the frequent lower thresholds. -/
theorem le_limsup_of_frequently_sub_lt
    {u : Nat -> alpha} {L B : alpha}
    (hL : IsLimsup F u L)
    (hB :
      forall eps : alpha,
        F.lt F.zero eps ->
          Frequently (fun n : Nat => F.lt (F.sub B eps) (u n))) :
    F.le B L := by
  by_cases hBL : F.le B L
  · exact hBL
  · have hLB_le : F.le L B := by
      cases F.le_total L B with
      | inl hle => exact hle
      | inr hle => exact False.elim (hBL hle)
    have hLB : F.lt L B :=
      lt_of_le_of_not_le F hLB_le hBL
    let eps := half F (F.sub B L)
    have hgap : F.lt F.zero (F.sub B L) :=
      sub_pos_of_lt F hLB
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    cases hL.left eps heps with
    | intro N hN =>
        cases hB eps heps N with
        | intro n hn =>
            exact False.elim
              (not_between_sub_add_half F hn.right (hN n hn.left))

/-- The liminf counterpart of the eventual-bound closure: if `u n` stays
above `B - eps` eventually for every positive `eps`, then `B` is at most the
liminf witness -- the liminf is the greatest eventual lower bound. -/
theorem le_liminf_of_eventually_sub_lt
    {u : Nat -> alpha} {l B : alpha}
    (hl : IsLiminf F u l)
    (hB :
      forall eps : alpha,
        F.lt F.zero eps ->
          Eventually (fun n : Nat => F.lt (F.sub B eps) (u n))) :
    F.le B l := by
  by_cases hBl : F.le B l
  · exact hBl
  · have hlB_le : F.le l B := by
      cases F.le_total l B with
      | inl hle => exact hle
      | inr hle => exact False.elim (hBl hle)
    have hlB : F.lt l B :=
      lt_of_le_of_not_le F hlB_le hBl
    let eps := half F (F.sub B l)
    have hgap : F.lt F.zero (F.sub B l) :=
      sub_pos_of_lt F hlB
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    cases hB eps heps with
    | intro N hN =>
        cases hl.right eps heps N with
        | intro n hn =>
            exact False.elim
              (not_between_sub_add_half F (hN n hn.left) hn.right)

/-- The liminf counterpart of the frequent-threshold closure: if `u n`
crosses above `B + eps` arbitrarily far out for every positive `eps`, then
the liminf witness is at most `B`. -/
theorem liminf_le_of_frequently_lt_add
    {u : Nat -> alpha} {l B : alpha}
    (hl : IsLiminf F u l)
    (hB :
      forall eps : alpha,
        F.lt F.zero eps ->
          Frequently (fun n : Nat => F.lt (u n) (F.add B eps))) :
    F.le l B := by
  by_cases hlB : F.le l B
  · exact hlB
  · have hBl_le : F.le B l := by
      cases F.le_total B l with
      | inl hle => exact hle
      | inr hle => exact False.elim (hlB hle)
    have hBl : F.lt B l :=
      lt_of_le_of_not_le F hBl_le hlB
    let eps := half F (F.sub l B)
    have hgap : F.lt F.zero (F.sub l B) :=
      sub_pos_of_lt F hBl
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    cases hl.left eps heps with
    | intro N hN =>
        cases hB eps heps N with
        | intro n hn =>
            exact False.elim
              (not_between_sub_add_half F (hN n hn.left) hn.right)

theorem limsup_unique {u : Nat -> alpha} {L M : alpha}
    (hL : IsLimsup F u L)
    (hM : IsLimsup F u M) :
    L = M :=
  F.le_antisymm
    (limsup_le_of_eventually_lt_add F hL hM.left)
    (limsup_le_of_eventually_lt_add F hM hL.left)

theorem liminf_unique {u : Nat -> alpha} {l m : alpha}
    (hl : IsLiminf F u l)
    (hm : IsLiminf F u m) :
    l = m :=
  F.le_antisymm
    (le_liminf_of_eventually_sub_lt F hm hl.left)
    (le_liminf_of_eventually_sub_lt F hl hm.left)

theorem limsup_mono {u v : Nat -> alpha} {Lu Lv : alpha}
    (huv : Eventually (fun n : Nat => F.le (u n) (v n)))
    (hu : IsLimsup F u Lu)
    (hv : IsLimsup F v Lv) :
    F.le Lu Lv := by
  apply limsup_le_of_eventually_lt_add F hu
  intro eps heps
  exact Eventually.mono
    (fun n hn => lt_of_le_of_lt F hn.right hn.left)
    (Eventually.and (hv.left eps heps) huv)

theorem liminf_mono {u v : Nat -> alpha} {lu lv : alpha}
    (huv : Eventually (fun n : Nat => F.le (u n) (v n)))
    (hu : IsLiminf F u lu)
    (hv : IsLiminf F v lv) :
    F.le lu lv := by
  apply le_liminf_of_eventually_sub_lt F hv
  intro eps heps
  exact Eventually.mono
    (fun n hn => lt_of_lt_of_le F hn.left hn.right)
    (Eventually.and (hu.left eps heps) huv)

theorem isLimsup_congr {u v : Nat -> alpha} {L : alpha}
    (huv : forall n : Nat, u n = v n)
    (hu : IsLimsup F u L) :
    IsLimsup F v L := by
  constructor
  · intro eps heps
    apply Eventually.mono ?_ (hu.left eps heps)
    intro n hn
    rwa [<- huv n]
  · intro eps heps
    apply Frequently.mono ?_ (hu.right eps heps)
    intro n hn
    rwa [<- huv n]

theorem isLiminf_congr {u v : Nat -> alpha} {l : alpha}
    (huv : forall n : Nat, u n = v n)
    (hu : IsLiminf F u l) :
    IsLiminf F v l := by
  constructor
  · intro eps heps
    apply Eventually.mono ?_ (hu.left eps heps)
    intro n hn
    rwa [<- huv n]
  · intro eps heps
    apply Frequently.mono ?_ (hu.right eps heps)
    intro n hn
    rwa [<- huv n]

/-- Every cluster value of `u` lies below every limsup witness. Only the two
clauses of `IsLimsup` enter: the eventual upper bound squeezes the
subsequence, so this direction costs no Archimedean assumption. The
converse, that the limsup witness is itself a cluster value, is exactly what
requires one; see `limsup_clusterValue` below. -/
theorem cluster_le_limsup {u : Nat -> alpha} {x L : alpha}
    (hL : IsLimsup F u L)
    (hx : SeqClusterValue F u x) :
    F.le x L := by
  cases hx with
  | intro phi hphi =>
      by_cases hxL : F.le x L
      · exact hxL
      · have hLx_le : F.le L x := by
          cases F.le_total L x with
          | inl hle => exact hle
          | inr hle => exact False.elim (hxL hle)
        have hLx : F.lt L x :=
          lt_of_le_of_not_le F hLx_le hxL
        let eps := half F (F.sub x L)
        have hgap : F.lt F.zero (F.sub x L) :=
          sub_pos_of_lt F hLx
        have heps : F.lt F.zero eps :=
          half_pos F hgap
        have hupper :
            Eventually
              (fun k : Nat =>
                F.lt (u (phi k)) (F.add L eps)) :=
          eventually_subsequence_of_eventually hphi.left
            (hL.left eps heps)
        have hclose := hphi.right eps heps
        cases Eventually.and hupper hclose with
        | intro N hN =>
            have hN' := hN N (Nat.le_refl N)
            have hlow :
                F.lt (F.sub x eps) (u (phi N)) :=
              abs_sub_lt_left F hN'.right
            have hbad :
                F.lt (F.sub x eps) (F.add L eps) :=
              lt_trans F hlow hN'.left
            have heq :
                F.add L eps = F.sub x eps := by
              unfold eps
              exact add_half_sub_eq_sub_half F x L
            rw [heq] at hbad
            exact False.elim ((lt_irrefl F (F.sub x eps)) hbad)

/-- The mirror statement: every liminf witness lies below every cluster
value, again from the two clauses of `IsLiminf` alone, with no Archimedean
assumption on this direction. -/
theorem liminf_le_cluster {u : Nat -> alpha} {x l : alpha}
    (hl : IsLiminf F u l)
    (hx : SeqClusterValue F u x) :
    F.le l x := by
  cases hx with
  | intro phi hphi =>
      by_cases hlx : F.le l x
      · exact hlx
      · have hxl_le : F.le x l := by
          cases F.le_total x l with
          | inl hle => exact hle
          | inr hle => exact False.elim (hlx hle)
        have hxl : F.lt x l :=
          lt_of_le_of_not_le F hxl_le hlx
        let eps := half F (F.sub l x)
        have hgap : F.lt F.zero (F.sub l x) :=
          sub_pos_of_lt F hxl
        have heps : F.lt F.zero eps :=
          half_pos F hgap
        have hlower :
            Eventually
              (fun k : Nat =>
                F.lt (F.sub l eps) (u (phi k))) :=
          eventually_subsequence_of_eventually hphi.left
            (hl.left eps heps)
        have hclose := hphi.right eps heps
        cases Eventually.and hlower hclose with
        | intro N hN =>
            have hN' := hN N (Nat.le_refl N)
            have hhigh :
                F.lt (u (phi N)) (F.add x eps) :=
              abs_sub_lt_right F hN'.right
            have hbad :
                F.lt (F.sub l eps) (F.add x eps) :=
              lt_trans F hN'.left hhigh
            have heq :
                F.add x eps = F.sub l eps := by
              unfold eps
              exact add_half_sub_eq_sub_half F l x
            rw [heq] at hbad
            exact False.elim ((lt_irrefl F (F.sub l eps)) hbad)

/-- Two quantities that each overshoot by half of `eps` overshoot by `eps`
when added. This identity is the entire halving bookkeeping behind the four
addition inequalities below. -/
theorem add_add_halves (a b eps : alpha) :
    F.add (F.add a (half F eps)) (F.add b (half F eps)) =
      F.add (F.add a b) eps := by
  let h := half F eps
  change F.add (F.add a h) (F.add b h) =
      F.add (F.add a b) eps
  have hmid :
      F.add h (F.add b h) = F.add b (F.add h h) := by
    calc
      F.add h (F.add b h) =
          F.add (F.add h b) h := by rw [<- F.add_assoc]
      _ = F.add (F.add b h) h := by rw [F.add_comm h b]
      _ = F.add b (F.add h h) := by rw [F.add_assoc]
  calc
    F.add (F.add a h) (F.add b h) =
        F.add a (F.add h (F.add b h)) := by rw [F.add_assoc]
    _ = F.add a (F.add b (F.add h h)) := by rw [hmid]
    _ = F.add (F.add a b) (F.add h h) := by rw [<- F.add_assoc]
    _ = F.add (F.add a b) eps := by rw [half_add_half F eps]

/-- Two quantities that each undershoot by half of `eps` undershoot by `eps`
when added; the subtractive twin of `add_add_halves`, feeding the liminf and
mixed inequalities. -/
theorem add_sub_halves (a b eps : alpha) :
    F.add (F.sub a (half F eps)) (F.sub b (half F eps)) =
      F.sub (F.add a b) eps := by
  let h := half F eps
  change F.add (F.sub a h) (F.sub b h) =
      F.sub (F.add a b) eps
  rw [F.sub_eq_add_neg a h, F.sub_eq_add_neg b h]
  rw [F.sub_eq_add_neg (F.add a b) eps]
  rw [<- half_add_half F eps]
  rw [neg_add_distrib F h h]
  have hmid :
      F.add (F.neg h) (F.add b (F.neg h)) =
        F.add b (F.add (F.neg h) (F.neg h)) := by
    calc
      F.add (F.neg h) (F.add b (F.neg h)) =
          F.add (F.add (F.neg h) b) (F.neg h) := by
            rw [<- F.add_assoc]
      _ = F.add (F.add b (F.neg h)) (F.neg h) := by
            rw [F.add_comm (F.neg h) b]
      _ = F.add b (F.add (F.neg h) (F.neg h)) := by
            rw [F.add_assoc]
  calc
    F.add (F.add a (F.neg h)) (F.add b (F.neg h)) =
        F.add a (F.add (F.neg h) (F.add b (F.neg h))) := by
          rw [F.add_assoc]
    _ = F.add a (F.add b (F.add (F.neg h) (F.neg h))) := by
          rw [hmid]
    _ = F.add (F.add a b) (F.add (F.neg h) (F.neg h)) := by
          rw [<- F.add_assoc]

/-- Subadditivity: a limsup witness of the pointwise sum is at most the sum
of limsup witnesses of the summands. Each summand is estimated to half an
`eps` and the halves are recombined by `add_add_halves`; nothing beyond the
`IsLimsup` clauses enters, so the bound holds over any ordered field. -/
theorem limsup_add_le_add_limsup
    {u v : Nat -> alpha} {Luv Lu Lv : alpha}
    (hadd : IsLimsup F (fun n : Nat => F.add (u n) (v n)) Luv)
    (hu : IsLimsup F u Lu)
    (hv : IsLimsup F v Lv) :
    F.le Luv (F.add Lu Lv) := by
  apply limsup_le_of_eventually_lt_add F hadd
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  apply Eventually.mono ?_
    (Eventually.and (hu.left e2 he2) (hv.left e2 he2))
  intro n hn
  have hsum := add_lt_add F hn.left hn.right
  rwa [add_add_halves F Lu Lv eps] at hsum

/-- Superadditivity of the liminf: the sum of liminf witnesses of the
summands is at most a liminf witness of the pointwise sum, by the mirrored
half-epsilon argument. -/
theorem add_liminf_le_liminf_add
    {u v : Nat -> alpha} {Luv lu lv : alpha}
    (hadd : IsLiminf F (fun n : Nat => F.add (u n) (v n)) Luv)
    (hu : IsLiminf F u lu)
    (hv : IsLiminf F v lv) :
    F.le (F.add lu lv) Luv := by
  apply le_liminf_of_eventually_sub_lt F hadd
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  apply Eventually.mono ?_
    (Eventually.and (hu.left e2 he2) (hv.left e2 he2))
  intro n hn
  have hsum := add_lt_add F hn.left hn.right
  rwa [add_sub_halves F lu lv eps] at hsum

/-- The first mixed inequality: a liminf witness of the pointwise sum is at
most the liminf witness of one summand plus the limsup witness of the other.
Mixing an eventual clause with a frequent clause is what makes the proof
pair the two cutoffs through a max instead of sharing one. -/
theorem liminf_add_le_add_liminf_limsup
    {u v : Nat -> alpha} {Luv lu Lv : alpha}
    (hadd : IsLiminf F (fun n : Nat => F.add (u n) (v n)) Luv)
    (hu : IsLiminf F u lu)
    (hv : IsLimsup F v Lv) :
    F.le Luv (F.add lu Lv) := by
  apply liminf_le_of_frequently_lt_add F hadd
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  intro N
  cases hv.left e2 he2 with
  | intro Nv hNv =>
      cases hu.right e2 he2 (Nat.max N Nv) with
      | intro n hn =>
          refine Exists.intro n ?_
          constructor
          · exact Nat.le_trans (Nat.le_max_left N Nv) hn.left
          · have hvn : F.lt (v n) (F.add Lv e2) :=
              hNv n (Nat.le_trans (Nat.le_max_right N Nv) hn.left)
            have hsum := add_lt_add F hn.right hvn
            rwa [add_add_halves F lu Lv eps] at hsum

/-- The second mixed inequality: the liminf witness of one summand plus the
limsup witness of the other is at most a limsup witness of the pointwise
sum. Chained with `liminf_add_le_add_liminf_limsup` it brackets the mixed
sums between the two one-sided bounds. -/
theorem add_liminf_limsup_le_limsup_add
    {u v : Nat -> alpha} {Luv lu Lv : alpha}
    (hadd : IsLimsup F (fun n : Nat => F.add (u n) (v n)) Luv)
    (hu : IsLiminf F u lu)
    (hv : IsLimsup F v Lv) :
    F.le (F.add lu Lv) Luv := by
  apply le_limsup_of_frequently_sub_lt F hadd
  intro eps heps
  let e2 := half F eps
  have he2 : F.lt F.zero e2 :=
    half_pos F heps
  intro N
  cases hu.left e2 he2 with
  | intro Nu hNu =>
      cases hv.right e2 he2 (Nat.max N Nu) with
      | intro n hn =>
          refine Exists.intro n ?_
          constructor
          · exact Nat.le_trans (Nat.le_max_left N Nu) hn.left
          · have hun : F.lt (F.sub lu e2) (u n) :=
              hNu n (Nat.le_trans (Nat.le_max_right N Nu) hn.left)
            have hsum := add_lt_add F hun hn.right
            rwa [add_sub_halves F lu Lv eps] at hsum

theorem neg_sub_eq_neg_add (x eps : alpha) :
    F.neg (F.sub x eps) = F.add (F.neg x) eps := by
  calc
    F.neg (F.sub x eps) = F.sub eps x := by
      rw [<- sub_rev_eq_neg_sub F x eps]
    _ = F.add eps (F.neg x) := by
      rw [F.sub_eq_add_neg]
    _ = F.add (F.neg x) eps := by
      rw [F.add_comm eps (F.neg x)]

theorem neg_add_eq_neg_sub (x eps : alpha) :
    F.neg (F.add x eps) = F.sub (F.neg x) eps := by
  rw [neg_add_distrib F x eps]
  rw [F.sub_eq_add_neg]

/-- Negation exchanges the two halves: a liminf witness `l` of `u` yields a
limsup witness of the negated sequence, namely `-l`. This is the bridge that
carries the addition inequality over to subtraction below. -/
theorem limsup_neg_of_liminf
    {u : Nat -> alpha} {l : alpha}
    (hl : IsLiminf F u l) :
    IsLimsup F (fun n : Nat => F.neg (u n)) (F.neg l) := by
  constructor
  · intro eps heps
    apply Eventually.mono ?_ (hl.left eps heps)
    intro n hn
    have h := neg_lt_neg F hn
    rwa [neg_sub_eq_neg_add F l eps] at h
  · intro eps heps N
    cases hl.right eps heps N with
    | intro n hn =>
        refine Exists.intro n ?_
        constructor
        · exact hn.left
        · have h := neg_lt_neg F hn.right
          rwa [neg_add_eq_neg_sub F l eps] at h

/-- The mirror bridge: a limsup witness `L` of `u` yields the liminf witness
`-L` of the negated sequence. -/
theorem liminf_neg_of_limsup
    {u : Nat -> alpha} {L : alpha}
    (hL : IsLimsup F u L) :
    IsLiminf F (fun n : Nat => F.neg (u n)) (F.neg L) := by
  constructor
  · intro eps heps
    apply Eventually.mono ?_ (hL.left eps heps)
    intro n hn
    have h := neg_lt_neg F hn
    rwa [neg_add_eq_neg_sub F L eps] at h
  · intro eps heps N
    cases hL.right eps heps N with
    | intro n hn =>
        refine Exists.intro n ?_
        constructor
        · exact hn.left
        · have h := neg_lt_neg F hn.right
          rwa [neg_sub_eq_neg_add F L eps] at h

/-- Subtraction bound: a limsup witness of the pointwise difference is at
most the limsup witness of the minuend minus the liminf witness of the
subtrahend. Obtained by rewriting the difference as a sum against the
negated subtrahend and applying `limsup_add_le_add_limsup` through
`limsup_neg_of_liminf`. -/
theorem limsup_sub_le_sub_liminf
    {u v : Nat -> alpha} {Lsub Lu lv : alpha}
    (hsub : IsLimsup F (fun n : Nat => F.sub (u n) (v n)) Lsub)
    (hu : IsLimsup F u Lu)
    (hv : IsLiminf F v lv) :
    F.le Lsub (F.sub Lu lv) := by
  have hsubAdd :
      IsLimsup F (fun n : Nat => F.add (u n) (F.neg (v n))) Lsub :=
    isLimsup_congr F
      (fun n => F.sub_eq_add_neg (u n) (v n)) hsub
  have hneg :
      IsLimsup F (fun n : Nat => F.neg (v n)) (F.neg lv) :=
    limsup_neg_of_liminf F hv
  have h :=
    limsup_add_le_add_limsup F hsubAdd hu hneg
  rwa [<- F.sub_eq_add_neg Lu lv] at h

/-- The subtraction bound on the liminf side: the liminf witness of the
minuend minus the limsup witness of the subtrahend is at most a liminf
witness of the pointwise difference. -/
theorem sub_limsup_le_liminf_sub
    {u v : Nat -> alpha} {lsub lu Lv : alpha}
    (hsub : IsLiminf F (fun n : Nat => F.sub (u n) (v n)) lsub)
    (hu : IsLiminf F u lu)
    (hv : IsLimsup F v Lv) :
    F.le (F.sub lu Lv) lsub := by
  have hsubAdd :
      IsLiminf F (fun n : Nat => F.add (u n) (F.neg (v n))) lsub :=
    isLiminf_congr F
      (fun n => F.sub_eq_add_neg (u n) (v n)) hsub
  have hneg :
      IsLiminf F (fun n : Nat => F.neg (v n)) (F.neg Lv) :=
    liminf_neg_of_limsup F hv
  have h :=
    add_liminf_le_liminf_add F hsubAdd hu hneg
  rwa [<- F.sub_eq_add_neg lu Lv] at h

/-- The field element `1 / (n + 1)`, the canonical vanishing scale of the
cluster constructions below: indices get selected where `u` climbs above
`L - 1 / (k + 1)`, and only an Archimedean principle can make those windows
shrink. -/
def invSucc (n : Nat) : alpha :=
  F.inv (nat F (n + 1))

theorem invSucc_pos (n : Nat) :
    F.lt F.zero (invSucc F n) :=
  inv_pos F (nat_succ_pos F n)

/-- The index selection behind the cluster subsequence: at stage `k` an index
is chosen, past the previous choice plus one, at which `u` exceeds
`L - 1 / (k + 1)`, by choice on the `Frequently` clause of `IsLimsup`.
Starting each search beyond the predecessor is what makes the selection a
subsequence rather than a mere sequence of witnesses. -/
noncomputable def limsupClusterIndex
    {u : Nat -> alpha} {L : alpha}
    (hL : IsLimsup F u L) : Nat -> Nat
  | 0 =>
      Classical.choose (hL.right (invSucc F 0) (invSucc_pos F 0) 0)
  | k + 1 =>
      Classical.choose
        (hL.right (invSucc F (k + 1)) (invSucc_pos F (k + 1))
          (limsupClusterIndex hL k + 1))

/-- What the selection delivers: the chosen index at stage `k + 1` clears the
cutoff it was chosen against, and the term there exceeds `L - 1 / (k + 1)`.
The only place where the recursive shape of the selection is exposed; the
corollaries after it turn that shape into a subsequence. -/
theorem limsupClusterIndex_spec
    {u : Nat -> alpha} {L : alpha}
    (hL : IsLimsup F u L) :
    forall k : Nat,
      And
        ((match k with
          | 0 => 0
          | j + 1 => limsupClusterIndex F hL j + 1) <=
            limsupClusterIndex F hL k)
        (F.lt (F.sub L (invSucc F k))
          (u (limsupClusterIndex F hL k)))
  | 0 =>
      Classical.choose_spec
        (hL.right (invSucc F 0) (invSucc_pos F 0) 0)
  | k + 1 =>
      Classical.choose_spec
        (hL.right (invSucc F (k + 1)) (invSucc_pos F (k + 1))
          (limsupClusterIndex F hL k + 1))

theorem limsupClusterIndex_step
    {u : Nat -> alpha} {L : alpha}
    (hL : IsLimsup F u L)
    (k : Nat) :
    limsupClusterIndex F hL k < limsupClusterIndex F hL (k + 1) := by
  have hle := (limsupClusterIndex_spec F hL (k + 1)).left
  change limsupClusterIndex F hL k + 1 <=
    limsupClusterIndex F hL (k + 1) at hle
  omega

theorem limsupClusterIndex_subsequence
    {u : Nat -> alpha} {L : alpha}
    (hL : IsLimsup F u L) :
    SubsequenceIndex (limsupClusterIndex F hL) :=
  limsupClusterIndex_step F hL

/-- The converse of `cluster_le_limsup`: a limsup witness is itself a cluster
value, on the selected subsequence. This is the one theorem of the
ordered-field part that needs more than ordered-field structure -- the
hypothesis `A` makes `1 / (n + 1)` eventually smaller than any given positive
`eps`, shrinking the windows the selection provides, which
ordered-field structure alone cannot do. The Dedekind-complete layer at
the end of this module discharges `A` from completeness. -/
theorem limsup_clusterValue
    {u : Nat -> alpha} {L : alpha}
    (A : F.InvNatArchimedeanPrinciple)
    (hL : IsLimsup F u L) :
    SeqClusterValue F u L := by
  refine Exists.intro (limsupClusterIndex F hL) ?_
  constructor
  · exact limsupClusterIndex_subsequence F hL
  · intro eps heps
    cases A.small_inv_succ heps with
    | intro N hN =>
        cases hL.left eps heps with
        | intro Nu hNu =>
            refine Exists.intro (Nat.max N Nu) ?_
            intro k hk
            have hNk : N <= k :=
              Nat.le_trans (Nat.le_max_left N Nu) hk
            have hNuk : Nu <= k :=
              Nat.le_trans (Nat.le_max_right N Nu) hk
            have hidx_ge_k :
                k <= limsupClusterIndex F hL k :=
              subsequenceIndex_ge_self
                (limsupClusterIndex_subsequence F hL) k
            have hNu_idx :
                Nu <= limsupClusterIndex F hL k :=
              Nat.le_trans hNuk hidx_ge_k
            have hupper :
                F.lt (u (limsupClusterIndex F hL k))
                  (F.add L eps) :=
              hNu (limsupClusterIndex F hL k) hNu_idx
            have hnat_le :
                F.le (nat F (N + 1)) (nat F (k + 1)) :=
              nat_le_nat_of_le F (Nat.succ_le_succ hNk)
            have hinv_le :
                F.le (invSucc F k) (invSucc F N) := by
              unfold invSucc
              exact inv_le_inv_of_le_pos F
                (nat_succ_pos F N) (nat_succ_pos F k) hnat_le
            have hinv_lt_eps :
                F.lt (invSucc F k) eps :=
              lt_of_le_of_lt F hinv_le hN
            have hsub_le :
                F.le (F.sub L eps) (F.sub L (invSucc F k)) :=
              sub_le_sub_of_le_of_le F
                (F.le_refl L) (le_of_lt F hinv_lt_eps)
            have hlower :
                F.lt (F.sub L eps)
                  (u (limsupClusterIndex F hL k)) :=
              lt_of_le_of_lt F hsub_le
                (limsupClusterIndex_spec F hL k).right
            exact abs_sub_lt_of_bounds F hlower hupper

/-- The mirror selection for the liminf: at stage `k` an index is chosen,
past the previous choice plus one, at which `u` sits below `l + 1 / (k + 1)`,
by choice on the `Frequently` clause of `IsLiminf`. -/
noncomputable def liminfClusterIndex
    {u : Nat -> alpha} {l : alpha}
    (hl : IsLiminf F u l) : Nat -> Nat
  | 0 =>
      Classical.choose (hl.right (invSucc F 0) (invSucc_pos F 0) 0)
  | k + 1 =>
      Classical.choose
        (hl.right (invSucc F (k + 1)) (invSucc_pos F (k + 1))
          (liminfClusterIndex hl k + 1))

/-- The liminf selection's contract, mirroring `limsupClusterIndex_spec`: the
cutoffs are cleared and the term at each chosen index is below
`l + 1 / (k + 1)`. -/
theorem liminfClusterIndex_spec
    {u : Nat -> alpha} {l : alpha}
    (hl : IsLiminf F u l) :
    forall k : Nat,
      And
        ((match k with
          | 0 => 0
          | j + 1 => liminfClusterIndex F hl j + 1) <=
            liminfClusterIndex F hl k)
        (F.lt (u (liminfClusterIndex F hl k))
          (F.add l (invSucc F k)))
  | 0 =>
      Classical.choose_spec
        (hl.right (invSucc F 0) (invSucc_pos F 0) 0)
  | k + 1 =>
      Classical.choose_spec
        (hl.right (invSucc F (k + 1)) (invSucc_pos F (k + 1))
          (liminfClusterIndex F hl k + 1))

theorem liminfClusterIndex_step
    {u : Nat -> alpha} {l : alpha}
    (hl : IsLiminf F u l)
    (k : Nat) :
    liminfClusterIndex F hl k < liminfClusterIndex F hl (k + 1) := by
  have hle := (liminfClusterIndex_spec F hl (k + 1)).left
  change liminfClusterIndex F hl k + 1 <=
    liminfClusterIndex F hl (k + 1) at hle
  omega

theorem liminfClusterIndex_subsequence
    {u : Nat -> alpha} {l : alpha}
    (hl : IsLiminf F u l) :
    SubsequenceIndex (liminfClusterIndex F hl) :=
  liminfClusterIndex_step F hl

/-- The liminf counterpart of `limsup_clusterValue`: a liminf witness is a
cluster value on its selected subsequence, with the inverse-natural
Archimedean principle as the only input beyond ordered-field structure. -/
theorem liminf_clusterValue
    {u : Nat -> alpha} {l : alpha}
    (A : F.InvNatArchimedeanPrinciple)
    (hl : IsLiminf F u l) :
    SeqClusterValue F u l := by
  refine Exists.intro (liminfClusterIndex F hl) ?_
  constructor
  · exact liminfClusterIndex_subsequence F hl
  · intro eps heps
    cases A.small_inv_succ heps with
    | intro N hN =>
        cases hl.left eps heps with
        | intro Nu hNu =>
            refine Exists.intro (Nat.max N Nu) ?_
            intro k hk
            have hNk : N <= k :=
              Nat.le_trans (Nat.le_max_left N Nu) hk
            have hNuk : Nu <= k :=
              Nat.le_trans (Nat.le_max_right N Nu) hk
            have hidx_ge_k :
                k <= liminfClusterIndex F hl k :=
              subsequenceIndex_ge_self
                (liminfClusterIndex_subsequence F hl) k
            have hNu_idx :
                Nu <= liminfClusterIndex F hl k :=
              Nat.le_trans hNuk hidx_ge_k
            have hlower :
                F.lt (F.sub l eps)
                  (u (liminfClusterIndex F hl k)) :=
              hNu (liminfClusterIndex F hl k) hNu_idx
            have hnat_le :
                F.le (nat F (N + 1)) (nat F (k + 1)) :=
              nat_le_nat_of_le F (Nat.succ_le_succ hNk)
            have hinv_le :
                F.le (invSucc F k) (invSucc F N) := by
              unfold invSucc
              exact inv_le_inv_of_le_pos F
                (nat_succ_pos F N) (nat_succ_pos F k) hnat_le
            have hinv_lt_eps :
                F.lt (invSucc F k) eps :=
              lt_of_le_of_lt F hinv_le hN
            have hadd_le :
                F.le (F.add l (invSucc F k)) (F.add l eps) :=
              add_le_add_left F (le_of_lt F hinv_lt_eps) l
            have hupper :
                F.lt (u (liminfClusterIndex F hl k))
                  (F.add l eps) :=
              lt_of_lt_of_le F
                (liminfClusterIndex_spec F hl k).right hadd_le
            exact abs_sub_lt_of_bounds F hlower hupper

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The bridge between the construction and the characterization: the value
built in `Tautology.RealSequence.Limsup.CompleteCore` as the greatest lower
bound of the tail suprema satisfies the predicate `IsLimsup`. Both boundedness
hypotheses are structural -- `hAbove` is what makes each tail supremum exist,
while `hBelow` is what keeps the family of tail suprema bounded below, without
which its greatest lower bound would not exist either. -/
theorem limsup_isLimsup
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.IsLimsup u (limsup C u hAbove hBelow) := by
  let F := C.field
  constructor
  · intro eps heps
    let L := limsup C u hAbove hBelow
    have hLlt : F.lt L (F.add L eps) := by
      have h := IsOrderedFieldBaseLike.add_lt_add_left F heps L
      rwa [F.add_zero] at h
    cases IsOrderedFieldBaseLike.exists_gt_of_glb_lt F
        (limsup_is_glb C u hAbove hBelow) hLlt with
    | intro s hs =>
        cases hs.left with
        | intro N hN =>
            refine Exists.intro N ?_
            intro n hn
            have hmem :
                IsOrderedFieldBaseLike.TailValues u N (u n) :=
              Exists.intro n (And.intro hn rfl)
            have hu_le :
                F.le (u n) (tailSup C u hAbove N) :=
              IsOrderedFieldBaseLike.le_lub_of_mem F
                (tailSup_is_lub C u hAbove N) hmem
            rw [<- hN] at hu_le
            exact IsOrderedFieldBaseLike.lt_of_le_of_lt F hu_le hs.right
  · intro eps heps N
    let L := limsup C u hAbove hBelow
    have hsub_lt_L : F.lt (F.sub L eps) L :=
      IsOrderedFieldBaseLike.sub_lt_self_of_pos F heps
    have hL_le_tail :
        F.le L (tailSup C u hAbove N) :=
      (limsup_is_glb C u hAbove hBelow).left
        (tailSup C u hAbove N)
        (Exists.intro N rfl)
    have hsub_lt_tail :
        F.lt (F.sub L eps) (tailSup C u hAbove N) :=
      IsOrderedFieldBaseLike.lt_of_lt_of_le F hsub_lt_L hL_le_tail
    cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub F
        (tailSup_is_lub C u hAbove N) hsub_lt_tail with
    | intro x hx =>
        cases hx.left with
        | intro n hn =>
            refine Exists.intro n ?_
            constructor
            · exact hn.left
            · have hxlt := hx.right
              rwa [hn.right] at hxlt

/-- The bridge on the liminf side: the least upper bound of the tail infima
satisfies `IsLiminf`, with the two boundedness hypotheses playing the
mirrored roles (`hBelow` for each tail infimum, `hAbove` to bound the family
from above). -/
theorem liminf_isLiminf
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.IsLiminf u (liminf C u hAbove hBelow) := by
  let F := C.field
  constructor
  · intro eps heps
    let l := liminf C u hAbove hBelow
    have hsub_lt_l : F.lt (F.sub l eps) l :=
      IsOrderedFieldBaseLike.sub_lt_self_of_pos F heps
    cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub F
        (liminf_is_lub C u hAbove hBelow) hsub_lt_l with
    | intro s hs =>
        cases hs.left with
        | intro N hN =>
            refine Exists.intro N ?_
            intro n hn
            have hmem :
                IsOrderedFieldBaseLike.TailValues u N (u n) :=
              Exists.intro n (And.intro hn rfl)
            have htail_le :
                F.le (tailInf C u hBelow N) (u n) :=
              IsOrderedFieldBaseLike.glb_le_of_mem F
                (tailInf_is_glb C u hBelow N) hmem
            rw [<- hN] at htail_le
            exact IsOrderedFieldBaseLike.lt_of_lt_of_le F
              hs.right htail_le
  · intro eps heps N
    let l := liminf C u hAbove hBelow
    have hl_lt_add : F.lt l (F.add l eps) := by
      have h := IsOrderedFieldBaseLike.add_lt_add_left F heps l
      rwa [F.add_zero] at h
    have htail_le_l :
        F.le (tailInf C u hBelow N) l :=
      (liminf_is_lub C u hAbove hBelow).left
        (tailInf C u hBelow N)
        (Exists.intro N rfl)
    have htail_lt_add :
        F.lt (tailInf C u hBelow N) (F.add l eps) :=
      IsOrderedFieldBaseLike.lt_of_le_of_lt F htail_le_l hl_lt_add
    cases IsOrderedFieldBaseLike.exists_gt_of_glb_lt F
        (tailInf_is_glb C u hBelow N) htail_lt_add with
    | intro x hx =>
        cases hx.left with
        | intro n hn =>
            refine Exists.intro n ?_
            constructor
            · exact hn.left
            · have hxlt := hx.right
              rwa [hn.right] at hxlt

theorem limsup_clusterValue
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.SeqClusterValue u (limsup C u hAbove hBelow) :=
  IsOrderedFieldBaseLike.limsup_clusterValue C.field
    (C.invNatArchimedean)
    (limsup_isLimsup C u hAbove hBelow)

theorem liminf_clusterValue
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.SeqClusterValue u (liminf C u hAbove hBelow) :=
  IsOrderedFieldBaseLike.liminf_clusterValue C.field
    (C.invNatArchimedean)
    (liminf_isLiminf C u hAbove hBelow)

theorem cluster_le_limsup
    {u : Nat -> alpha} {x : alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u)
    (hx : C.field.SeqClusterValue u x) :
    C.field.le x (limsup C u hAbove hBelow) :=
  IsOrderedFieldBaseLike.cluster_le_limsup C.field
    (limsup_isLimsup C u hAbove hBelow) hx

theorem liminf_le_cluster
    {u : Nat -> alpha} {x : alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u)
    (hx : C.field.SeqClusterValue u x) :
    C.field.le (liminf C u hAbove hBelow) x :=
  IsOrderedFieldBaseLike.liminf_le_cluster C.field
    (liminf_isLiminf C u hAbove hBelow) hx

/-- The packaged classical statement: over a Dedekind-complete field, the
constructed limsup of a two-sided bounded sequence is a cluster value, and
every cluster value lies below it. The Archimedean hypothesis that
`IsOrderedFieldBaseLike.limsup_clusterValue` demands is supplied by the field
itself, through `invNatArchimedean` of `Tautology.RealBootstrap.Archimedean`.
-/
theorem limsup_is_greatest_clusterValue
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    And
      (C.field.SeqClusterValue u (limsup C u hAbove hBelow))
      (forall x : alpha,
        C.field.SeqClusterValue u x ->
          C.field.le x (limsup C u hAbove hBelow)) :=
  And.intro
    (limsup_clusterValue C u hAbove hBelow)
    (fun _ hx => cluster_le_limsup C hAbove hBelow hx)

/-- The mirrored package: the constructed liminf is a cluster value and every
cluster value lies above it, so the cluster values of a two-sided bounded
sequence sit between the two, with both endpoints attained. -/
theorem liminf_is_least_clusterValue
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    And
      (C.field.SeqClusterValue u (liminf C u hAbove hBelow))
      (forall x : alpha,
        C.field.SeqClusterValue u x ->
          C.field.le (liminf C u hAbove hBelow) x) :=
  And.intro
    (liminf_clusterValue C u hAbove hBelow)
    (fun _ hx => liminf_le_cluster C hAbove hBelow hx)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
