import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements
import Tengoku.Tautology.Tautology.RealSequence.Principles.Dyadic
import Tengoku.Tautology.Tautology.RealSequence.Principles.NestedBasic

/-!
# Entry: nested intervals give finite subcovers

The mirror image of
`Tautology.RealCompactness.ClosedInterval.FromNestedSequential`: the same
bisection machinery, the same two explicit hypotheses, aimed at the cover side
of the graph.

What differs is the steering criterion and the closing move. Bisection is
steered here by badness -- if both halves had finite subcovers, so would the
whole, hence some half stays bad -- and the argument ends by contradiction: the
common point of the nested chain lies in some member of the cover, that member
contains an interval around it with positive slack on both sides, and once the
stage length drops below that slack the whole stage fits inside a single
member, contradicting its badness. The dyadic hypothesis is used once, to make
the lengths small.

## Position and role

Entry module, exporting a universe-polymorphic `Target` that
`Tautology.RealCompactness.ClosedInterval.Routes` instantiates at `max u 1`.
Proved and available; the selected route reaches the cover side through the
sequential principle instead.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace FromNestedFinite

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The promise of this entry point, kept at the ordered-field level: the
nested-interval principle and the dyadic Archimedean principle, both taken
as explicit hypotheses, imply the closed-interval compactness node. It is
the nested-interval counterpart of `FromSupFinite`, which reaches the same
node from the supremum property over a complete field. -/
def Target : Prop :=
  F.NestedIntervalPrinciple ->
    F.DyadicArchimedeanPrinciple ->
      ClosedIntervalCompactnessPrinciple.{u} F

/-- The negation the argument is driven by: no finite list of indices from
`U` covers `[left, right]`. Naming it lets the invariants below say that a
stage is bad rather than repeat a negation. -/
def NoFiniteSubcover {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) : Prop :=
  Not (FiniteSubcover U (F.ClosedInterval left right))

/-- A closed interval, `left ≤ right`, that has no finite subcover: the
predicate the bisection keeps true at every stage. -/
def BadInterval {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) : Prop :=
  And (F.le left right) (NoFiniteSubcover F U left right)

/-- Two list subcovers of the halves concatenate into one of the whole: a
point of `[a, b]` lies on one side of `m` or the other. This is the only
way index lists are combined in the argument. -/
theorem combine_half_subcovers {iota : Type u}
    {U : iota -> alpha -> Prop} {a m b : alpha}
    {js ks : List iota}
    (hleft : ListSubcover U (F.ClosedInterval a m) js)
    (hright : ListSubcover U (F.ClosedInterval m b) ks) :
    ListSubcover U (F.ClosedInterval a b) (js ++ ks) := by
  intro x hx
  by_cases hxm : F.le x m
  · cases hleft x (And.intro hx.left hxm) with
    | intro i hi =>
        refine Exists.intro i ?_
        exact And.intro (List.mem_append_left ks hi.left) hi.right
  · have hmx : F.le m x := by
      cases F.le_total m x with
      | inl h => exact h
      | inr h => exact False.elim (hxm h)
    cases hright x (And.intro hmx hx.right) with
    | intro i hi =>
        refine Exists.intro i ?_
        exact And.intro (List.mem_append_right js hi.left) hi.right

theorem finiteSubcover_of_halves {iota : Type u}
    {U : iota -> alpha -> Prop} {a m b : alpha}
    (hleft : FiniteSubcover U (F.ClosedInterval a m))
    (hright : FiniteSubcover U (F.ClosedInterval m b)) :
    FiniteSubcover U (F.ClosedInterval a b) := by
  cases hleft with
  | intro js hjs =>
      cases hright with
      | intro ks hks =>
          exact Exists.intro (js ++ ks)
            (combine_half_subcovers F hjs hks)

/-- The contrapositive that steers the bisection: if `[a, b]` has no
finite subcover while `[a, m]` does, then `[m, b]` has none either, since
covers of the two halves would concatenate into one of the whole. -/
theorem right_half_bad_of_left_finite {iota : Type u}
    {U : iota -> alpha -> Prop} {a b m : alpha}
    (hbad : NoFiniteSubcover F U a b)
    (hleft : FiniteSubcover U (F.ClosedInterval a m)) :
    NoFiniteSubcover F U m b := by
  intro hright
  exact hbad (finiteSubcover_of_halves F hleft hright)

/-- One bisection step: keep the half that has not yet been covered --
the right half when the left one has a finite subcover, the left half
otherwise. The test branches on a `Prop` under classical choice, hence
the noncomputable marker. -/
noncomputable def stepInterval {iota : Type u}
    (U : iota -> alpha -> Prop) (I : Prod alpha alpha) :
    Prod alpha alpha := by
  classical
  let a := I.fst
  let b := I.snd
  let m := midpoint F a b
  exact
    if FiniteSubcover U (F.ClosedInterval a m) then
      (m, b)
    else
      (a, m)

/-- The bisection run: `bisectInterval n` applies `stepInterval` `n`
times starting from `[left, right]`, each step keeping an uncoverable
half. -/
noncomputable def bisectInterval {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) :
    Nat -> Prod alpha alpha
  | 0 => (left, right)
  | n + 1 => stepInterval F U (bisectInterval U left right n)

/-- The left endpoints of the bisection run; with `upper` it forms the
pair of sequences the nested-interval principle is applied to. -/
noncomputable def lower {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) (n : Nat) :
    alpha :=
  (bisectInterval F U left right n).fst

/-- The right endpoints of the bisection run, companion of `lower`. -/
noncomputable def upper {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) (n : Nat) :
    alpha :=
  (bisectInterval F U left right n).snd

theorem lower_zero {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) :
    lower F U left right 0 = left :=
  rfl

theorem upper_zero {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) :
    upper F U left right 0 = right :=
  rfl

theorem lower_succ_right {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha} {n : Nat}
    (h :
      FiniteSubcover U
        (F.ClosedInterval
          (lower F U left right n)
          (midpoint F (lower F U left right n) (upper F U left right n)))) :
    lower F U left right (n + 1) =
      midpoint F (lower F U left right n) (upper F U left right n) := by
  classical
  have h' :
      FiniteSubcover U
        (F.ClosedInterval
          (bisectInterval F U left right n).fst
          (midpoint F (bisectInterval F U left right n).fst
            (bisectInterval F U left right n).snd)) := by
    simpa [lower, upper] using h
  simp [lower, upper, bisectInterval, stepInterval, h']

theorem upper_succ_right {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha} {n : Nat}
    (h :
      FiniteSubcover U
        (F.ClosedInterval
          (lower F U left right n)
          (midpoint F (lower F U left right n) (upper F U left right n)))) :
    upper F U left right (n + 1) = upper F U left right n := by
  classical
  have h' :
      FiniteSubcover U
        (F.ClosedInterval
          (bisectInterval F U left right n).fst
          (midpoint F (bisectInterval F U left right n).fst
            (bisectInterval F U left right n).snd)) := by
    simpa [lower, upper] using h
  simp [upper, bisectInterval, stepInterval, h']

theorem lower_succ_left {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha} {n : Nat}
    (h :
      Not
        (FiniteSubcover U
          (F.ClosedInterval
            (lower F U left right n)
            (midpoint F (lower F U left right n) (upper F U left right n))))) :
    lower F U left right (n + 1) = lower F U left right n := by
  classical
  have h' :
      Not
        (FiniteSubcover U
          (F.ClosedInterval
            (bisectInterval F U left right n).fst
            (midpoint F (bisectInterval F U left right n).fst
              (bisectInterval F U left right n).snd))) := by
    simpa [lower, upper] using h
  simp [lower, bisectInterval, stepInterval, h']

theorem upper_succ_left {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha} {n : Nat}
    (h :
      Not
        (FiniteSubcover U
          (F.ClosedInterval
            (lower F U left right n)
            (midpoint F (lower F U left right n) (upper F U left right n))))) :
    upper F U left right (n + 1) =
      midpoint F (lower F U left right n) (upper F U left right n) := by
  classical
  have h' :
      Not
        (FiniteSubcover U
          (F.ClosedInterval
            (bisectInterval F U left right n).fst
            (midpoint F (bisectInterval F U left right n).fst
              (bisectInterval F U left right n).snd))) := by
    simpa [lower, upper] using h
  simp [lower, upper, bisectInterval, stepInterval, h']

theorem interval_order {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) :
    forall n : Nat, F.le (lower F U left right n) (upper F U left right n) := by
  intro n
  induction n with
  | zero =>
      rw [lower_zero, upper_zero]
      exact h0
  | succ n ih =>
      by_cases hleft :
        FiniteSubcover U
          (F.ClosedInterval
            (lower F U left right n)
            (midpoint F (lower F U left right n) (upper F U left right n)))
      · rw [lower_succ_right F hleft, upper_succ_right F hleft]
        exact midpoint_le_right F ih
      · rw [lower_succ_left F hleft, upper_succ_left F hleft]
        exact left_le_midpoint F ih

theorem lower_step_le {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) (n : Nat) :
    F.le (lower F U left right n) (lower F U left right (n + 1)) := by
  by_cases hleft :
    FiniteSubcover U
      (F.ClosedInterval
        (lower F U left right n)
        (midpoint F (lower F U left right n) (upper F U left right n)))
  · rw [lower_succ_right F hleft]
    exact left_le_midpoint F (interval_order F h0 n)
  · rw [lower_succ_left F hleft]
    exact F.le_refl (lower F U left right n)

theorem upper_step_le {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) (n : Nat) :
    F.le (upper F U left right (n + 1)) (upper F U left right n) := by
  by_cases hleft :
    FiniteSubcover U
      (F.ClosedInterval
        (lower F U left right n)
        (midpoint F (lower F U left right n) (upper F U left right n)))
  · rw [upper_succ_right F hleft]
    exact F.le_refl (upper F U left right n)
  · rw [upper_succ_left F hleft]
    exact midpoint_le_right F (interval_order F h0 n)

theorem lower_mono {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) {n m : Nat} (hnm : n <= m) :
    F.le (lower F U left right n) (lower F U left right m) := by
  exact monotoneIncreasing_of_step F (lower_step_le F h0) n m hnm

theorem upper_antitone {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) {n m : Nat} (hnm : n <= m) :
    F.le (upper F U left right m) (upper F U left right n) := by
  exact monotoneDecreasing_of_step F (upper_step_le F h0) n m hnm

/-- The bisection run is a nested chain of closed intervals, the shape
`NestedClosedIntervals` demands; only `left ≤ right` enters, not which
half was kept. -/
theorem nested_intervals {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right) :
    F.NestedClosedIntervals
      (lower F U left right) (upper F U left right) := by
  constructor
  · exact interval_order F h0
  · constructor
    · intro n m hnm
      exact lower_mono F h0 hnm
    · intro n m hnm
      exact upper_antitone F h0 hnm

/-- The steering invariant: if the starting interval has no finite
subcover, neither does any stage of the bisection. Some half always
inherits the badness, because covers of both halves would concatenate
into one of the whole. -/
theorem bad_intervals {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right)
    (hbad0 : NoFiniteSubcover F U left right) :
    forall n : Nat, BadInterval F U
      (lower F U left right n) (upper F U left right n) := by
  intro n
  induction n with
  | zero =>
      exact And.intro (by simpa [lower_zero, upper_zero] using h0)
        (by simpa [lower_zero, upper_zero] using hbad0)
  | succ n ih =>
      by_cases hleft :
        FiniteSubcover U
          (F.ClosedInterval
            (lower F U left right n)
            (midpoint F (lower F U left right n) (upper F U left right n)))
      · have hright_bad :
            NoFiniteSubcover F U
              (midpoint F (lower F U left right n) (upper F U left right n))
              (upper F U left right n) :=
          right_half_bad_of_left_finite F ih.right hleft
        rw [lower_succ_right F hleft, upper_succ_right F hleft]
        exact And.intro
          (midpoint_le_right F ih.left)
          hright_bad
      · rw [lower_succ_left F hleft, upper_succ_left F hleft]
        exact And.intro
          (left_le_midpoint F ih.left)
          hleft

/-- The length `upper n - lower n` of the `n`-th bisection stage; it
halves exactly at every step, which is what the dyadic Archimedean
hypothesis will drive below every positive bound. -/
noncomputable def length {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) (n : Nat) :
    alpha :=
  F.sub (upper F U left right n) (lower F U left right n)

theorem length_zero {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) :
    length F U left right 0 = F.sub right left := by
  unfold length
  rw [lower_zero, upper_zero]

theorem length_succ {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (n : Nat) :
    length F U left right (n + 1) =
      half F (length F U left right n) := by
  unfold length
  by_cases hleft :
    FiniteSubcover U
      (F.ClosedInterval
        (lower F U left right n)
        (midpoint F (lower F U left right n) (upper F U left right n)))
  · rw [lower_succ_right F hleft, upper_succ_right F hleft]
    exact right_sub_midpoint F
      (lower F U left right n) (upper F U left right n)
  · rw [lower_succ_left F hleft, upper_succ_left F hleft]
    exact midpoint_sub_left F
      (lower F U left right n) (upper F U left right n)

/-- The closed form of the stage lengths: after `n` halvings the stage has
length exactly `(right - left) / 2^n`, `dyadic n` being `2^n`. -/
theorem length_formula {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (n : Nat) :
    length F U left right n =
      F.mul (F.sub right left) (F.inv (dyadic F n)) := by
  induction n with
  | zero =>
      rw [length_zero, dyadic_zero, inv_one F, F.mul_one]
  | succ n ih =>
      rw [length_succ F n, ih]
      unfold half
      rw [dyadic_succ]
      have hdne : Not (dyadic F n = F.zero) :=
        dyadic_ne_zero F n
      have htwo_ne : Not (two F = F.zero) :=
        two_ne_zero F
      rw [inv_mul F hdne htwo_ne]
      calc
        F.mul (F.mul (F.sub right left) (F.inv (dyadic F n)))
            (F.inv (two F)) =
            F.mul (F.sub right left)
              (F.mul (F.inv (dyadic F n)) (F.inv (two F))) := by
              rw [F.mul_assoc]
        _ = F.mul (F.sub right left)
              (F.mul (F.inv (two F)) (F.inv (dyadic F n))) := by
              rw [F.mul_comm (F.inv (dyadic F n)) (F.inv (two F))]

/-- The stage lengths tend to zero; the dyadic Archimedean hypothesis
enters exactly here, making the nonnegative quantity `L / 2^n`
eventually smaller than any positive bound. -/
theorem length_tendsto_zero {iota : Type u}
    {U : iota -> alpha -> Prop} {left right : alpha}
    (h0 : F.le left right)
    (hdyadic : F.DyadicArchimedeanPrinciple) :
    F.IntervalLengthsToZero
      (lower F U left right) (upper F U left right) := by
  intro eps heps
  let L := F.sub right left
  have hL_nonneg : F.le F.zero L :=
    sub_nonneg_of_le F h0
  cases hdyadic.small_mul_inv hL_nonneg heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      have hlen_le :
          F.le (length F U left right n) (length F U left right N) := by
        unfold length
        exact sub_le_sub_of_le_of_le F
          (upper_antitone F h0 hn)
          (lower_mono F h0 hn)
      have hlenN :
          F.lt (length F U left right N) eps := by
        rwa [length_formula F N]
      have hlen_lt : F.lt (length F U left right n) eps :=
        lt_of_le_of_lt F hlen_le hlenN
      have hlen_nonneg :
          F.le F.zero (length F U left right n) := by
        unfold length
        exact sub_nonneg_of_le F (interval_order F h0 n)
      change
        F.lt (abs F (F.sub (length F U left right n) F.zero)) eps
      rwa [sub_zero F (length F U left right n),
        abs_of_nonneg F hlen_nonneg]

/-- A closed interval `[left, right]` containing `x` fits inside the open
interval `(a, b)` as soon as it is shorter than both gaps `x - a` and
`b - x`; the distance bounds come from
`NestedBasic.interval_points_close`. -/
theorem interval_subset_open_interval {left right x a b y : alpha}
    (hx : F.ClosedInterval left right x)
    (hy : F.ClosedInterval left right y)
    (hlen_left : F.lt (F.sub right left) (F.sub x a))
    (hlen_right : F.lt (F.sub right left) (F.sub b x)) :
    F.OpenInterval a b y := by
  have hclose_left :
      F.lt (abs F (F.sub y x)) (F.sub x a) :=
    NestedBasic.interval_points_close F hy hx hlen_left
  have hay : F.lt a y := by
    have h := abs_sub_lt_left F hclose_left
    rwa [sub_self_sub F x a] at h
  have hclose_right :
      F.lt (abs F (F.sub y x)) (F.sub b x) :=
    NestedBasic.interval_points_close F hy hx hlen_right
  have hyb : F.lt y b := by
    have h := abs_sub_lt_right F hclose_right
    have hx_sub : F.add x (F.sub b x) = b := by
      rw [F.add_comm x (F.sub b x)]
      exact sub_add_cancel F b x
    rwa [hx_sub] at h
  exact And.intro hay hyb

/-- An interval that small, sitting inside the open interval of one cover
member, is covered by that single member's index alone. This is the shape
of the contradiction that ends the main argument. -/
theorem singleton_subcover_of_small_interval {iota : Type u}
    {U : iota -> alpha -> Prop} {left right x a b : alpha} {i : iota}
    (hx : F.ClosedInterval left right x)
    (hlen_left : F.lt (F.sub right left) (F.sub x a))
    (hlen_right : F.lt (F.sub right left) (F.sub b x))
    (hinside : forall y : alpha, F.OpenInterval a b y -> U i y) :
    FiniteSubcover U (F.ClosedInterval left right) := by
  refine Exists.intro [i] ?_
  intro y hy
  refine Exists.intro i ?_
  constructor
  · exact List.Mem.head []
  · exact hinside y
      (interval_subset_open_interval F hx hy hlen_left hlen_right)

end FromNestedFinite
end Compactness
end IsOrderedFieldBaseLike
end Tautology
