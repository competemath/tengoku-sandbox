import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.Nat.Least

/-!
# Edge: a Lebesgue number gives finite subcovers

The reverse of `Tautology.RealCompactness.ClosedInterval.FiniteToLebesgue`, and
it needs a `LinearArchimedeanPrinciple`. The reason is that the construction
lays a grid of step `delta / 2` across the interval and must know that finitely
many steps suffice -- that some natural number `N` has `right - left` below `N`
times the step. Nothing else in the file uses it.

Grid points beyond the right end are clamped back to it, since a Lebesgue ball
is only useful when centred inside the interval. Each of the finitely many
centres selects one member of the cover, and those members cover everything:
any point is within `delta` of a grid point whose index is at most `N`, found
by taking the least index that overshoots it.

## Position and role

Edge module implementing `LebesgueToFiniteSubcover`, exporting `target`. The
selected route does not travel it -- it is exported because
`compactnessEquivalence` is a fact about the two nodes regardless of the path
taken. Its grid vocabulary has a second life in
`Tautology.RealDerivative.BoundedVariation.Covering.DirectDyadicCore`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike
namespace Compactness
namespace LebesgueToFinite

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The edge proved by this file: a Lebesgue number turns open covers of a
closed interval into finite ones. The extra hypothesis is the linear
Archimedean principle, and it is not decoration: the finite list has to be
bounded in advance, which needs the interval's length to be overrun by
finitely many steps of a fixed positive size -- the number of steps is
exactly what the principle supplies. -/
def Target : Prop :=
  IsOrderedFieldBaseLike.LebesgueToFiniteSubcover.{u} F

/-- The countdown list of stages up to `N`: `N` first, `0` last. -/
def natListUpTo : Nat -> List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: natListUpTo n

theorem mem_natListUpTo_of_le :
    forall {n N : Nat}, n <= N -> List.Mem n (natListUpTo N)
  | n, 0, h => by
      have hn : n = 0 := by omega
      subst hn
      exact List.Mem.head []
  | n, N + 1, h => by
      by_cases hn : n = N + 1
      · subst hn
        exact List.Mem.head _
      · have hnle : n <= N := by omega
        exact List.Mem.tail _ (mem_natListUpTo_of_le hnle)

/-- The first `N + 1` values of a choosing function, most recent first:
the finite list of cover members the proof offers as its subcover. -/
def indexList {iota : Type u} (choose : Nat -> iota) :
    Nat -> List iota
  | 0 => [choose 0]
  | n + 1 => choose (n + 1) :: indexList choose n

theorem mem_indexList_of_le {iota : Type u}
    (choose : Nat -> iota) :
    forall {n N : Nat}, n <= N -> List.Mem (choose n) (indexList choose N)
  | n, 0, h => by
      have hn : n = 0 := by omega
      subst hn
      exact List.Mem.head []
  | n, N + 1, h => by
      by_cases hn : n = N + 1
      · subst hn
        exact List.Mem.head _
      · have hnle : n <= N := by omega
        exact List.Mem.tail _ (mem_indexList_of_le choose hnle)

theorem nat_le_nat_of_le {m n : Nat}
    (hmn : m <= n) :
    F.le (nat F m) (nat F n) :=
  Tautology.IsOrderedFieldBaseLike.nat_le_nat_of_le F hmn
theorem nat_mul_step_le_of_le {m n : Nat} {step : alpha}
    (hmn : m <= n) (hstep : F.le F.zero step) :
    F.le (F.mul (nat F m) step) (F.mul (nat F n) step) :=
  mul_le_mul_nonneg_right F (nat_le_nat_of_le F hmn) hstep

theorem nat_mul_step_succ (n : Nat) (step : alpha) :
    F.mul (nat F (n + 1)) step =
      F.add (F.mul (nat F n) step) step := by
  rw [nat_succ, F.add_mul, F.one_mul]

/-- The `n`-th point of the arithmetic grid anchored at `left` with the
given step. The grid is the scaffolding of the finite subcover: the
centres are clamped grid points, and the indices run up to the stage where
the grid overruns the interval. -/
def gridPoint (left step : alpha) (n : Nat) : alpha :=
  F.add left (F.mul (nat F n) step)

theorem gridPoint_zero (left step : alpha) :
    gridPoint F left step 0 = left := by
  unfold gridPoint
  rw [nat_zero, zero_mul F, F.add_zero]

theorem gridPoint_succ (left step : alpha) (n : Nat) :
    gridPoint F left step (n + 1) =
      F.add (gridPoint F left step n) step := by
  unfold gridPoint
  rw [nat_mul_step_succ]
  rw [<- F.add_assoc]

theorem left_le_gridPoint {left step : alpha} (n : Nat)
    (hstep : F.le F.zero step) :
    F.le left (gridPoint F left step n) := by
  unfold gridPoint
  have hprod : F.le F.zero (F.mul (nat F n) step) :=
    F.mul_nonneg (nat_nonneg F n) hstep
  have h := F.add_le_add_right hprod left
  rwa [F.zero_add, F.add_comm (F.mul (nat F n) step) left] at h

theorem gridPoint_le_of_step_le_sub {left step x : alpha} {n : Nat}
    (h : F.le (F.mul (nat F n) step) (F.sub x left)) :
    F.le (gridPoint F left step n) x := by
  unfold gridPoint
  have h' := F.add_le_add_right h left
  have hright : F.add (F.sub x left) left = x :=
    sub_add_cancel F x left
  have hleft :
      F.add (F.mul (nat F n) step) left =
        F.add left (F.mul (nat F n) step) := by
    rw [F.add_comm]
  rwa [hleft, hright] at h'

theorem sub_lt_nat_mul_step_of_lt_grid_succ
    {left step x : alpha} {n : Nat}
    (h : F.lt x (gridPoint F left step (n + 1))) :
    F.lt (F.sub x left) (F.mul (nat F (n + 1)) step) := by
  unfold gridPoint at h
  exact sub_lt_of_lt_add F h

theorem lt_grid_succ_of_sub_lt_nat_mul_step
    {left step x : alpha} {n : Nat}
    (h : F.lt (F.sub x left) (F.mul (nat F (n + 1)) step)) :
    F.lt x (gridPoint F left step (n + 1)) := by
  unfold gridPoint
  exact lt_add_of_sub_lt F h

theorem gridPoint_lt_gridPoint_succ {left step : alpha} {n : Nat}
    (hstep : F.lt F.zero step) :
    F.lt (gridPoint F left step n) (gridPoint F left step (n + 1)) := by
  rw [gridPoint_succ]
  have h := add_lt_add_left F hstep (gridPoint F left step n)
  rwa [F.add_zero] at h

theorem gridPoint_succ_lt_add_delta {left step delta : alpha} {n : Nat}
    (hstep_delta : F.lt step delta) :
    F.lt (gridPoint F left step (n + 1))
      (F.add (gridPoint F left step n) delta) := by
  rw [gridPoint_succ]
  exact add_lt_add_left F hstep_delta (gridPoint F left step n)

/-- Every point of the interval is within `delta` of a grid point that is
itself in the interval and has index at most `N`, provided `N` steps of
`delta / 2` overrun the interval's length. The least index whose next
grid point clears `x - left` is found with `Tautology.Nat.least`, which
is what keeps the index bounded. -/
theorem exists_grid_close {left right delta : alpha}
    (hdelta : F.lt F.zero delta)
    {N : Nat}
    (hN :
      F.lt (F.sub right left)
        (F.mul (nat F N) (half F delta)))
    {x : alpha}
    (hx : F.ClosedInterval left right x) :
    Exists
      (fun n : Nat =>
        And (n <= N)
          (And (F.ClosedInterval left right (gridPoint F left (half F delta) n))
            (F.lt (dist F x (gridPoint F left (half F delta) n)) delta))) := by
  let step := half F delta
  have hstep_pos : F.lt F.zero step := half_pos F hdelta
  have hstep_nonneg : F.le F.zero step := le_of_lt F hstep_pos
  have hstep_lt_delta : F.lt step delta := half_lt_self F hdelta
  have hx_sub_le_right :
      F.le (F.sub x left) (F.sub right left) :=
    sub_le_sub_of_le_of_le F hx.right (F.le_refl left)
  have hN_succ :
      F.lt (F.sub x left)
        (F.mul (nat F (N + 1)) step) := by
    have hN_le_succ :
        F.le (F.mul (nat F N) step)
          (F.mul (nat F (N + 1)) step) :=
      nat_mul_step_le_of_le F (Nat.le_succ N) hstep_nonneg
    exact lt_of_le_of_lt F hx_sub_le_right
      (lt_of_lt_of_le F hN hN_le_succ)
  let P : Nat -> Prop :=
    fun k => F.lt (F.sub x left) (F.mul (nat F (k + 1)) step)
  have hP_exists : Exists P :=
    Exists.intro N hN_succ
  let k0 := Tautology.Nat.least P hP_exists
  have hkP : P k0 :=
    Tautology.Nat.least_spec P hP_exists
  have hk_le_N : k0 <= N :=
    Tautology.Nat.least_min P hP_exists hN_succ
  have hx_lt_grid_succ :
      F.lt x (gridPoint F left step (k0 + 1)) :=
    lt_grid_succ_of_sub_lt_nat_mul_step F hkP
  have hgrid_le_x : F.le (gridPoint F left step k0) x := by
    cases hkcase : k0 with
    | zero =>
        rw [gridPoint_zero]
        exact hx.left
    | succ k' =>
        have hnot_prev : Not (P k') := by
          intro hp
          have hself : k' + 1 <= k' := by
            have hmin := Tautology.Nat.least_min P hP_exists hp
            change Tautology.Nat.least P hP_exists = k' + 1 at hkcase
            rw [hkcase] at hmin
            exact hmin
          omega
        have hle_sub :
            F.le (F.mul (nat F (k' + 1)) step) (F.sub x left) :=
          le_of_not_lt F hnot_prev
        exact gridPoint_le_of_step_le_sub F hle_sub
  have hgrid_interval :
      F.ClosedInterval left right (gridPoint F left step k0) :=
    And.intro
      (left_le_gridPoint F k0 hstep_nonneg)
      (F.le_trans hgrid_le_x hx.right)
  have hright_close :
      F.lt x (F.add (gridPoint F left step k0) delta) := by
    exact lt_trans F hx_lt_grid_succ
      (gridPoint_succ_lt_add_delta F hstep_lt_delta)
  have hleft_close :
      F.lt (F.sub (gridPoint F left step k0) delta) x := by
    have hbelow :
        F.lt (F.sub (gridPoint F left step k0) delta)
          (gridPoint F left step k0) :=
      sub_lt_self_of_pos F hdelta
    exact lt_of_lt_of_le F hbelow hgrid_le_x
  have hdist :
      F.lt (dist F x (gridPoint F left step k0)) delta := by
    unfold dist
    exact abs_sub_lt_of_bounds F hleft_close hright_close
  exact Exists.intro k0 (And.intro hk_le_N
    (And.intro hgrid_interval hdist))

/-- The grid point clamped back to `right`. Centres must lie in the
interval for the Lebesgue property to apply to them, including at indices
whose grid point has already run past the right endpoint. -/
noncomputable def chosenCenter
    (left right step : alpha) (n : Nat) : alpha := by
  classical
  exact
    if F.le (gridPoint F left step n) right then
      gridPoint F left step n
    else
      right

theorem chosenCenter_of_grid_le
    {left right step : alpha} {n : Nat}
    (hn : F.le (gridPoint F left step n) right) :
    chosenCenter F left right step n =
      gridPoint F left step n := by
  unfold chosenCenter
  simp [hn]

theorem chosenCenter_mem
    {left right step : alpha} {n : Nat}
    (hle : F.le left right)
    (hstep : F.le F.zero step) :
    F.ClosedInterval left right
      (chosenCenter F left right step n) := by
  unfold chosenCenter
  by_cases hn : F.le (gridPoint F left step n) right
  · simp [hn]
    exact And.intro (left_le_gridPoint F n hstep) hn
  · simp [hn]
    exact And.intro hle (F.le_refl right)

/-- The edge as a principle: halve the Lebesgue number into a grid step,
take `N` from the linear Archimedean principle so that `N` steps overrun
the interval, let every clamped grid centre choose the member its
Lebesgue ball forces, and read the finite subcover off the first `N + 1`
choices. -/
theorem compactnessPrinciple
    (harch : LinearArchimedeanPrinciple F)
    (hleb : ClosedIntervalLebesguePrinciple.{u} F) :
    ClosedIntervalCompactnessPrinciple.{u} F where
  finite_subcover := by
    intro iota left right U hle hopen hcover
    cases hleb.lebesgue_number left right U hle hopen hcover with
    | intro delta hdelta =>
        let step := half F delta
        have hstep_pos : F.lt F.zero step :=
          half_pos F hdelta.left
        have hstep_nonneg : F.le F.zero step :=
          le_of_lt F hstep_pos
        have hlength_nonneg : F.le F.zero (F.sub right left) :=
          sub_nonneg_of_le F hle
        cases harch.large_nat_mul hlength_nonneg hstep_pos with
        | intro N hN =>
            let center : Nat -> alpha :=
              fun n => chosenCenter F left right step n
            have hcenter_mem :
                forall n : Nat, F.ClosedInterval left right (center n) := by
              intro n
              exact chosenCenter_mem F hle hstep_nonneg
            let choose : Nat -> iota :=
              fun n => Classical.choose
                (hdelta.right (center n) (hcenter_mem n))
            have choose_spec :
                forall n : Nat,
                  forall y : alpha,
                    F.ClosedInterval left right y ->
                      F.lt (dist F y (center n)) delta ->
                        U (choose n) y := by
              intro n
              exact Classical.choose_spec
                (hdelta.right (center n) (hcenter_mem n))
            refine Exists.intro (indexList choose N) ?_
            intro x hx
            cases exists_grid_close F hdelta.left hN hx with
            | intro k hk =>
                refine Exists.intro (choose k) ?_
                constructor
                · exact mem_indexList_of_le choose hk.left
                · have hcenter_eq :
                      center k = gridPoint F left step k := by
                    exact chosenCenter_of_grid_le F hk.right.left.right
                  have hdist :
                      F.lt (dist F x (center k)) delta := by
                    rw [hcenter_eq]
                    exact hk.right.right
                  exact choose_spec k x hx hdist

/-- The exported edge `LebesgueToFiniteSubcover`, linear Archimedean
hypothesis included; `ClosedInterval.Selected` consumes it, and the
bounded-variation covering engine of `RealDerivative` consumes this
file's grid vocabulary. -/
theorem target : Target.{u} F := by
  intro harch hleb
  exact compactnessPrinciple F harch hleb

end LebesgueToFinite
end Compactness
end IsOrderedFieldBaseLike
end Tautology
