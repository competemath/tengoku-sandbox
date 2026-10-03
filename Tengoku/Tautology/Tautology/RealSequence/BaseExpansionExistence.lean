import Tengoku.Tautology.Tautology.Nat.Least
import Tengoku.Tautology.Tautology.RealSequence.BaseExpansionDigits

/-!
# Constructing the digits

Two parallel machines that extract a digit stream from a number by bisecting
the unit interval into `q` children, plus the envelope apparatus that makes
uniqueness provable.

## The two machines, and why their names mislead

`greedyDigit` takes the *smallest* digit whose child interval still reaches
`x`, working bottom-up; boundary points fall into the lower child, so the
stream may trail off in maximal digits -- one half becomes `0.4999...` in base
ten. `canonicalDigit` takes the *largest* digit whose child interval starts at
or below `x`, working top-down; boundary points fall into the upper child and
the stream terminates -- one half becomes `0.5000...`.

So the machine called greedy is not the one that grabs the largest digit. That
is the canonical one, and its maximality is exactly what
`canonicalDigit_maximal` records. Guessing the direction from the names gets it
backwards.

Both maintain the same bisection invariant -- the truncation is below `x`, and
`x` is below the truncation plus one tail -- and both converge by squeezing
that tail to zero.

## Three theorems, three prices

Existence of an expansion, existence of a canonical one, and uniqueness of the
canonical one are proved here, and they cost different things. Neither
existence theorem uses completeness at all: they consume only an
`InvNatArchimedeanPrinciple`. Uniqueness consumes nothing beyond
ordered-field structure. This is the constructive counterpart of the abstract
route in `Tautology.RealSequence.BaseExpansionDigits`, which reaches existence
from monotone convergence instead.

The domains differ too, and the difference is real rather than cosmetic:
ordinary existence allows `x = 1`, where the only expansion is the all-maximal
one, while canonical existence requires `x < 1`, since canonicity is precisely
what rules that stream out.

## The envelope

A truncation plus a whole remaining tail is an upper fence for any expansion
with that prefix. Every expansion's value stays at or below every envelope; a
canonical expansion's value stays strictly below. Comparing at the first digit
where two streams differ is what closes uniqueness, and the same bracket --
truncation below, envelope above -- is what
`Tautology.RealNegligibility.CantorSet` reads its cylinder endpoints off.

## Position and role

Implementation module, the top of the expansion cluster.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- Left endpoint of the `digit`-th child of the parent interval
`[approx, approx + 1 / q ^ place]`: the parent's left endpoint advanced
by `digit` child-widths of `1 / q ^ (place + 1)`. -/
noncomputable def baseChildLeft
    (q : Nat) (approx : alpha) (place digit : Nat) : alpha :=
  F.add approx
    (F.mul (nat F digit) (baseTail F q (place + 1)))

/-- Right endpoint of the `digit`-th child: the parent's left endpoint
advanced by `digit + 1` child-widths, so this is simultaneously the left
endpoint of child `digit + 1` (`baseChildRight_eq_next_left`). Over
`digit = 0, ..., q - 1` the children therefore tile the parent without
gaps or overlaps: child `0` starts at `approx` (`baseChildLeft_zero`)
and child `q - 1` ends at `approx + 1 / q ^ place`
(`baseChildRight_max_eq_add_tail`). -/
noncomputable def baseChildRight
    (q : Nat) (approx : alpha) (place digit : Nat) : alpha :=
  F.add approx
    (F.mul (nat F (digit + 1)) (baseTail F q (place + 1)))

theorem baseChildLeft_zero
    (q : Nat) (approx : alpha) (place : Nat) :
    baseChildLeft F q approx place 0 = approx := by
  unfold baseChildLeft
  rw [nat_zero, zero_mul F, F.add_zero]

theorem baseChildRight_eq_next_left
    (q : Nat) (approx : alpha) (place digit : Nat) :
    baseChildRight F q approx place digit =
      baseChildLeft F q approx place (digit + 1) := by
  rfl

theorem baseChildLeft_eq_add_weighted
    (q : Nat) (approx : alpha) (place digit : Nat) :
    baseChildLeft F q approx place digit =
      F.add approx (baseWeightedDigit F q digit place) := by
  rfl

theorem baseChildRight_max_eq_add_tail
    {q : Nat} (hq : ValidBase q)
    (approx : alpha) (place : Nat) :
    baseChildRight F q approx place (q - 1) =
      F.add approx (baseTail F q place) := by
  unfold baseChildRight
  have hsucc : q - 1 + 1 = q := by
    unfold ValidBase at hq
    omega
  rw [hsucc]
  rw [baseTail_eq_mul_baseTail_succ F hq place]

theorem baseChildRight_eq_left_add_tail
    (q : Nat) (approx : alpha) (place digit : Nat) :
    baseChildRight F q approx place digit =
      F.add (baseChildLeft F q approx place digit)
        (baseTail F q (place + 1)) := by
  unfold baseChildRight baseChildLeft
  rw [nat_succ]
  rw [F.add_mul, F.one_mul]
  rw [<- F.add_assoc]

/-- The greedy digit at `place`: the least digit `d` with `x` at or
below the right endpoint of child `d`, found by bounded search
(`Nat.firstAux`, up to `q - 1`). This bottom-up choice takes the lower
child of a boundary point -- a value with two expansions -- which is
why the greedy stream may end in repeating maxima, `0.4999...` for
`1 / 2` in base `10`. The two halves of its spec live separately, as
`greedyDigit_spec_of_right_bound` and `greedyDigit_left_bound`; when
the digit is positive the left inequality is strict. -/
noncomputable def greedyDigit
    (q : Nat) (x approx : alpha) (place : Nat) : Nat := by
  classical
  exact
    Tautology.Nat.firstAux
      (fun digit : Nat =>
        F.le x (baseChildRight F q approx place digit))
      (q - 1)

theorem greedyDigit_le_max
    (q : Nat) (x approx : alpha) (place : Nat) :
    greedyDigit F q x approx place <= q - 1 := by
  unfold greedyDigit
  classical
  exact Tautology.Nat.firstAux_le
    (fun digit : Nat =>
      F.le x (baseChildRight F q approx place digit))
    (q - 1)

theorem greedyDigit_is_digit {q : Nat}
    (hq : ValidBase q) (x approx : alpha) (place : Nat) :
    BaseDigit q (greedyDigit F q x approx place) := by
  unfold BaseDigit
  have hle := greedyDigit_le_max F q x approx place
  unfold ValidBase at hq
  omega

theorem greedyDigit_spec_of_right_bound {q : Nat}
    (hq : ValidBase q) {x approx : alpha} {place : Nat}
    (hright : F.le x (F.add approx (baseTail F q place))) :
    F.le x
      (baseChildRight F q approx place
        (greedyDigit F q x approx place)) := by
  unfold greedyDigit
  classical
  exact Tautology.Nat.firstAux_spec_of_exists
    (fun digit : Nat =>
      F.le x (baseChildRight F q approx place digit))
    (Exists.intro (q - 1)
      (And.intro (Nat.le_refl (q - 1)) (by
        change F.le x (baseChildRight F q approx place (q - 1))
        rwa [baseChildRight_max_eq_add_tail F hq approx place])))

theorem greedyDigit_minimal {q : Nat}
    {x approx : alpha} {place k : Nat}
    (hkmax : k <= q - 1)
    (hk : F.le x (baseChildRight F q approx place k)) :
    greedyDigit F q x approx place <= k := by
  unfold greedyDigit
  classical
  exact Tautology.Nat.firstAux_min
    (fun digit : Nat =>
      F.le x (baseChildRight F q approx place digit))
    (n := q - 1)
    (k := k)
    hkmax
    hk

theorem greedyDigit_left_bound {q : Nat}
    {x approx : alpha} {place : Nat}
    (hleft : F.le approx x) :
    F.le
      (baseChildLeft F q approx place
        (greedyDigit F q x approx place))
      x := by
  let d := greedyDigit F q x approx place
  by_cases hd0 : d = 0
  case pos =>
    rw [show baseChildLeft F q approx place d = approx by
      rw [hd0, baseChildLeft_zero]]
    exact hleft
  case neg =>
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    let k := d - 1
    have hk_succ : k + 1 = d := by
      dsimp [k]
      omega
    have hnot :
        Not (F.le x (baseChildRight F q approx place k)) := by
      intro hkprop
      have hkmax : k <= q - 1 := by
        have hdmax : d <= q - 1 := by
          dsimp [d]
          exact greedyDigit_le_max F q x approx place
        dsimp [k]
        omega
      have hmin :
          d <= k := by
        dsimp [d]
        exact greedyDigit_minimal F hkmax hkprop
      omega
    have hnot_left :
        Not (F.le x (baseChildLeft F q approx place d)) := by
      intro hxleft
      apply hnot
      rwa [baseChildRight_eq_next_left F q approx place k, hk_succ]
    cases F.le_total (baseChildLeft F q approx place d) x with
    | inl h => exact h
    | inr hxleft => exact False.elim (hnot_left hxleft)

/-- What one greedy step must deliver, bundled: the chosen digit is
genuine, its child's left endpoint lies at or below `x`, and `x` lies at
or below that child's right endpoint. The two inequalities are the two
halves of the running invariant, restated one stage later. -/
structure GreedyStepBounds
    (q : Nat) (x approx : alpha) (place : Nat) : Prop where
  digit : BaseDigit q (greedyDigit F q x approx place)
  left :
    F.le
      (baseChildLeft F q approx place
        (greedyDigit F q x approx place))
      x
  right :
    F.le x
      (baseChildRight F q approx place
        (greedyDigit F q x approx place))

/-- The greedy step discharges its bundled bounds whenever `x` lies in
the parent interval `[approx, approx + 1 / q ^ place]`: read against
`greedyInvariant`, the hypotheses `hleft` and `hright` are exactly the
invariant at the parent stage. -/
theorem greedyStepBounds {q : Nat}
    (hq : ValidBase q) {x approx : alpha} {place : Nat}
    (hleft : F.le approx x)
    (hright : F.le x (F.add approx (baseTail F q place))) :
    GreedyStepBounds F q x approx place where
  digit := greedyDigit_is_digit F hq x approx place
  left := greedyDigit_left_bound F hleft
  right := greedyDigit_spec_of_right_bound F hq hright

/-- The greedy approximants to `x`: start at zero and repeatedly step
into the greedy child of the current approximation. These are defined as
child endpoints, not as digit sums -- the coincidence with digit sums is
`greedyPartial_eq_baseExpansionPartial`. -/
noncomputable def greedyPartial
    (q : Nat) (x : alpha) : Nat -> alpha
  | 0 => F.zero
  | n + 1 =>
      baseChildLeft F q (greedyPartial q x n) n
        (greedyDigit F q x (greedyPartial q x n) n)

/-- The digit stream the greedy walk emits: the digit chosen at stage
`n` from the approximation `greedyPartial q x n`. These are the digits
that `greedy_hasBaseExpansion` certifies as an expansion of `x`. -/
noncomputable def greedyDigits
    (q : Nat) (x : alpha) (n : Nat) : Nat :=
  greedyDigit F q x (greedyPartial F q x n) n

theorem greedyPartial_zero
    (q : Nat) (x : alpha) :
    greedyPartial F q x 0 = F.zero := by
  rfl

theorem greedyPartial_succ
    (q : Nat) (x : alpha) (n : Nat) :
    greedyPartial F q x (n + 1) =
      baseChildLeft F q (greedyPartial F q x n) n
        (greedyDigits F q x n) := by
  rfl

theorem greedyDigits_digitStream {q : Nat}
    (hq : ValidBase q) (x : alpha) :
    BaseDigitStream q (greedyDigits F q x) := by
  intro n
  unfold greedyDigits
  exact greedyDigit_is_digit F hq x (greedyPartial F q x n) n

/-- The greedy approximants are digit sums after all: the `n`-th
approximant equals the `n`-th truncation of the emitted digits. This is
the bridge that turns the child-stepping construction into an expansion
in the sense of `HasBaseExpansion`. -/
theorem greedyPartial_eq_baseExpansionPartial
    (q : Nat) (x : alpha) :
    forall n : Nat,
      greedyPartial F q x n =
        baseExpansionPartial F q (greedyDigits F q x) n := by
  intro n
  induction n with
  | zero =>
      rw [greedyPartial_zero, baseExpansionPartial_zero]
  | succ n ih =>
      rw [greedyPartial_succ, baseExpansionPartial_succ, <- ih]
      rw [baseChildLeft_eq_add_weighted]

/-- The bisection invariant of the greedy walk, at every stage: the
approximant sits at or below `x`, and `x` sits at or below the
approximant plus the current tail `1 / q ^ n`. Squeezing between these
two bounds with a tail that tends to zero is what proves convergence,
in `greedyPartial_tendsto`. -/
theorem greedyInvariant {q : Nat}
    (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    forall n : Nat,
      And
        (F.le (greedyPartial F q x n) x)
        (F.le x
          (F.add (greedyPartial F q x n) (baseTail F q n))) := by
  intro n
  induction n with
  | zero =>
      constructor
      · rw [greedyPartial_zero]
        exact hx0
      · rw [greedyPartial_zero, baseTail_zero, F.zero_add]
        exact hx1
  | succ n ih =>
      have hstep :
          GreedyStepBounds F q x (greedyPartial F q x n) n :=
        greedyStepBounds F hq ih.left ih.right
      constructor
      · rw [greedyPartial_succ]
        exact hstep.left
      · have hright := hstep.right
        rw [baseChildRight_eq_left_add_tail] at hright
        change
          F.le x
            (F.add
              (baseChildLeft F q (greedyPartial F q x n) n
                (greedyDigit F q x (greedyPartial F q x n) n))
              (baseTail F q (n + 1)))
        exact hright

theorem greedyPartial_lower_bound {q : Nat}
    {x : alpha} {n : Nat}
    (h :
      F.le x
        (F.add (greedyPartial F q x n) (baseTail F q n))) :
    F.le
      (F.sub x (baseTail F q n))
      (greedyPartial F q x n) := by
  have hshift :=
    F.add_le_add_right h (F.neg (baseTail F q n))
  rwa [<- F.sub_eq_add_neg x (baseTail F q n),
    add_neg_cancel_right F (greedyPartial F q x n) (baseTail F q n)]
    at hshift

theorem sub_le_of_le_add {x p t : alpha}
    (h : F.le x (F.add p t)) :
    F.le (F.sub x t) p := by
  have hshift := F.add_le_add_right h (F.neg t)
  rwa [<- F.sub_eq_add_neg x t, add_neg_cancel_right F p t]
    at hshift

/-- The tails `1 / q ^ n` tend to zero, stated without index shift --
this, rather than the shifted `baseTail_tendsto_zero` of
`Tautology.RealSequence.BaseExpansion`, is the form the rest of the library
quotes. The inverse-natural Archimedean principle rides as an explicit
hypothesis, and it is needed: a positive `eps` bounding every
`1 / (n + 1)` from below bounds every `1 / q ^ n` as well, `q ^ n`
being one of the naturals. -/
theorem baseTail_tendsto_zero_all
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) :
    SeqTendsto F (fun n : Nat => baseTail F q n) F.zero := by
  intro eps heps
  cases A.small_inv_succ heps with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      let qpow := q ^ n
      have hN_le_qpow : N + 1 <= qpow := by
        have hNn : N + 1 <= n + 1 := Nat.succ_le_succ hn
        have hpow : n + 1 <= q ^ n :=
          nat_succ_le_pow_of_one_lt hq n
        exact Nat.le_trans hNn hpow
      have hqpow_ne : Not (qpow = 0) := by
        intro hzero
        have hbad : N + 1 <= 0 := by
          rwa [hzero] at hN_le_qpow
        omega
      have hNpos : F.lt F.zero (nat F (N + 1)) :=
        nat_succ_pos F N
      have hqpow_pos : F.lt F.zero (nat F qpow) :=
        nat_pos_of_ne_zero F hqpow_ne
      have hle_nat :
          F.le (nat F (N + 1)) (nat F qpow) :=
        nat_le_nat_of_le F hN_le_qpow
      have hle_inv :
          F.le (F.inv (nat F qpow)) (F.inv (nat F (N + 1))) :=
        inv_le_inv_of_le_pos F hNpos hqpow_pos hle_nat
      have hinv_pos : F.lt F.zero (F.inv (nat F qpow)) :=
        inv_pos F hqpow_pos
      have habs :
          abs F (F.sub (baseTail F q n) F.zero) =
            F.inv (nat F qpow) := by
        unfold baseTail basePow
        dsimp [qpow]
        rw [sub_zero F]
        exact abs_of_nonneg F (le_of_lt F hinv_pos)
      rw [habs]
      exact lt_of_le_of_lt F hle_inv hN

/-- The greedy approximants converge to `x`, by a pure squeeze:
`x - 1 / q ^ n` tends to `x` from below, the invariant pins the
approximants between that sequence and `x`, and the only principle
consumed on the way is the inverse-natural Archimedean one. The
construction supplies its own limit candidate, so no completeness
enters. -/
theorem greedyPartial_tendsto {q : Nat}
    (A : F.InvNatArchimedeanPrinciple)
    (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    SeqTendsto F (greedyPartial F q x) x := by
  have hinv := greedyInvariant F hq hx0 hx1
  have htail : SeqTendsto F (fun n : Nat => baseTail F q n) F.zero :=
    baseTail_tendsto_zero_all F A hq
  have hconst : SeqTendsto F (fun _ : Nat => x) x :=
    seqTendsto_const F x
  have hlower :
      SeqTendsto F
        (fun n : Nat => F.sub x (baseTail F q n)) x := by
    have hsub :=
      seqTendsto_sub F hconst htail
    change
      SeqTendsto F
        (fun n : Nat => F.sub x (baseTail F q n))
        (F.sub x F.zero) at hsub
    rwa [sub_zero F] at hsub
  apply seqTendsto_of_squeeze F hlower hconst
  · apply Eventually.of_forall
    intro n
    exact sub_le_of_le_add F (hinv n).right
  · apply Eventually.of_forall
    intro n
    exact (hinv n).left

theorem greedy_hasBaseExpansion
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q)
    {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    HasBaseExpansion F q x (greedyDigits F q x) := by
  refine And.intro hq ?_
  refine And.intro (greedyDigits_digitStream F hq x) ?_
  have hpartial :
      SeqTendsto F
        (baseExpansionPartial F q (greedyDigits F q x)) x := by
    have hgreedy := greedyPartial_tendsto F A hq hx0 hx1
    have heq :
        (fun n : Nat =>
          baseExpansionPartial F q (greedyDigits F q x) n) =
          greedyPartial F q x := by
      funext n
      exact (greedyPartial_eq_baseExpansionPartial F q x n).symm
    change
      SeqTendsto F
        (fun n : Nat =>
          baseExpansionPartial F q (greedyDigits F q x) n)
        x
    rwa [heq]
  exact hpartial

/-- Every point of the closed unit interval has a base-`q` expansion,
witnessed by the greedy digits. Note what the proof never touches:
completeness. The abstract route through
`baseExpansionPartial_converges` and the monotone convergence principle
is available but costlier than the greedy squeeze, which needs only the
inverse-natural Archimedean principle. -/
theorem baseExpansion_exists
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) :
    BaseExpansionExistenceStatement F q := by
  intro x hx0 hx1
  exact Exists.intro (greedyDigits F q x)
    (greedy_hasBaseExpansion F A hq hx0 hx1)

/-- The countdown behind the canonical digit: the least number of steps
`rev` by which the top digit must be lowered before the left endpoint
of child `q - 1 - rev` lies at or below `x`, again by bounded search up
to `q - 1`. -/
noncomputable def canonicalRev
    (q : Nat) (x approx : alpha) (place : Nat) : Nat := by
  classical
  exact
    Tautology.Nat.firstAux
      (fun rev : Nat =>
        F.le
          (baseChildLeft F q approx place (q - 1 - rev))
          x)
      (q - 1)

/-- The canonical digit at `place`: the greatest digit whose child's
left endpoint lies at or below `x` -- the greedy digit read from the top
of the alphabet down instead of up from zero. On a boundary point this
takes the upper child, so the stream terminates where the greedy one
would end in repeating maxima: `1 / 2` in base `10` becomes `0.5000...`
here against `0.4999...` under `greedyDigits`. -/
noncomputable def canonicalDigit
    (q : Nat) (x approx : alpha) (place : Nat) : Nat :=
  q - 1 - canonicalRev F q x approx place

theorem canonicalRev_le_max
    (q : Nat) (x approx : alpha) (place : Nat) :
    canonicalRev F q x approx place <= q - 1 := by
  unfold canonicalRev
  classical
  exact Tautology.Nat.firstAux_le
    (fun rev : Nat =>
      F.le
        (baseChildLeft F q approx place (q - 1 - rev))
        x)
    (q - 1)

theorem canonicalDigit_le_max
    (q : Nat) (x approx : alpha) (place : Nat) :
    canonicalDigit F q x approx place <= q - 1 := by
  unfold canonicalDigit
  exact Nat.sub_le (q - 1) (canonicalRev F q x approx place)

theorem canonicalDigit_is_digit {q : Nat}
    (hq : ValidBase q) (x approx : alpha) (place : Nat) :
    BaseDigit q (canonicalDigit F q x approx place) := by
  unfold BaseDigit
  have hle := canonicalDigit_le_max F q x approx place
  unfold ValidBase at hq
  omega

theorem canonicalDigit_left_spec {q : Nat}
    {x approx : alpha} {place : Nat}
    (hleft : F.le approx x) :
    F.le
      (baseChildLeft F q approx place
        (canonicalDigit F q x approx place))
      x := by
  unfold canonicalDigit
  unfold canonicalRev
  classical
  have hspec :=
    Tautology.Nat.firstAux_spec_of_exists
      (fun rev : Nat =>
        F.le
          (baseChildLeft F q approx place (q - 1 - rev))
          x)
      (Exists.intro (q - 1)
        (And.intro (Nat.le_refl (q - 1)) (by
          have hzero : q - 1 - (q - 1) = 0 := Nat.sub_self (q - 1)
          change F.le (baseChildLeft F q approx place (q - 1 - (q - 1))) x
          rwa [hzero, baseChildLeft_zero F q approx place])))
  exact hspec

/-- Maximality, the property the whole canonical machinery runs on: any
digit `k` whose child's left endpoint lies at or below `x` is at most
the digit chosen. Together with `canonicalDigit_left_spec` this says the
canonical digit is the greatest digit that fits, not merely a fitting
one. -/
theorem canonicalDigit_maximal {q : Nat}
    {x approx : alpha} {place k : Nat}
    (hkmax : k <= q - 1)
    (hk : F.le (baseChildLeft F q approx place k) x) :
    k <= canonicalDigit F q x approx place := by
  let r := q - 1 - k
  have hrmax : r <= q - 1 := by
    dsimp [r]
    omega
  have hpred :
      F.le
        (baseChildLeft F q approx place (q - 1 - r))
        x := by
    have hqr : q - 1 - r = k := by
      dsimp [r]
      omega
    rwa [hqr]
  unfold canonicalDigit
  unfold canonicalRev
  classical
  have hmin :
      Tautology.Nat.firstAux
        (fun rev : Nat =>
          F.le
            (baseChildLeft F q approx place (q - 1 - rev))
            x)
        (q - 1) <= r :=
    Tautology.Nat.firstAux_min
      (fun rev : Nat =>
        F.le
          (baseChildLeft F q approx place (q - 1 - rev))
          x)
      (n := q - 1)
      (k := r)
      hrmax
      hpred
  omega

theorem canonicalDigit_right_bound {q : Nat}
    (hq : ValidBase q) {x approx : alpha} {place : Nat}
    (hright : F.le x (F.add approx (baseTail F q place))) :
    F.le x
      (baseChildRight F q approx place
        (canonicalDigit F q x approx place)) := by
  let d := canonicalDigit F q x approx place
  have hdmax : d <= q - 1 := by
    dsimp [d]
    exact canonicalDigit_le_max F q x approx place
  by_cases hdtop : d = q - 1
  case pos =>
    rw [show
      baseChildRight F q approx place d =
        F.add approx (baseTail F q place) by
      rw [hdtop, baseChildRight_max_eq_add_tail F hq approx place]]
    exact hright
  case neg =>
    have hdnext : d + 1 <= q - 1 := by
      omega
    have hnot :
        Not (F.le
          (baseChildLeft F q approx place (d + 1)) x) := by
      intro hnext
      have hmax :
          d + 1 <= d := by
        dsimp [d]
        exact canonicalDigit_maximal F hdnext hnext
      omega
    have hxle :
        F.le x (baseChildLeft F q approx place (d + 1)) := by
      cases F.le_total x (baseChildLeft F q approx place (d + 1)) with
      | inl hx => exact hx
      | inr hleftnext => exact False.elim (hnot hleftnext)
    rwa [<- baseChildRight_eq_next_left F q approx place d] at hxle

/-- What one canonical step must deliver, mirroring `GreedyStepBounds`:
the digit is genuine, its child's left endpoint lies at or below `x`,
and `x` lies at or below that child's right endpoint. -/
structure CanonicalStepBounds
    (q : Nat) (x approx : alpha) (place : Nat) : Prop where
  digit : BaseDigit q (canonicalDigit F q x approx place)
  left :
    F.le
      (baseChildLeft F q approx place
        (canonicalDigit F q x approx place))
      x
  right :
    F.le x
      (baseChildRight F q approx place
        (canonicalDigit F q x approx place))

/-- The canonical step discharges its bundled bounds whenever `x` lies
in the parent interval. The left inequality needs only `hleft`; it is
the right one that uses the parent's upper end. -/
theorem canonicalStepBounds {q : Nat}
    (hq : ValidBase q) {x approx : alpha} {place : Nat}
    (hleft : F.le approx x)
    (hright : F.le x (F.add approx (baseTail F q place))) :
    CanonicalStepBounds F q x approx place where
  digit := canonicalDigit_is_digit F hq x approx place
  left := canonicalDigit_left_spec F hleft
  right := canonicalDigit_right_bound F hq hright

/-- The canonical approximants to `x`: start at zero and repeatedly step
into the canonical child of the current approximation, exactly as
`greedyPartial` does with the other digit rule. -/
noncomputable def canonicalPartial
    (q : Nat) (x : alpha) : Nat -> alpha
  | 0 => F.zero
  | n + 1 =>
      baseChildLeft F q (canonicalPartial q x n) n
        (canonicalDigit F q x (canonicalPartial q x n) n)

/-- The digit stream the canonical walk emits: the digit chosen at stage
`n` from the approximation `canonicalPartial q x n`. Where the two walks
disagree -- the boundary points -- this one has taken the upper child
and will settle to zeros where `greedyDigits` runs on maxima. -/
noncomputable def canonicalDigits
    (q : Nat) (x : alpha) (n : Nat) : Nat :=
  canonicalDigit F q x (canonicalPartial F q x n) n

theorem canonicalPartial_zero
    (q : Nat) (x : alpha) :
    canonicalPartial F q x 0 = F.zero := by
  rfl

theorem canonicalPartial_succ
    (q : Nat) (x : alpha) (n : Nat) :
    canonicalPartial F q x (n + 1) =
      baseChildLeft F q (canonicalPartial F q x n) n
        (canonicalDigits F q x n) := by
  rfl

theorem canonicalDigits_digitStream {q : Nat}
    (hq : ValidBase q) (x : alpha) :
    BaseDigitStream q (canonicalDigits F q x) := by
  intro n
  unfold canonicalDigits
  exact canonicalDigit_is_digit F hq x (canonicalPartial F q x n) n

/-- The canonical approximants are the truncations of the canonical
digits -- the same bridge as
`greedyPartial_eq_baseExpansionPartial`, crossed by the top-down walk. -/
theorem canonicalPartial_eq_baseExpansionPartial
    (q : Nat) (x : alpha) :
    forall n : Nat,
      canonicalPartial F q x n =
        baseExpansionPartial F q (canonicalDigits F q x) n := by
  intro n
  induction n with
  | zero =>
      rw [canonicalPartial_zero, baseExpansionPartial_zero]
  | succ n ih =>
      rw [canonicalPartial_succ, baseExpansionPartial_succ, <- ih]
      rw [baseChildLeft_eq_add_weighted]

/-- The bisection invariant of the canonical walk, identical in form to
`greedyInvariant`: the approximant sits at or below `x`, and `x` at or
below the approximant plus the tail `1 / q ^ n`. The two walks differ
only in which child they enter at each stage. -/
theorem canonicalInvariant {q : Nat}
    (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    forall n : Nat,
      And
        (F.le (canonicalPartial F q x n) x)
        (F.le x
          (F.add (canonicalPartial F q x n) (baseTail F q n))) := by
  intro n
  induction n with
  | zero =>
      constructor
      · rw [canonicalPartial_zero]
        exact hx0
      · rw [canonicalPartial_zero, baseTail_zero, F.zero_add]
        exact hx1
  | succ n ih =>
      have hstep :
          CanonicalStepBounds F q x (canonicalPartial F q x n) n :=
        canonicalStepBounds F hq ih.left ih.right
      constructor
      · rw [canonicalPartial_succ]
        exact hstep.left
      · have hright := hstep.right
        rw [baseChildRight_eq_left_add_tail] at hright
        change
          F.le x
            (F.add
              (baseChildLeft F q (canonicalPartial F q x n) n
                (canonicalDigit F q x (canonicalPartial F q x n) n))
              (baseTail F q (n + 1)))
        exact hright

/-- The canonical approximants converge to `x`, by the same squeeze and
with the same single hypothesis as `greedyPartial_tendsto`: the
inverse-natural Archimedean principle, nothing more. -/
theorem canonicalPartial_tendsto {q : Nat}
    (A : F.InvNatArchimedeanPrinciple)
    (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    SeqTendsto F (canonicalPartial F q x) x := by
  have hinv := canonicalInvariant F hq hx0 hx1
  have htail : SeqTendsto F (fun n : Nat => baseTail F q n) F.zero :=
    baseTail_tendsto_zero_all F A hq
  have hconst : SeqTendsto F (fun _ : Nat => x) x :=
    seqTendsto_const F x
  have hlower :
      SeqTendsto F
        (fun n : Nat => F.sub x (baseTail F q n)) x := by
    have hsub :=
      seqTendsto_sub F hconst htail
    change
      SeqTendsto F
        (fun n : Nat => F.sub x (baseTail F q n))
        (F.sub x F.zero) at hsub
    rwa [sub_zero F] at hsub
  apply seqTendsto_of_squeeze F hlower hconst
  · apply Eventually.of_forall
    intro n
    exact sub_le_of_le_add F (hinv n).right
  · apply Eventually.of_forall
    intro n
    exact (hinv n).left

theorem canonicalDigits_hasBaseExpansion
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q)
    {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one) :
    HasBaseExpansion F q x (canonicalDigits F q x) := by
  refine And.intro hq ?_
  refine And.intro (canonicalDigits_digitStream F hq x) ?_
  have hcanonical := canonicalPartial_tendsto F A hq hx0 hx1
  have heq :
      (fun n : Nat =>
        baseExpansionPartial F q (canonicalDigits F q x) n) =
        canonicalPartial F q x := by
    funext n
    exact (canonicalPartial_eq_baseExpansionPartial F q x n).symm
  change
    SeqTendsto F
      (fun n : Nat =>
        baseExpansionPartial F q (canonicalDigits F q x) n)
      x
  rwa [heq]

/-- Closed form for the canonical approximants once the digits are all
`q - 1` from `N` on: stage `N + k` equals the ceiling at `N` -- the
stage-`N` truncation plus the whole tail -- minus the remaining tail.
The all-max digits cancel against the tail stage by stage, so the
approximants climb the ceiling's last gap exactly. -/
theorem canonicalPartial_eq_ceiling_sub_tail_of_max_from
    {q : Nat} (hq : ValidBase q) {x : alpha} {N : Nat}
    (hmax :
      forall n : Nat,
        N <= n -> canonicalDigits F q x n = q - 1) :
    forall k : Nat,
      canonicalPartial F q x (N + k) =
        F.sub
          (F.add (canonicalPartial F q x N) (baseTail F q N))
          (baseTail F q (N + k)) := by
  intro k
  induction k with
  | zero =>
      rw [Nat.add_zero]
      rw [add_sub_cancel F (canonicalPartial F q x N) (baseTail F q N)]
  | succ k ih =>
      have hNk : N <= N + k := by omega
      rw [Nat.add_succ]
      rw [canonicalPartial_succ]
      rw [baseChildLeft_eq_add_weighted]
      rw [hmax (N + k) hNk]
      rw [baseWeightedMax_eq_tail_sub F hq]
      rw [ih]
      exact
        sub_add_sub_cancel F
          (F.add (canonicalPartial F q x N) (baseTail F q N))
          (baseTail F q (N + k))
          (baseTail F q (N + k + 1))

theorem canonicalTailMax_ceiling_le_value
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one)
    {N : Nat}
    (hmax :
      forall n : Nat,
        N <= n -> canonicalDigits F q x n = q - 1) :
    F.le
      (F.add (canonicalPartial F q x N) (baseTail F q N))
      x := by
  let ceiling :=
    F.add (canonicalPartial F q x N) (baseTail F q N)
  have htail : SeqTendsto F (fun n : Nat => baseTail F q n) F.zero :=
    baseTail_tendsto_zero_all F A hq
  have hconst : SeqTendsto F (fun _ : Nat => ceiling) ceiling :=
    seqTendsto_const F ceiling
  have hseq :
      SeqTendsto F
        (fun n : Nat => F.sub ceiling (baseTail F q n))
        ceiling := by
    have hsub := seqTendsto_sub F hconst htail
    change
      SeqTendsto F
        (fun n : Nat => F.sub ceiling (baseTail F q n))
        (F.sub ceiling F.zero) at hsub
    rwa [sub_zero F] at hsub
  have hpartial_le :
      Eventually
        (fun n : Nat =>
          F.le (F.sub ceiling (baseTail F q n)) x) := by
    refine Exists.intro N ?_
    intro n hn
    have hk : Exists (fun k : Nat => n = N + k) := by
      exact Exists.intro (n - N) (by omega)
    cases hk with
    | intro k hk =>
        rw [hk]
        rw [<- canonicalPartial_eq_ceiling_sub_tail_of_max_from
          F hq hmax k]
        exact (canonicalInvariant F hq hx0 hx1 (N + k)).left
  exact seqTendsto_le_of_eventually_le F
    hseq
    (seqTendsto_const F x)
    hpartial_le

/-- If the canonical digits are all `q - 1` from `N` on, then `x` equals
the ceiling there, truncation plus the whole tail: the invariant's upper
bound and the closed form's lower bound meet. This is the lever of
`canonicalDigits_not_eventuallyMax`, where at `N = 0` it forces
`x = 1`. -/
theorem canonicalTailMax_value_eq_ceiling
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x) (hx1 : F.le x F.one)
    {N : Nat}
    (hmax :
      forall n : Nat,
        N <= n -> canonicalDigits F q x n = q - 1) :
    x =
      F.add (canonicalPartial F q x N) (baseTail F q N) := by
  have hle_ceiling :
      F.le x
        (F.add (canonicalPartial F q x N) (baseTail F q N)) :=
    (canonicalInvariant F hq hx0 hx1 N).right
  have hceiling_le :
      F.le
        (F.add (canonicalPartial F q x N) (baseTail F q N))
        x :=
    canonicalTailMax_ceiling_le_value F A hq hx0 hx1 hmax
  exact F.le_antisymm hle_ceiling hceiling_le

/-- For `x < 1` the canonical digits never settle into the all-max tail.
The proof takes the least stage from which they would be maximal and kills the
two cases separately: `N = 0` forces `x = 1` by the ceiling theorem, while for
`N > 0` the digit just before `N` contradicts the
maximality of `canonicalDigit`. -/
theorem canonicalDigits_not_eventuallyMax
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x)
    (hxlt1 : F.lt x F.one) :
    Not (EventuallyMaxDigits q (canonicalDigits F q x)) := by
  intro hevent
  let P : Nat -> Prop :=
    fun N : Nat =>
      forall n : Nat,
        N <= n -> canonicalDigits F q x n = q - 1
  let N := Tautology.Nat.least P hevent
  have hN : P N := by
    dsimp [N]
    exact Tautology.Nat.least_spec P hevent
  have hNmin : forall k : Nat, P k -> N <= k := by
    intro k hk
    dsimp [N]
    exact Tautology.Nat.least_min P hevent hk
  by_cases hN0 : N = 0
  case pos =>
    have hx1eq :
        x = F.one := by
      have hxceil :=
        canonicalTailMax_value_eq_ceiling F A hq hx0
          (le_of_lt F hxlt1) (N := N) hN
      rw [hN0, canonicalPartial_zero, baseTail_zero, F.zero_add] at hxceil
      exact hxceil
    exact (ne_of_lt F hxlt1) hx1eq
  case neg =>
    let m := N - 1
    have hm_succ : m + 1 = N := by
      dsimp [m]
      omega
    have hnotPm : Not (P m) := by
      intro hm
      have hNm : N <= m := hNmin m hm
      omega
    have hdm_ne :
        Not (canonicalDigits F q x m = q - 1) := by
      intro hdm
      apply hnotPm
      intro n hn
      by_cases hnm : n = m
      case pos =>
        rw [hnm]
        exact hdm
      case neg =>
        have hNn : N <= n := by
          omega
        exact hN n hNn
    let d := canonicalDigits F q x m
    have hdle : d <= q - 1 := by
      dsimp [d, canonicalDigits]
      exact canonicalDigit_le_max F q x (canonicalPartial F q x m) m
    have hdnext : d + 1 <= q - 1 := by
      have hne : Not (d = q - 1) := by
        dsimp [d]
        exact hdm_ne
      omega
    have hxceil :=
      canonicalTailMax_value_eq_ceiling F A hq hx0
        (le_of_lt F hxlt1) (N := N) hN
    have hright_eq :
        baseChildRight F q (canonicalPartial F q x m) m d = x := by
      calc
        baseChildRight F q (canonicalPartial F q x m) m d =
            F.add
              (baseChildLeft F q (canonicalPartial F q x m) m d)
              (baseTail F q (m + 1)) := by
              rw [baseChildRight_eq_left_add_tail]
        _ = F.add
              (canonicalPartial F q x (m + 1))
              (baseTail F q (m + 1)) := by
              rw [canonicalPartial_succ]
        _ = F.add
              (canonicalPartial F q x N)
              (baseTail F q N) := by
              rw [hm_succ]
        _ = x := by
              exact hxceil.symm
    have hleft_next :
        F.le
          (baseChildLeft F q (canonicalPartial F q x m) m (d + 1))
          x := by
      rw [<- baseChildRight_eq_next_left F q
        (canonicalPartial F q x m) m d]
      rw [hright_eq]
      exact F.le_refl x
    have hdnext_le_d : d + 1 <= d := by
      dsimp [d, canonicalDigits]
      exact canonicalDigit_maximal F hdnext hleft_next
    omega

theorem canonicalDigits_canonicalStream
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) {x : alpha}
    (hx0 : F.le F.zero x)
    (hxlt1 : F.lt x F.one) :
    CanonicalBaseDigitStream q (canonicalDigits F q x) := by
  constructor
  · exact canonicalDigits_digitStream F hq x
  · intro N
    classical
    by_cases h :
        Exists
          (fun n : Nat =>
            And (N <= n)
              (Not (canonicalDigits F q x n = q - 1)))
    · exact h
    · have hmax :
          EventuallyMaxDigits q (canonicalDigits F q x) := by
        exact Exists.intro N (fun n hn => by
          by_cases heq : canonicalDigits F q x n = q - 1
          · exact heq
          · exact False.elim
              (h (Exists.intro n (And.intro hn heq))))
      exact False.elim
        ((canonicalDigits_not_eventuallyMax F A hq hx0 hxlt1) hmax)

/-- Every point of the half-open unit interval has a canonical base-`q`
expansion: the canonical digits both expand `x` and never settle to all
max. The strict upper bound is forced, and the only hypothesis is again
the inverse-natural Archimedean principle. -/
theorem canonicalBaseExpansion_exists
    (A : F.InvNatArchimedeanPrinciple)
    {q : Nat} (hq : ValidBase q) :
    CanonicalBaseExpansionExistenceStatement F q := by
  intro x hx0 hxlt1
  let digits := canonicalDigits F q x
  have hbase :
      HasBaseExpansion F q x digits :=
    canonicalDigits_hasBaseExpansion F A hq hx0 (le_of_lt F hxlt1)
  exact Exists.intro digits
    (And.intro hq
      (And.intro
        (canonicalDigits_canonicalStream F A hq hx0 hxlt1)
        hbase.right.right))

/-- The stage-`n` envelope of a digit stream: the truncation plus the
whole remaining tail. It only shrinks as the stage grows
(`baseExpansionEnvelope_mono`), dropping strictly at a stage whose digit
is not maximal. Every value these digits expand to lies at or below
every envelope, which makes it the upper fence of the uniqueness proof. -/
noncomputable def baseExpansionEnvelope
    (q : Nat) (digits : Nat -> Nat) (n : Nat) : alpha :=
  F.add (baseExpansionPartial F q digits n) (baseTail F q n)

theorem baseExpansionPartial_le_envelope {q : Nat}
    (hq : ValidBase q) (digits : Nat -> Nat) (n : Nat) :
    F.le
      (baseExpansionPartial F q digits n)
      (baseExpansionEnvelope F q digits n) := by
  unfold baseExpansionEnvelope
  have htail : F.le F.zero (baseTail F q n) :=
    le_of_lt F (baseTail_pos F hq n)
  have h :=
    add_le_add_left F htail (baseExpansionPartial F q digits n)
  rwa [F.add_zero] at h

theorem baseWeightedDigit_mono_valid {q d e n : Nat}
    (hq : ValidBase q)
    (hde : d <= e) :
    F.le
      (baseWeightedDigit F q d n)
      (baseWeightedDigit F q e n) := by
  unfold baseWeightedDigit baseDigitValue
  exact mul_le_mul_nonneg_right F
    (nat_le_nat_of_le F hde)
    (le_of_lt F (baseTail_pos F hq (n + 1)))

theorem baseWeightedDigit_add_tail_succ_eq_succ
    (q d n : Nat) :
    F.add (baseWeightedDigit F q d n)
      (baseTail F q (n + 1)) =
    baseWeightedDigit F q (d + 1) n := by
  unfold baseWeightedDigit baseDigitValue
  rw [nat_succ]
  rw [F.add_mul, F.one_mul]

theorem baseWeightedDigit_add_tail_succ_lt_tail_of_not_max
    {q digit n : Nat}
    (hq : ValidBase q)
    (hdigit : BaseDigit q digit)
    (hnot : Not (digit = q - 1)) :
    F.lt
      (F.add (baseWeightedDigit F q digit n)
        (baseTail F q (n + 1)))
      (baseTail F q n) := by
  rw [baseWeightedDigit_add_tail_succ_eq_succ]
  have hsucc_le : digit + 1 <= q - 1 := by
    unfold BaseDigit at hdigit
    omega
  have hle :
      F.le
        (baseWeightedDigit F q (digit + 1) n)
        (baseWeightedDigit F q (q - 1) n) :=
    baseWeightedDigit_mono_valid F hq hsucc_le
  have hlt_tail :
      F.lt
        (baseWeightedDigit F q (q - 1) n)
        (baseTail F q n) := by
    have hpos : F.lt F.zero (baseTail F q (n + 1)) :=
      baseTail_pos F hq (n + 1)
    have hlt_add :=
      add_lt_add_left F hpos
        (baseWeightedDigit F q (q - 1) n)
    rw [F.add_zero] at hlt_add
    rwa [baseWeightedMax_add_tail_succ F hq] at hlt_add
  exact lt_of_le_of_lt F hle hlt_tail

theorem baseWeightedDigit_add_tail_succ_le_tail
    {q digit n : Nat}
    (hq : ValidBase q)
    (hdigit : BaseDigit q digit) :
    F.le
      (F.add (baseWeightedDigit F q digit n)
        (baseTail F q (n + 1)))
      (baseTail F q n) := by
  by_cases hmax : digit = q - 1
  · rw [hmax]
    rw [baseWeightedMax_add_tail_succ F hq]
    exact F.le_refl (baseTail F q n)
  · exact le_of_lt F
      (baseWeightedDigit_add_tail_succ_lt_tail_of_not_max
        F hq hdigit hmax)

theorem baseExpansionEnvelope_succ_le
    {q : Nat} (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits)
    (n : Nat) :
    F.le
      (baseExpansionEnvelope F q digits (n + 1))
      (baseExpansionEnvelope F q digits n) := by
  unfold baseExpansionEnvelope
  rw [baseExpansionPartial_succ]
  rw [F.add_assoc]
  exact add_le_add_left F
    (baseWeightedDigit_add_tail_succ_le_tail F hq (hdigits n))
    (baseExpansionPartial F q digits n)

theorem baseExpansionEnvelope_succ_lt_of_not_max
    {q : Nat} (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits)
    {n : Nat}
    (hnot : Not (digits n = q - 1)) :
    F.lt
      (baseExpansionEnvelope F q digits (n + 1))
      (baseExpansionEnvelope F q digits n) := by
  unfold baseExpansionEnvelope
  rw [baseExpansionPartial_succ]
  rw [F.add_assoc]
  exact add_lt_add_left F
    (baseWeightedDigit_add_tail_succ_lt_tail_of_not_max
      F hq (hdigits n) hnot)
    (baseExpansionPartial F q digits n)

theorem baseExpansionEnvelope_mono {q : Nat}
    (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits) :
    forall n m : Nat,
      n <= m ->
        F.le
          (baseExpansionEnvelope F q digits m)
          (baseExpansionEnvelope F q digits n) := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact F.le_refl (baseExpansionEnvelope F q digits n)
  | step h ih =>
      exact F.le_trans
        (baseExpansionEnvelope_succ_le F hq hdigits _)
        ih

theorem baseExpansionPartial_le_value
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits)
    (n : Nat) :
    F.le (baseExpansionPartial F q digits n) x := by
  have hpartial_const :
      SeqTendsto F
        (fun _ : Nat => baseExpansionPartial F q digits n)
        (baseExpansionPartial F q digits n) :=
    seqTendsto_const F (baseExpansionPartial F q digits n)
  have hevent :
      Eventually
        (fun m : Nat =>
          F.le
            (baseExpansionPartial F q digits n)
            (baseExpansionPartial F q digits m)) :=
    Exists.intro n
      (fun m hm =>
        baseExpansionPartial_mono F h.left digits n m hm)
  exact seqTendsto_le_of_eventually_le F
    hpartial_const h.right.right hevent

/-- The value sits at or below every envelope. Together with
`baseExpansionPartial_le_value`, which keeps every truncation at or
below the value, this brackets `x` between the two stage-`n`
quantities, truncation below and envelope above -- the bracket
`Tautology.RealNegligibility.CantorSet` reads its cylinder endpoints from. -/
theorem baseExpansion_value_le_envelope
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits)
    (n : Nat) :
    F.le x (baseExpansionEnvelope F q digits n) := by
  have henvelope_const :
      SeqTendsto F
        (fun _ : Nat => baseExpansionEnvelope F q digits n)
        (baseExpansionEnvelope F q digits n) :=
    seqTendsto_const F (baseExpansionEnvelope F q digits n)
  have hevent :
      Eventually
        (fun m : Nat =>
          F.le
            (baseExpansionPartial F q digits m)
            (baseExpansionEnvelope F q digits n)) := by
    refine Exists.intro n ?_
    intro m hm
    exact F.le_trans
      (baseExpansionPartial_le_envelope F h.left digits m)
      (baseExpansionEnvelope_mono F h.left h.right.left n m hm)
  exact seqTendsto_le_of_eventually_le F
    h.right.right henvelope_const hevent

/-- For a canonical stream the bracket is strict on the upper side:
some later digit differs from `q - 1`, the envelope drops strictly
there, and `x` falls strictly below every envelope. This strictness,
available only under canonicity, is what separates two canonical
streams at their first differing digit. -/
theorem canonicalBaseExpansion_value_lt_envelope
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasCanonicalBaseExpansion F q x digits)
    (n : Nat) :
    F.lt x (baseExpansionEnvelope F q digits n) := by
  have hbase : HasBaseExpansion F q x digits :=
    canonical_hasBaseExpansion F h
  cases h.right.left.right n with
  | intro k hk =>
      have hvalue_le :
          F.le x (baseExpansionEnvelope F q digits (k + 1)) :=
        baseExpansion_value_le_envelope F hbase (k + 1)
      have hstrict :
          F.lt
            (baseExpansionEnvelope F q digits (k + 1))
            (baseExpansionEnvelope F q digits k) :=
        baseExpansionEnvelope_succ_lt_of_not_max
          F h.left h.right.left.left hk.right
      have hmono :
          F.le
            (baseExpansionEnvelope F q digits k)
            (baseExpansionEnvelope F q digits n) :=
        baseExpansionEnvelope_mono F h.left h.right.left.left n k hk.left
      exact lt_of_le_of_lt F hvalue_le
        (lt_of_lt_of_le F hstrict hmono)

theorem baseExpansionPartial_eq_of_prefix_eq
    (q : Nat) {digits e : Nat -> Nat} :
    forall n : Nat,
      (forall k : Nat, k < n -> digits k = e k) ->
        baseExpansionPartial F q digits n =
          baseExpansionPartial F q e n := by
  intro n
  induction n with
  | zero =>
      intro _h
      rw [baseExpansionPartial_zero, baseExpansionPartial_zero]
  | succ n ih =>
      intro hprefix
      rw [baseExpansionPartial_succ, baseExpansionPartial_succ]
      rw [ih (fun k hk => hprefix k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
      rw [hprefix n (Nat.lt_succ_self n)]

/-- The crossing the uniqueness argument turns on: when two streams
agree below `n` and the first has the strictly smaller digit at `n`,
that stream's envelope at stage `n + 1` already lies at or below the
other stream's truncation at stage `n + 1`. -/
theorem baseExpansionEnvelope_succ_le_partial_succ_of_digit_lt
    {q : Nat} (hq : ValidBase q)
    {digits e : Nat -> Nat} {n : Nat}
    (hprefix :
      forall k : Nat, k < n -> digits k = e k)
    (hlt : digits n < e n) :
    F.le
      (baseExpansionEnvelope F q digits (n + 1))
      (baseExpansionPartial F q e (n + 1)) := by
  unfold baseExpansionEnvelope
  rw [baseExpansionPartial_succ, baseExpansionPartial_succ]
  rw [baseExpansionPartial_eq_of_prefix_eq F q n hprefix]
  rw [F.add_assoc]
  rw [baseWeightedDigit_add_tail_succ_eq_succ]
  exact add_le_add_left F
    (baseWeightedDigit_mono_valid F hq (Nat.succ_le_of_lt hlt))
    (baseExpansionPartial F q e n)

/-- Canonical digits are determined by their value: two canonical
expansions of the same `x` agree positionwise. The proof demands
nothing of the field -- no completeness, no Archimedean principle --
only the envelope machinery above: at the first differing position the
smaller stream's envelope crosses below the larger one's truncation,
while both must sandwich one and the same `x`. -/
theorem canonicalBaseExpansion_unique
    {q : Nat} :
    CanonicalBaseExpansionUniquenessStatement F q := by
  intro x digits e hdigits he
  funext n
  by_cases hsame : digits n = e n
  · exact hsame
  let P : Nat -> Prop := fun k : Nat => Not (digits k = e k)
  let N := Tautology.Nat.least P (Exists.intro n hsame)
  have hNdiff : P N := by
    dsimp [N]
    exact Tautology.Nat.least_spec P (Exists.intro n hsame)
  have hNmin : forall k : Nat, P k -> N <= k := by
    intro k hk
    dsimp [N]
    exact Tautology.Nat.least_min P (Exists.intro n hsame) hk
  have hprefix :
      forall k : Nat, k < N -> digits k = e k := by
    intro k hk
    by_cases hkeq : digits k = e k
    · exact hkeq
    · have hNk : N <= k := hNmin k hkeq
      omega
  have hbaseDigits : HasBaseExpansion F q x digits :=
    canonical_hasBaseExpansion F hdigits
  have hbaseE : HasBaseExpansion F q x e :=
    canonical_hasBaseExpansion F he
  by_cases hle : digits N <= e N
  case pos =>
    have hlt : digits N < e N := by
      have hneN : Not (digits N = e N) := hNdiff
      omega
    have hstrict :
        F.lt x (baseExpansionEnvelope F q digits (N + 1)) :=
      canonicalBaseExpansion_value_lt_envelope F hdigits (N + 1)
    have hbridge :
        F.le
          (baseExpansionEnvelope F q digits (N + 1))
          (baseExpansionPartial F q e (N + 1)) :=
      baseExpansionEnvelope_succ_le_partial_succ_of_digit_lt
        F hdigits.left hprefix hlt
    have hright :
        F.le (baseExpansionPartial F q e (N + 1)) x :=
      baseExpansionPartial_le_value F hbaseE (N + 1)
    have hbad : F.lt x x :=
      lt_of_lt_of_le F hstrict (F.le_trans hbridge hright)
    exact False.elim ((lt_irrefl F x) hbad)
  case neg =>
    have hlt : e N < digits N := by
      omega
    have hstrict :
        F.lt x (baseExpansionEnvelope F q e (N + 1)) :=
      canonicalBaseExpansion_value_lt_envelope F he (N + 1)
    have hprefix_symm :
        forall k : Nat, k < N -> e k = digits k := by
      intro k hk
      exact (hprefix k hk).symm
    have hbridge :
        F.le
          (baseExpansionEnvelope F q e (N + 1))
          (baseExpansionPartial F q digits (N + 1)) :=
      baseExpansionEnvelope_succ_le_partial_succ_of_digit_lt
        F he.left hprefix_symm hlt
    have hright :
        F.le (baseExpansionPartial F q digits (N + 1)) x :=
      baseExpansionPartial_le_value F hbaseDigits (N + 1)
    have hbad : F.lt x x :=
      lt_of_lt_of_le F hstrict (F.le_trans hbridge hright)
    exact False.elim ((lt_irrefl F x) hbad)

end IsOrderedFieldBaseLike
end Tautology
