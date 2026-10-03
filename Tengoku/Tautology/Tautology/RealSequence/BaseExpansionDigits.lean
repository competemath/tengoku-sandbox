import Tengoku.Tautology.Tautology.RealSequence.BaseExpansion
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# The vocabulary of base expansions

Everything one needs to *state* facts about expansions, before any expansion is
constructed: digit streams and the four shapes they can have (eventually zero,
eventually maximal, canonical, restricted); the weighted digits and their
partial sums; the three `Has...Expansion` predicates with their bundled data;
prefix and cylinder vocabulary; and two instantiations that later regions
consume -- binary expansions, and the ternary Cantor digits used by
`Tautology.RealNegligibility.CantorSet`.

The theorems here are the ones that need no construction: the truncations
increase, stay below one, and are determined by their digits, so a value has at
most one digit stream up to canonicity.

## Where completeness enters, and where it does not

At exactly one declaration. `baseExpansionPartial_converges` takes the
monotone-convergence principle -- a node of the completeness route graph in
`Tautology.RealSequence.Principles.Statements` -- as an explicit hypothesis,
and concludes that any digit stream has a value. That is the abstract route to
existence.

Everything else in this file is ordered-field reasoning, and the *constructive*
route to existence in `Tautology.RealSequence.BaseExpansionExistence` bypasses
the abstract one entirely: it builds the digits by bisection and needs only an
Archimedean principle. Two routes to the same conclusion, priced differently,
both kept.

## Position and role

Implementation module, the middle of the expansion cluster. The facade
`Tautology.RealTheory.Sequence` assembles its `BaseExpansionPackage` for the
selected carrier.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- A base: a natural number strictly above one, so that the digits `0`
through `q - 1` exist and each place weighs strictly less than the one
before it. This is the standing hypothesis of every definition and
every theorem across the three base-expansion modules. -/
def ValidBase (q : Nat) : Prop :=
  1 < q

/-- A digit for base `q`: a natural strictly below `q`. Digits live in
`Nat`, not in the field; the embedding that turns one into a field
element is `baseDigitValue` below. -/
def BaseDigit (q digit : Nat) : Prop :=
  digit < q

/-- A digit stream for base `q`: a genuine digit at every position.
Nothing is demanded about the stream's eventual shape; the shape
predicates live separately, as `EventuallyZeroDigits`,
`EventuallyMaxDigits` and `CanonicalBaseDigitStream`. -/
def BaseDigitStream (q : Nat) (digits : Nat -> Nat) : Prop :=
  forall n : Nat, BaseDigit q (digits n)

/-- The digits are zero from some position on -- the shape of a
terminating expansion. The predicate is independent of the base. -/
def EventuallyZeroDigits (digits : Nat -> Nat) : Prop :=
  Exists (fun N : Nat => forall n : Nat, N <= n -> digits n = 0)

/-- The digits are all `q - 1` from some position on: the repeating-max
tail, the shape an expansion takes on the other side of a value that has
two of them. Canonicity below is defined so as to exclude exactly this. -/
def EventuallyMaxDigits (q : Nat) (digits : Nat -> Nat) : Prop :=
  Exists (fun N : Nat => forall n : Nat, N <= n -> digits n = q - 1)

/-- The canonical form of a digit stream: still a genuine digit stream
at every position, and after every `N` some later position carries a
digit other than `q - 1`. This is the positive form of "not eventually
max"; imposing it selects one of the two expansions a value may have,
which is what makes the uniqueness statement below provable. -/
def CanonicalBaseDigitStream (q : Nat) (digits : Nat -> Nat) : Prop :=
  And (BaseDigitStream q digits)
    (forall N : Nat,
      Exists
        (fun n : Nat =>
          And (N <= n) (Not (digits n = q - 1))))

/-- A digit stream confined to an allowed set: still digits of base `q`,
and at every position the digit satisfies the predicate `allowed`. The
Cantor digits (`TernaryCantorDigitAllowed` below) are the restriction
`Tautology.RealNegligibility.CantorSet` runs on. -/
def RestrictedBaseDigitStream
    (q : Nat) (allowed : Nat -> Prop) (digits : Nat -> Nat) : Prop :=
  And (BaseDigitStream q digits)
    (forall n : Nat, allowed (digits n))

theorem zero_baseDigit {q : Nat}
    (hq : ValidBase q) :
    BaseDigit q 0 := by
  unfold ValidBase at hq
  unfold BaseDigit
  omega

theorem max_baseDigit {q : Nat}
    (hq : ValidBase q) :
    BaseDigit q (q - 1) := by
  unfold ValidBase at hq
  unfold BaseDigit
  omega

theorem zeroDigitStream {q : Nat}
    (hq : ValidBase q) :
    BaseDigitStream q (fun _ : Nat => 0) := by
  intro _n
  exact zero_baseDigit hq

theorem maxDigitStream {q : Nat}
    (hq : ValidBase q) :
    BaseDigitStream q (fun _ : Nat => q - 1) := by
  intro _n
  exact max_baseDigit hq

theorem zeroDigits_eventuallyZero :
    EventuallyZeroDigits (fun _ : Nat => 0) :=
  Exists.intro 0 (fun _ _ => rfl)

theorem maxDigits_eventuallyMax (q : Nat) :
    EventuallyMaxDigits q (fun _ : Nat => q - 1) :=
  Exists.intro 0 (fun _ _ => rfl)

theorem not_eventuallyMax_of_canonical
    {q : Nat} {digits : Nat -> Nat}
    (h : CanonicalBaseDigitStream q digits) :
    Not (EventuallyMaxDigits q digits) := by
  intro hmax
  cases hmax with
  | intro N hN =>
      cases h.right N with
      | intro n hn =>
          exact hn.right (hN n hn.left)

/-- A digit seen as a field element: the natural `digit` pushed through
`nat F`. Digits are compared and searched for on the Nat side and
embedded only when field arithmetic is needed. -/
noncomputable def baseDigitValue (digit : Nat) : alpha :=
  nat F digit

/-- The contribution of one digit to the sum: the digit's value scaled
by the weight of its place, `digit / q ^ (place + 1)`. Places are
counted from zero immediately after the point, so place `0` carries
weight `1 / q`. -/
noncomputable def baseWeightedDigit
    (q digit place : Nat) : alpha :=
  F.mul (baseDigitValue F digit) (baseTail F q (place + 1))

theorem basePow_pos {q : Nat}
    (hq : ValidBase q) (n : Nat) :
    F.lt F.zero (basePow F q n) := by
  unfold ValidBase at hq
  unfold basePow
  have hq_pos : 0 < q := by omega
  have hpow_pos : 0 < q ^ n := Nat.pow_pos hq_pos
  have hpow_ne : Not (q ^ n = 0) := by
    intro hzero
    omega
  exact nat_pos_of_ne_zero F hpow_ne

theorem baseTail_pos {q : Nat}
    (hq : ValidBase q) (n : Nat) :
    F.lt F.zero (baseTail F q n) := by
  unfold baseTail
  exact inv_pos F (basePow_pos F hq n)

theorem basePow_ne_zero {q : Nat}
    (hq : ValidBase q) (n : Nat) :
    Not (basePow F q n = F.zero) := by
  intro hzero
  exact ne_of_lt F (basePow_pos F hq n) hzero.symm

theorem basePow_succ
    (q n : Nat) :
    basePow F q (n + 1) =
      F.mul (basePow F q n) (nat F q) := by
  unfold basePow
  rw [Nat.pow_succ, nat_mul]

/-- The tail at stage zero is one, not zero: nothing has been cut off
yet, and what remains to be distributed is the whole of `[0, 1]`. -/
theorem baseTail_zero (q : Nat) :
    baseTail F q 0 = F.one := by
  unfold baseTail basePow
  rw [Nat.pow_zero, nat_one, inv_one F]

theorem baseTail_eq_mul_baseTail_succ {q : Nat}
    (hq : ValidBase q) (n : Nat) :
    baseTail F q n =
      F.mul (nat F q) (baseTail F q (n + 1)) := by
  symm
  unfold baseTail
  apply eq_inv_of_mul_eq_one_left F
    (x := basePow F q n)
    (y := F.mul (nat F q) (F.inv (basePow F q (n + 1))))
  · exact basePow_ne_zero F hq n
  · calc
      F.mul (basePow F q n)
          (F.mul (nat F q) (F.inv (basePow F q (n + 1)))) =
          F.mul (F.mul (basePow F q n) (nat F q))
            (F.inv (basePow F q (n + 1))) := by
            rw [F.mul_assoc]
      _ = F.mul (basePow F q (n + 1))
            (F.inv (basePow F q (n + 1))) := by
            rw [basePow_succ F q n]
      _ = F.one := by
            rw [F.mul_inv_cancel (basePow_ne_zero F hq (n + 1))]

theorem nat_pred_add_one {q : Nat}
    (hq : ValidBase q) :
    nat F q = F.add (nat F (q - 1)) F.one := by
  unfold ValidBase at hq
  have hsucc : q - 1 + 1 = q := by omega
  calc
    nat F q = nat F (q - 1 + 1) := by rw [hsucc]
    _ = F.add (nat F (q - 1)) F.one := by rw [nat_succ]

theorem baseWeightedDigit_nonneg {q digit place : Nat}
    (hq : ValidBase q) :
    F.le F.zero (baseWeightedDigit F q digit place) := by
  unfold baseWeightedDigit baseDigitValue
  exact F.mul_nonneg
    (nat_nonneg F digit)
    (le_of_lt F (baseTail_pos F hq (place + 1)))

theorem baseWeightedDigit_le_max {q digit place : Nat}
    (hq : ValidBase q)
    (hdigit : BaseDigit q digit) :
    F.le
      (baseWeightedDigit F q digit place)
      (baseWeightedDigit F q (q - 1) place) := by
  unfold BaseDigit at hdigit
  unfold baseWeightedDigit baseDigitValue
  have hdigit_le : digit <= q - 1 := by omega
  exact mul_le_mul_nonneg_right F
    (nat_le_nat_of_le F hdigit_le)
    (le_of_lt F (baseTail_pos F hq (place + 1)))

theorem baseWeightedMax_add_tail_succ {q n : Nat}
    (hq : ValidBase q) :
    F.add (baseWeightedDigit F q (q - 1) n)
      (baseTail F q (n + 1)) =
    baseTail F q n := by
  let t := baseTail F q (n + 1)
  have htail : baseTail F q n = F.mul (nat F q) t := by
    unfold t
    exact baseTail_eq_mul_baseTail_succ F hq n
  calc
    F.add (baseWeightedDigit F q (q - 1) n)
        (baseTail F q (n + 1)) =
        F.add (F.mul (nat F (q - 1)) t) t := by
          unfold baseWeightedDigit baseDigitValue t
          rfl
    _ = F.add (F.mul (nat F (q - 1)) t)
        (F.mul F.one t) := by
          rw [F.one_mul]
    _ = F.mul (F.add (nat F (q - 1)) F.one) t := by
          rw [F.add_mul]
    _ = F.mul (nat F q) t := by
          rw [<- nat_pred_add_one F hq]
    _ = baseTail F q n := by rw [<- htail]

theorem baseWeightedMax_eq_tail_sub {q n : Nat}
    (hq : ValidBase q) :
    baseWeightedDigit F q (q - 1) n =
      F.sub (baseTail F q n) (baseTail F q (n + 1)) := by
  apply add_right_cancel F (a := baseTail F q (n + 1))
  rw [sub_add_cancel F (baseTail F q n) (baseTail F q (n + 1))]
  exact baseWeightedMax_add_tail_succ F hq

/-- The `n`-th truncation of a digit stream: the running sum of the
weighted digits, `digits 0 / q + ... + digits (n - 1) / q ^ n`, with the
empty truncation at `n = 0` equal to zero. Convergence of these
truncations is what "having an expansion" means below. -/
noncomputable def baseExpansionPartial
    (q : Nat) (digits : Nat -> Nat) : Nat -> alpha
  | 0 => F.zero
  | n + 1 =>
      F.add (baseExpansionPartial q digits n)
        (baseWeightedDigit F q (digits n) n)

theorem baseExpansionPartial_zero
    (q : Nat) (digits : Nat -> Nat) :
    baseExpansionPartial F q digits 0 = F.zero :=
  rfl

theorem baseExpansionPartial_succ
    (q : Nat) (digits : Nat -> Nat) (n : Nat) :
    baseExpansionPartial F q digits (n + 1) =
      F.add (baseExpansionPartial F q digits n)
        (baseWeightedDigit F q (digits n) n) :=
  rfl

theorem baseExpansionPartial_nonneg {q : Nat}
    (hq : ValidBase q) (digits : Nat -> Nat) :
    forall n : Nat,
      F.le F.zero (baseExpansionPartial F q digits n) := by
  intro n
  induction n with
  | zero =>
      rw [baseExpansionPartial_zero]
      exact F.le_refl F.zero
  | succ n ih =>
      rw [baseExpansionPartial_succ]
      have hterm :
          F.le F.zero (baseWeightedDigit F q (digits n) n) :=
        baseWeightedDigit_nonneg F
          (q := q) (digit := digits n) (place := n) hq
      have h :=
        add_le_add F
          (w := F.zero)
          (x := baseExpansionPartial F q digits n)
          (y := F.zero)
          (z := baseWeightedDigit F q (digits n) n)
          ih hterm
      rwa [F.zero_add] at h

theorem baseExpansionPartial_le_succ {q : Nat}
    (hq : ValidBase q) (digits : Nat -> Nat) (n : Nat) :
    F.le
      (baseExpansionPartial F q digits n)
      (baseExpansionPartial F q digits (n + 1)) := by
  rw [baseExpansionPartial_succ]
  have hterm :
      F.le F.zero (baseWeightedDigit F q (digits n) n) :=
    baseWeightedDigit_nonneg F hq
  have h :=
    add_le_add_left F hterm (baseExpansionPartial F q digits n)
  rwa [F.add_zero] at h

theorem baseExpansionPartial_mono {q : Nat}
    (hq : ValidBase q) (digits : Nat -> Nat) :
    forall n m : Nat,
      n <= m ->
        F.le
          (baseExpansionPartial F q digits n)
          (baseExpansionPartial F q digits m) := by
  intro n m hnm
  induction m with
  | zero =>
      have hn0 : n = 0 := by omega
      subst hn0
      exact F.le_refl (baseExpansionPartial F q digits 0)
  | succ m ih =>
      by_cases hnm' : n <= m
      · exact F.le_trans (ih hnm')
          (baseExpansionPartial_le_succ F hq digits m)
      · have hn : n = m + 1 := by omega
        subst hn
        exact F.le_refl (baseExpansionPartial F q digits (m + 1))

/-- The all-`(q - 1)` stream has closed-form partials: the first `n` max
digits telescope to `1 - 1 / q ^ n`. This identifies the digit-sum side
of the repeating-nines limit with the closed form defined in
`Tautology.RealSequence.BaseExpansion`. -/
theorem maxDigitsPartial_eq_repeatingMaxDigitPartial {q : Nat}
    (hq : ValidBase q) :
    forall n : Nat,
      baseExpansionPartial F q (fun _ : Nat => q - 1) n =
        repeatingMaxDigitPartial F q n := by
  intro n
  induction n with
  | zero =>
      unfold repeatingMaxDigitPartial
      rw [baseExpansionPartial_zero, baseTail_zero, sub_self F F.one]
  | succ n ih =>
      rw [baseExpansionPartial_succ, ih]
      unfold repeatingMaxDigitPartial
      rw [baseWeightedMax_eq_tail_sub F hq]
      exact
        sub_add_sub_cancel F F.one
          (baseTail F q n) (baseTail F q (n + 1))

theorem baseExpansionPartial_le_maxDigitsPartial {q : Nat}
    (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits) :
    forall n : Nat,
      F.le
        (baseExpansionPartial F q digits n)
        (baseExpansionPartial F q (fun _ : Nat => q - 1) n) := by
  intro n
  induction n with
  | zero =>
      rw [baseExpansionPartial_zero, baseExpansionPartial_zero]
      exact F.le_refl F.zero
  | succ n ih =>
      rw [baseExpansionPartial_succ, baseExpansionPartial_succ]
      exact add_le_add F ih
        (baseWeightedDigit_le_max F hq (hdigits n))

theorem sub_le_self_of_nonneg {x y : alpha}
    (hy : F.le F.zero y) :
    F.le (F.sub x y) x := by
  have hneg : F.le (F.neg y) F.zero := by
    have h := neg_le_neg F hy
    rwa [neg_zero F] at h
  have h := add_le_add_left F hneg x
  rwa [<- F.sub_eq_add_neg x y, F.add_zero] at h

theorem repeatingMaxDigitPartial_le_one {q : Nat}
    (hq : ValidBase q) (n : Nat) :
    F.le (repeatingMaxDigitPartial F q n) F.one := by
  unfold repeatingMaxDigitPartial
  exact sub_le_self_of_nonneg F
    (le_of_lt F (baseTail_pos F hq n))

/-- Every truncation of every digit stream stays at or below one: each
partial is dominated digit-by-digit by the all-max partial of the same
length, which is `1 - 1 / q ^ n`. Together with monotonicity this is the
bounded half of `baseExpansionPartial_converges`. -/
theorem baseExpansionPartial_le_one {q : Nat}
    (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits) :
    forall n : Nat,
      F.le (baseExpansionPartial F q digits n) F.one := by
  intro n
  exact F.le_trans
    (baseExpansionPartial_le_maxDigitsPartial F hq hdigits n)
    (by
      rw [maxDigitsPartial_eq_repeatingMaxDigitPartial F hq n]
      exact repeatingMaxDigitPartial_le_one F hq n)

/-- `x` has the base-`q` expansion given by `digits`: the base is valid,
the digits are genuine at every position, and the truncations converge
to `x`. Everything happens inside the unit interval -- nonnegativity of
`x` and `x ≤ 1` are consequences
(`baseExpansion_value_mem_unitInterval`), never hypotheses. -/
def HasBaseExpansion
    (q : Nat) (x : alpha) (digits : Nat -> Nat) : Prop :=
  And (ValidBase q)
    (And (BaseDigitStream q digits)
      (SeqTendsto F (baseExpansionPartial F q digits) x))

/-- Same, with the digit stream required to be canonical: after every
position some later digit differs from `q - 1`, which rules out the
repeating-max tail and pins the digits to `x`
(`canonicalBaseExpansion_unique` in
`Tautology.RealSequence.BaseExpansionExistence`). -/
def HasCanonicalBaseExpansion
    (q : Nat) (x : alpha) (digits : Nat -> Nat) : Prop :=
  And (ValidBase q)
    (And (CanonicalBaseDigitStream q digits)
      (SeqTendsto F (baseExpansionPartial F q digits) x))

/-- Same, with every digit required to satisfy the predicate `allowed`.
This is the form a set defined by its digits takes its expansions in;
the Cantor set's ternary expansions are the instance in use. -/
def HasRestrictedBaseExpansion
    (q : Nat) (allowed : Nat -> Prop)
    (x : alpha) (digits : Nat -> Nat) : Prop :=
  And (ValidBase q)
    (And (RestrictedBaseDigitStream q allowed digits)
      (SeqTendsto F (baseExpansionPartial F q digits) x))

theorem baseExpansionPartial_boundedAbove_one {q : Nat}
    (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits) :
    SeqBoundedAbove F (baseExpansionPartial F q digits) :=
  Exists.intro F.one (baseExpansionPartial_le_one F hq hdigits)

/-- Every digit stream has a value: its truncations, monotone and
bounded above by one, converge. This is the abstract existence route --
no algorithm anywhere, the monotone convergence principle taken as an
explicit hypothesis, so completeness enters here and only as this node.
The constructive route, `baseExpansion_exists` in
`Tautology.RealSequence.BaseExpansionExistence`, does without it, consuming the
weaker inverse-natural Archimedean principle instead. -/
theorem baseExpansionPartial_converges
    (M : F.MonotoneConvergencePrinciple)
    {q : Nat} (hq : ValidBase q)
    {digits : Nat -> Nat}
    (hdigits : BaseDigitStream q digits) :
    Exists (fun x : alpha => HasBaseExpansion F q x digits) := by
  cases M.increasing
      (baseExpansionPartial F q digits)
      (baseExpansionPartial_mono F hq digits)
      (baseExpansionPartial_boundedAbove_one F hq hdigits) with
  | intro x hx =>
      exact Exists.intro x (And.intro hq (And.intro hdigits hx))

theorem baseExpansion_value_nonneg
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits) :
    F.le F.zero x := by
  exact seqTendsto_nonneg_of_eventually_nonneg F
    h.right.right
    (Eventually.of_forall
      (baseExpansionPartial_nonneg F h.left digits))

theorem baseExpansion_value_le_one
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits) :
    F.le x F.one := by
  exact seqTendsto_le_of_eventually_le F
    h.right.right
    (seqTendsto_const F F.one)
    (Eventually.of_forall
      (baseExpansionPartial_le_one F h.left h.right.left))

theorem baseExpansion_value_mem_unitInterval
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits) :
    And (F.le F.zero x) (F.le x F.one) :=
  And.intro
    (baseExpansion_value_nonneg F h)
    (baseExpansion_value_le_one F h)
/-- An expansion bundled as data: the value, the digit stream, and the
proof that the truncations of the latter converge to the former. The
existential `HasBaseExpansion` is the propositional shadow of this;
packaging all three components as one value is for callers that carry a
witness around. -/
structure BaseExpansion (q : Nat) where
  value : alpha
  digits : Nat -> Nat
  has_expansion : HasBaseExpansion F q value digits

/-- The canonical companion of `BaseExpansion`: value, digits, and the
proof that the digits form a canonical stream converging to the value. -/
structure CanonicalBaseExpansion (q : Nat) where
  value : alpha
  digits : Nat -> Nat
  has_expansion : HasCanonicalBaseExpansion F q value digits

/-- The restricted companion of `BaseExpansion`, carrying the allowed
set alongside value, digits and proof. -/
structure RestrictedBaseExpansion
    (q : Nat) (allowed : Nat -> Prop) where
  value : alpha
  digits : Nat -> Nat
  has_expansion : HasRestrictedBaseExpansion F q allowed value digits

theorem hasBaseExpansion_digits
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits) :
    BaseDigitStream q digits :=
  h.right.left

theorem hasBaseExpansion_tendsto
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasBaseExpansion F q x digits) :
    SeqTendsto F (baseExpansionPartial F q digits) x :=
  h.right.right

/-- The value is a function of the digits: one digit stream cannot
converge to two limits. The converse fails without canonicity -- a value
may carry several digit streams, the repeating-nines phenomenon -- which
is why uniqueness is imposed on the digits, through
`CanonicalBaseDigitStream`, rather than expected of values. -/
theorem same_digits_baseExpansion_unique
    {q : Nat} {x y : alpha} {digits : Nat -> Nat}
    (hx : HasBaseExpansion F q x digits)
    (hy : HasBaseExpansion F q y digits) :
    x = y :=
  seqTendsto_unique F
    (hasBaseExpansion_tendsto F hx)
    (hasBaseExpansion_tendsto F hy)

theorem canonical_hasBaseExpansion
    {q : Nat} {x : alpha} {digits : Nat -> Nat}
    (h : HasCanonicalBaseExpansion F q x digits) :
    HasBaseExpansion F q x digits :=
  And.intro h.left
    (And.intro h.right.left.left h.right.right)

theorem restricted_hasBaseExpansion
    {q : Nat} {allowed : Nat -> Prop}
    {x : alpha} {digits : Nat -> Nat}
    (h : HasRestrictedBaseExpansion F q allowed x digits) :
    HasBaseExpansion F q x digits :=
  And.intro h.left
    (And.intro h.right.left.left h.right.right)

theorem baseWeightedDigit_zero
    (q n : Nat) :
    baseWeightedDigit F q 0 n = F.zero := by
  unfold baseWeightedDigit baseDigitValue
  rw [nat_zero]
  exact zero_mul F (baseTail F q (n + 1))

theorem zeroDigitsPartial_zero (q : Nat) :
    forall n : Nat,
      baseExpansionPartial F q (fun _ : Nat => 0) n = F.zero := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [baseExpansionPartial_succ, ih]
      rw [baseWeightedDigit_zero, F.add_zero]

theorem zeroDigits_hasBaseExpansion_zero {q : Nat}
    (hq : ValidBase q) :
    HasBaseExpansion F q F.zero (fun _ : Nat => 0) := by
  refine And.intro hq ?_
  refine And.intro (zeroDigitStream hq) ?_
  intro eps heps
  apply Eventually.of_forall
  intro n
  rw [zeroDigitsPartial_zero F q n]
  rw [abs_sub_self F F.zero]
  exact heps

/-- A finite prefix of digits: a length, a total function assigning a
digit to every position, and the guarantee that the positions below the
length carry genuine digits. Nothing is demanded at or beyond the
length; only `ExtendsBaseDigitPrefix` reads a prefix, and it reads
exactly the positions below it. -/
structure BaseDigitPrefix (q : Nat) where
  length : Nat
  digit : Nat -> Nat
  digit_lt : forall n : Nat, n < length -> BaseDigit q (digit n)

/-- A digit stream extends a prefix when the two agree at every position
below the prefix's length; beyond that length the stream is
unconstrained. This is the reading of a prefix that never touches its
unconstrained positions. -/
def ExtendsBaseDigitPrefix
    {q : Nat} (pref : BaseDigitPrefix q)
    (digits : Nat -> Nat) : Prop :=
  forall n : Nat, n < pref.length -> digits n = pref.digit n

/-- The base-`q` cylinder determined by a prefix: the points admitting
some base-`q` expansion whose digits extend the prefix. Membership is
witnessed by a digit stream, never by endpoints; the interval picture
of a cylinder is a theorem to be proved wherever it is needed, not part
of the definition. -/
def BaseCylinder
    (q : Nat) (pref : BaseDigitPrefix q) (x : alpha) : Prop :=
  Exists
    (fun digits : Nat -> Nat =>
      And (ExtendsBaseDigitPrefix pref digits)
        (HasBaseExpansion F q x digits))

/-- The cylinder cut out by a prefix inside the restricted expansions:
some stream extending the prefix, with every digit allowed, gives an
expansion of `x`. -/
def RestrictedBaseCylinder
    (q : Nat) (allowed : Nat -> Prop)
    (pref : BaseDigitPrefix q) (x : alpha) : Prop :=
  Exists
    (fun digits : Nat -> Nat =>
      And (ExtendsBaseDigitPrefix pref digits)
        (HasRestrictedBaseExpansion F q allowed x digits))

/-- The allowed set for binary expansions: a digit is either `0` or `1`. -/
def BinaryDigitAllowed (digit : Nat) : Prop :=
  Or (digit = 0) (digit = 1)

/-- The allowed set for middle-thirds Cantor expansions: a digit is either `0`
or `2`, the digit `1` being what the removed middle thirds delete. This is the
restriction `Tautology.RealNegligibility.CantorSet` runs on. -/
def TernaryCantorDigitAllowed (digit : Nat) : Prop :=
  Or (digit = 0) (digit = 2)

/-- A binary expansion of `x`: a restricted base-2 expansion with digits
confined to `0` and `1`. Being a specialisation of
`HasRestrictedBaseExpansion` at `q = 2`, every general fact about
restricted expansions applies to it unchanged. -/
def HasBinaryExpansion (x : alpha) (digits : Nat -> Nat) : Prop :=
  HasRestrictedBaseExpansion F 2 BinaryDigitAllowed x digits

/-- A ternary Cantor expansion of `x`: a restricted base-3 expansion
with digits confined to `0` and `2`. This is the digit-level definition
the Cantor set is built on -- `RealNegligibility.CantorSet.CantorSet`
is the existential over streams of exactly this predicate. -/
def HasTernaryCantorExpansion
    (x : alpha) (digits : Nat -> Nat) : Prop :=
  HasRestrictedBaseExpansion F 3 TernaryCantorDigitAllowed x digits

/-- Every point of the closed unit interval has some base-`q` expansion.
The upper bound is weak on purpose: `x = 1` does have an expansion, the
eventually-max one, and it is only the canonical statement below that
has to exclude it. -/
def BaseExpansionExistenceStatement (q : Nat) : Prop :=
  forall x : alpha,
    F.le F.zero x ->
      F.le x F.one ->
        Exists (fun digits : Nat -> Nat => HasBaseExpansion F q x digits)

/-- Every point of the half-open unit interval has a canonical base-`q`
expansion. The upper bound is strict here and has to be: `x = 1` has no
expansion that is not eventually max, hence no canonical one. -/
def CanonicalBaseExpansionExistenceStatement (q : Nat) : Prop :=
  forall x : alpha,
    F.le F.zero x ->
      F.lt x F.one ->
        Exists
          (fun digits : Nat -> Nat =>
            HasCanonicalBaseExpansion F q x digits)

/-- Canonical digits are determined by their value: two canonical
expansions of the same `x` agree at every position. Uniqueness holds
for the digits, not merely for the value; the value is always
determined by the digits
(`same_digits_baseExpansion_unique`), and canonicity is what makes the
converse direction true. -/
def CanonicalBaseExpansionUniquenessStatement (q : Nat) : Prop :=
  forall x : alpha,
    forall digits e : Nat -> Nat,
      HasCanonicalBaseExpansion F q x digits ->
        HasCanonicalBaseExpansion F q x e ->
          digits = e

/-- The four base-expansion facts bundled for one base: validity, existence on
the closed unit interval, canonical existence on the half-open one, and
uniqueness of canonical digits. `Tautology.RealTheory.Sequence` assembles this
package for the real carrier, discharging the Archimedean hypotheses from
Dedekind completeness. -/
structure BaseExpansionPackage (q : Nat) : Prop where
  valid : ValidBase q
  exists_expansion : BaseExpansionExistenceStatement F q
  exists_canonical : CanonicalBaseExpansionExistenceStatement F q
  unique_canonical : CanonicalBaseExpansionUniquenessStatement F q

end IsOrderedFieldBaseLike
end Tautology
