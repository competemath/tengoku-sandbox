module

public import Init.Data.Rat.Lemmas

/-!
# Rational arithmetic the backends need

Facts about Lean's `Rat` that the standard library does not provide in the
form used here: transitivity and trichotomy of the strict order, density,
sign behaviour, and the small manipulations the cut and sequence arguments
keep reaching for.

Every backend starts from `Rat`, so this file is genuinely shared -- the
Dedekind cuts are cuts of rationals, the Cauchy sequences are sequences of
rationals, and the Eudoxus construction counts along the integers with
rational estimates. Proving these once here is what keeps the three
constructions from each carrying their own copy.

Note this is Lean's `Rat`, an external type, and nothing to do with the
library's own `InternalRat`, which is a predicate on a carrier. At this depth
the carrier does not exist yet.

## Position in the development

Bottom of the backend subtree.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Rat

public theorem lt_trans {a b c : _root_.Rat} (hab : a < b) (hbc : b < c) :
    a < c := by
  have hac : a <= c :=
    _root_.Rat.le_trans (_root_.Rat.le_of_lt hab) (_root_.Rat.le_of_lt hbc)
  apply _root_.Rat.lt_of_le_of_ne hac
  intro hac_eq
  subst hac_eq
  have hba : b = a :=
    _root_.Rat.le_antisymm (_root_.Rat.le_of_lt hbc) (_root_.Rat.le_of_lt hab)
  rw [hba] at hbc
  exact _root_.Rat.lt_irrefl hbc

public theorem lt_of_le_of_lt {a b c : _root_.Rat}
    (hab : a <= b) (hbc : b < c) :
    a < c := by
  have hac : a <= c := _root_.Rat.le_trans hab (_root_.Rat.le_of_lt hbc)
  apply _root_.Rat.lt_of_le_of_ne hac
  intro hac_eq
  subst hac_eq
  have hba : b = a := _root_.Rat.le_antisymm (_root_.Rat.le_of_lt hbc) hab
  rw [hba] at hbc
  exact _root_.Rat.lt_irrefl hbc

public theorem lt_of_lt_of_le {a b c : _root_.Rat}
    (hab : a < b) (hbc : b <= c) :
    a < c := by
  have hac : a <= c := _root_.Rat.le_trans (_root_.Rat.le_of_lt hab) hbc
  apply _root_.Rat.lt_of_le_of_ne hac
  intro hac_eq
  subst hac_eq
  have hab_eq : a = b := _root_.Rat.le_antisymm (_root_.Rat.le_of_lt hab) hbc
  rw [hab_eq] at hab
  exact _root_.Rat.lt_irrefl hab

public theorem add_le_add {a b c d : _root_.Rat}
    (hac : a <= c) (hbd : b <= d) :
    a + b <= c + d := by
  have h1 : a + b <= c + b :=
    (_root_.Rat.add_le_add_right (a := a) (b := c) (c := b)).mpr hac
  have h2 : c + b <= c + d :=
    (_root_.Rat.add_le_add_left (a := b) (b := d) (c := c)).mpr hbd
  exact _root_.Rat.le_trans h1 h2

public theorem add_lt_add {a b c d : _root_.Rat}
    (hac : a < c) (hbd : b < d) :
    a + b < c + d := by
  have h1 : a + b < c + b :=
    (_root_.Rat.add_lt_add_right (a := a) (b := c) (c := b)).mpr hac
  have h2 : c + b < c + d :=
    (_root_.Rat.add_lt_add_left (a := b) (b := d) (c := c)).mpr hbd
  exact lt_trans h1 h2

public theorem le_cases {a b : _root_.Rat} (h : a <= b) :
    Or (a < b) (a = b) :=
  _root_.Rat.le_iff_lt_or_eq.mp h

private theorem lt_eq_gt (a b : _root_.Rat) :
    Or (a < b) (Or (a = b) (b < a)) := by
  cases _root_.Rat.le_total (a := a) (b := b) with
  | inl hab =>
      cases le_cases hab with
      | inl hlt =>
          exact Or.inl hlt
      | inr heq =>
          exact Or.inr (Or.inl heq)
  | inr hba =>
      cases le_cases hba with
      | inl hlt =>
          exact Or.inr (Or.inr hlt)
      | inr heq =>
          exact Or.inr (Or.inl heq.symm)

public theorem neg_nonneg_of_not_nonneg {a : _root_.Rat}
    (h : Not (0 <= a)) :
    0 <= -a := by
  have ha0lt : a < 0 := _root_.Rat.not_le.mp h
  have ha0 : a <= 0 := _root_.Rat.le_of_lt ha0lt
  have hneg : -0 <= -a := _root_.Rat.neg_le_neg ha0
  simpa [_root_.Rat.neg_zero] using hneg

private theorem two_eq_one_add_one : (2 : _root_.Rat) = 1 + 1 := by
  simp [_root_.Rat.add_def']
  rfl

public theorem mul_two (q : _root_.Rat) : q * 2 = q + q := by
  rw [two_eq_one_add_one]
  rw [_root_.Rat.mul_add]
  simp

public theorem sub_one_lt (a : _root_.Rat) : a - 1 < a := by
  apply (_root_.Rat.sub_lt_iff (a := a) (b := a) (c := 1)).mpr
  have h01 : (0 : _root_.Rat) < 1 := by decide
  have h : a + 0 < a + 1 :=
    (_root_.Rat.add_lt_add_left (a := 0) (b := 1) (c := a)).mpr h01
  rw [_root_.Rat.add_zero] at h
  exact h

/-- Between two rationals lies their midpoint `(a + b) / 2`, the witness the
density arguments of the backends use. -/
public theorem exists_between {a b : _root_.Rat} (h : a < b) :
    Exists (fun c : _root_.Rat => And (a < c) (c < b)) := by
  let c := (a + b) / 2
  have htwo : (0 : _root_.Rat) < 2 := by decide
  have ha2 : a * 2 < a + b := by
    have haa : a + a < a + b :=
      (_root_.Rat.add_lt_add_left (a := a) (b := b) (c := a)).mpr h
    rw [mul_two]
    exact haa
  have h2b : a + b < b * 2 := by
    have hab : a + b < b + b :=
      (_root_.Rat.add_lt_add_right (a := a) (b := b) (c := b)).mpr h
    rw [mul_two]
    exact hab
  refine Exists.intro c ?_
  constructor
  · exact (_root_.Rat.lt_div_iff htwo).mpr ha2
  · exact (_root_.Rat.div_lt_iff htwo).mpr h2b

/-- The arithmetic progression `a`, `a + δ`, `a + 2δ`, ... indexed by `Nat`.
The Dedekind backend walks it upward until it leaves a cut, and the Cauchy
supremum construction walks it until it first bounds a set from above. -/
public def step (a δ : _root_.Rat) : Nat -> _root_.Rat
  | 0 => a
  | n + 1 => step a δ n + δ

private theorem step_eq (a δ : _root_.Rat) (n : Nat) :
    step a δ n = a + (n : _root_.Rat) * δ := by
  induction n with
  | zero =>
      simp [step, _root_.Rat.add_zero, _root_.Rat.zero_mul]
  | succ n ih =>
      rw [step, ih]
      rw [_root_.Rat.natCast_add]
      rw [_root_.Rat.add_mul]
      change a + ↑n * δ + δ = a + (↑n * δ + 1 * δ)
      rw [_root_.Rat.one_mul]
      rw [_root_.Rat.add_assoc]

/-- Every rational is below some natural number, witnessed by `t.floor + 1`.
This is the Archimedean fact at the rational level, and the Archimedean
arguments of the Dedekind and Cauchy backends reduce to it. -/
public theorem exists_nat_gt (t : _root_.Rat) :
    Exists (fun n : Nat => t < (n : _root_.Rat)) := by
  let z : Int := t.floor + 1
  have htz : t < (z : _root_.Rat) := by
    simpa [z] using _root_.Rat.lt_floor_add_one t
  by_cases hz : z <= 0
  · have hz0 : (z : _root_.Rat) <= 0 := by
      exact _root_.Rat.intCast_le_intCast.mpr hz
    exact Exists.intro 0 (lt_of_lt_of_le htz hz0)
  · have h0z : 0 <= z := Int.le_of_lt (Int.not_le.mp hz)
    let n : Nat := z.toNat
    have hnz : (n : Int) = z := by
      exact Int.toNat_of_nonneg h0z
    have hnzRat : (n : _root_.Rat) = (z : _root_.Rat) := by
      rw [← _root_.Rat.intCast_natCast]
      rw [hnz]
    exact Exists.intro n (by
      rw [hnzRat]
      exact htz)

/-- Stepping from `a` by a positive `δ` eventually passes any `b`. Combines
`exists_nat_gt` with the closed form `step a δ n = a + n * δ`. -/
public theorem exists_step_gt (a b δ : _root_.Rat) (hδ : 0 < δ) :
    Exists (fun n : Nat => b < step a δ n) := by
  cases exists_nat_gt ((b - a) / δ) with
  | intro n hn =>
      have hsub : b - a < (n : _root_.Rat) * δ :=
        (_root_.Rat.div_lt_iff hδ).mp hn
      have hbna : b < (n : _root_.Rat) * δ + a :=
        (_root_.Rat.sub_lt_iff
          (a := b) (b := (n : _root_.Rat) * δ) (c := a)).mp hsub
      have hban : b < a + (n : _root_.Rat) * δ := by
        rw [_root_.Rat.add_comm] at hbna
        exact hbna
      refine Exists.intro n ?_
      rw [step_eq]
      exact hban

public theorem half_pos {ε : _root_.Rat} (hε : 0 < ε) :
    0 < ε / 2 := by
  have htwo : (0 : _root_.Rat) < 2 := by decide
  apply (_root_.Rat.lt_div_iff htwo).mpr
  rw [_root_.Rat.zero_mul]
  exact hε

public theorem half_lt {ε : _root_.Rat} (hε : 0 < ε) :
    ε / 2 < ε := by
  have htwo : (0 : _root_.Rat) < 2 := by decide
  apply (_root_.Rat.div_lt_iff htwo).mpr
  rw [mul_two]
  have h : ε + 0 < ε + ε :=
    (_root_.Rat.add_lt_add_left (a := 0) (b := ε) (c := ε)).mpr hε
  rw [_root_.Rat.add_zero] at h
  exact h

public theorem mul_le_mul_of_le_of_le_of_pos_of_pos {a b c d : _root_.Rat}
    (hac : a <= c)
    (hbd : b <= d)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b <= c * d := by
  have hleft : a * b <= c * b := by
    cases le_cases hac with
    | inl haclt =>
        exact _root_.Rat.le_of_lt
          (_root_.Rat.mul_lt_mul_of_pos_right
            (a := a) (b := c) (c := b) haclt hb)
    | inr haceq =>
        rw [haceq]
        exact _root_.Rat.le_refl
  have hright : c * b <= c * d := by
    cases le_cases hbd with
    | inl hbdlt =>
        exact _root_.Rat.le_of_lt
          (_root_.Rat.mul_lt_mul_of_pos_left
            (a := b) (b := d) (c := c) hbdlt hc)
    | inr hbdeq =>
        rw [hbdeq]
        exact _root_.Rat.le_refl
  exact _root_.Rat.le_trans hleft hright

public theorem mul_lt_mul_of_lt_of_lt_of_pos_of_pos {a b c d : _root_.Rat}
    (hac : a < c)
    (hbd : b < d)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b < c * d := by
  have hleft : a * b < c * b :=
    _root_.Rat.mul_lt_mul_of_pos_right (a := a) (b := c) (c := b) hac hb
  have hright : c * b < c * d :=
    _root_.Rat.mul_lt_mul_of_pos_left (a := b) (b := d) (c := c) hbd hc
  exact lt_trans hleft hright

public theorem mul_lt_of_lt_one_of_pos {a b : _root_.Rat}
    (ha : a < 1) (hb : 0 < b) :
    a * b < b := by
  have h : a * b < 1 * b :=
    _root_.Rat.mul_lt_mul_of_pos_right (a := a) (b := 1) (c := b) ha hb
  rw [_root_.Rat.one_mul] at h
  exact h

/-- A strict product bound `q < r` with `q >= 0` survives shrinking: some
multiplier with `0 < a < 1` still has `q < a * r`. The witness is any
rational between `q / r` and `1`. -/
public theorem exists_pos_lt_one_mul_gt {q r : _root_.Rat}
    (h0q : 0 <= q)
    (hqr : q < r) :
    Exists (fun a => And (0 < a) (And (a < 1) (q < a * r))) := by
  have h0r : 0 < r := lt_of_le_of_lt h0q hqr
  have hqdiv1 : q / r < 1 := by
    apply (_root_.Rat.div_lt_iff h0r).mpr
    rw [_root_.Rat.one_mul]
    exact hqr
  cases exists_between hqdiv1 with
  | intro a ha =>
      have h0qdiv : 0 <= q / r := by
        apply _root_.Rat.not_lt.mp
        intro hdiv0
        have hq0 : q < 0 := by
          have h : q < 0 * r := (_root_.Rat.div_lt_iff h0r).mp hdiv0
          rw [_root_.Rat.zero_mul] at h
          exact h
        exact (_root_.Rat.not_lt.mpr h0q) hq0
      have h0a : 0 < a := lt_of_le_of_lt h0qdiv ha.left
      have hqar : q < a * r := (_root_.Rat.div_lt_iff h0r).mp ha.left
      exact Exists.intro a (And.intro h0a (And.intro ha.right hqar))

/-- When `q < a * t` with `q >= 0` and `a > 0`, the second factor can be
lowered: some `d < t` still has `q < a * d`. Any rational between `q / a` and
`t` serves as the witness. -/
public theorem exists_pos_lt_of_lt_mul_left {q a t : _root_.Rat}
    (h0q : 0 <= q)
    (ha : 0 < a)
    (hqt : q < a * t) :
    Exists (fun d => And (0 < d) (And (q < a * d) (d < t))) := by
  have hqdivt : q / a < t := by
    apply (_root_.Rat.div_lt_iff ha).mpr
    rw [_root_.Rat.mul_comm]
    exact hqt
  cases exists_between hqdivt with
  | intro d hd =>
      have h0qdiv : 0 <= q / a := by
        apply _root_.Rat.not_lt.mp
        intro hdiv0
        have hq0 : q < 0 := by
          have h : q < 0 * a := (_root_.Rat.div_lt_iff ha).mp hdiv0
          rw [_root_.Rat.zero_mul] at h
          exact h
        exact (_root_.Rat.not_lt.mpr h0q) hq0
      have h0d : 0 < d := lt_of_le_of_lt h0qdiv hd.left
      have hqad : q < a * d := by
        have hqda : q < d * a := (_root_.Rat.div_lt_iff ha).mp hd.left
        rw [_root_.Rat.mul_comm] at hqda
        exact hqda
      exact Exists.intro d (And.intro h0d (And.intro hqad hd.right))

/-- The mirror of `exists_pos_lt_of_lt_mul_left` with the two factors
swapped, so that callers need not commute the product first. -/
public theorem exists_pos_lt_of_lt_mul_right {q t c : _root_.Rat}
    (h0q : 0 <= q)
    (hc : 0 < c)
    (hqt : q < t * c) :
    Exists (fun d => And (0 < d) (And (q < d * c) (d < t))) := by
  have hqct : q < c * t := by
    rw [_root_.Rat.mul_comm]
    exact hqt
  cases exists_pos_lt_of_lt_mul_left (q := q) (a := c) (t := t) h0q hc hqct with
  | intro d hd =>
      have hqdc : q < d * c := by
        have hqcd : q < c * d := hd.right.left
        rw [_root_.Rat.mul_comm] at hqcd
        exact hqcd
      exact Exists.intro d (And.intro hd.left (And.intro hqdc hd.right.right))

/-- A product of rationals boxed inside `[-A, A]` and `[-B, B]` is at most
`A * B`. The four sign cases are what make this more than monotonicity: when
both factors are negative the bound is read off `(-a) * (-b)`, and when the
signs mix the product is nonpositive while `A * B` is not. -/
public theorem mul_upper_of_box {a b A B : _root_.Rat}
    (hA0 : 0 <= A)
    (hB0 : 0 <= B)
    (ha : a <= A)
    (hna : -a <= A)
    (hb : b <= B)
    (hnb : -b <= B) :
    a * b <= A * B := by
  by_cases h0a : 0 <= a
  · by_cases h0b : 0 <= b
    · have hleft : a * b <= A * b :=
        _root_.Rat.mul_le_mul_of_nonneg_right ha h0b
      have hright : A * b <= A * B :=
        _root_.Rat.mul_le_mul_of_nonneg_left hb hA0
      exact _root_.Rat.le_trans hleft hright
    · have hb0 : b <= 0 := nonpos_of_not_nonneg h0b
      have hab0 : a * b <= 0 := mul_nonpos_of_nonneg_of_nonpos h0a hb0
      exact _root_.Rat.le_trans hab0 (_root_.Rat.mul_nonneg hA0 hB0)
  · have ha0 : a <= 0 := nonpos_of_not_nonneg h0a
    by_cases h0b : 0 <= b
    · have hab0 : a * b <= 0 := mul_nonpos_of_nonpos_of_nonneg ha0 h0b
      exact _root_.Rat.le_trans hab0 (_root_.Rat.mul_nonneg hA0 hB0)
    · have h0na : 0 <= -a := neg_nonneg_of_not_nonneg h0a
      have h0nb : 0 <= -b := neg_nonneg_of_not_nonneg h0b
      have hleft : (-a) * (-b) <= A * (-b) :=
        _root_.Rat.mul_le_mul_of_nonneg_right hna h0nb
      have hright : A * (-b) <= A * B :=
        _root_.Rat.mul_le_mul_of_nonneg_left hnb hA0
      rw [mul_eq_neg_neg_mul a b]
      exact _root_.Rat.le_trans hleft hright

/-- The boxed bound for `-(a * b)`, obtained by running `mul_upper_of_box` on
`-a`. Together the two give `|a * b| <= A * B`, the estimate on which the
regularity of products of sequences runs. -/
public theorem neg_mul_upper_of_box {a b A B : _root_.Rat}
    (hA0 : 0 <= A)
    (hB0 : 0 <= B)
    (ha : a <= A)
    (hna : -a <= A)
    (hb : b <= B)
    (hnb : -b <= B) :
    -(a * b) <= A * B := by
  have h := mul_upper_of_box (a := -a) (b := b) (A := A) (B := B)
    hA0 hB0 (by simpa using hna) (by simpa [_root_.Rat.neg_neg] using ha) hb hnb
  simpa [_root_.Rat.neg_mul] using h

public theorem inv_pos {a : _root_.Rat} (ha : 0 < a) :
    0 < a⁻¹ :=
  (_root_.Rat.inv_pos (a := a)).mpr ha

public theorem inv_lt_inv_of_pos_lt {a b : _root_.Rat}
    (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    b⁻¹ < a⁻¹ := by
  rw [← _root_.Rat.one_mul (a⁻¹)]
  rw [← _root_.Rat.div_def 1 a]
  apply (_root_.Rat.lt_div_iff ha).mpr
  have h : a / b < 1 := by
    apply (_root_.Rat.div_lt_iff hb).mpr
    rw [_root_.Rat.one_mul]
    exact hab
  rw [_root_.Rat.div_def] at h
  rw [_root_.Rat.mul_comm] at h
  exact h

public theorem lt_of_inv_lt_inv_of_pos {a b : _root_.Rat}
    (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ < b⁻¹) :
    b < a := by
  cases lt_eq_gt a b with
  | inl hab =>
      have hba : b⁻¹ < a⁻¹ := inv_lt_inv_of_pos_lt ha hb hab
      exact False.elim (_root_.Rat.lt_irrefl (lt_trans h hba))
  | inr hrest =>
      cases hrest with
      | inl hab_eq =>
          rw [hab_eq] at h
          exact False.elim (_root_.Rat.lt_irrefl h)
      | inr hba =>
          exact hba

private theorem mul_inv_cancel_of_pos {a : _root_.Rat} (ha : 0 < a) :
    a * a⁻¹ = 1 :=
  _root_.Rat.mul_inv_cancel a (_root_.Rat.ne_of_gt ha)

/-- The difference of two positive inverses as a single fraction with
numerator `b - a`. The reciprocal estimates in the Cauchy inversion proof
start from this identity. -/
public theorem inv_sub_inv_eq {a b : _root_.Rat} (ha : 0 < a) (hb : 0 < b) :
    a⁻¹ - b⁻¹ = (b - a) * (a * b)⁻¹ := by
  calc
    a⁻¹ - b⁻¹ = a⁻¹ + -b⁻¹ := by rw [_root_.Rat.sub_eq_add_neg]
    _ = b * (b⁻¹ * a⁻¹) + (-a) * (b⁻¹ * a⁻¹) := by
      conv =>
        rhs
        rw [← _root_.Rat.mul_assoc b b⁻¹ a⁻¹]
        rw [mul_inv_cancel_of_pos hb]
        rw [_root_.Rat.one_mul]
        rw [_root_.Rat.neg_mul]
        rw [← _root_.Rat.mul_assoc a b⁻¹ a⁻¹]
        rw [_root_.Rat.mul_comm a b⁻¹]
        rw [_root_.Rat.mul_assoc b⁻¹ a a⁻¹]
        rw [mul_inv_cancel_of_pos ha]
        rw [_root_.Rat.mul_one]
    _ = (b + -a) * (b⁻¹ * a⁻¹) := by
      rw [_root_.Rat.add_mul]
    _ = (b - a) * (a * b)⁻¹ := by
      rw [_root_.Rat.sub_eq_add_neg]
      rw [_root_.Rat.inv_mul_rev]

/-- The excess of `a * b⁻¹` over `1` equals `(a - b) * b⁻¹`, the form in
which the reciprocal comparisons of the Cauchy inversion proof are run. -/
public theorem mul_inv_sub_one_eq {a b : _root_.Rat} (hb : 0 < b) :
    a * b⁻¹ - 1 = (a - b) * b⁻¹ := by
  rw [_root_.Rat.sub_eq_add_neg, _root_.Rat.sub_eq_add_neg]
  rw [_root_.Rat.add_mul]
  rw [_root_.Rat.neg_mul]
  rw [mul_inv_cancel_of_pos hb]

/-- An inverse bound caps a product: `a <= r`, `b > 0` and `b < r⁻¹` give
`a * b < 1`. The proof squeezes `a * b <= r * b < r * r⁻¹ = 1`. -/
public theorem mul_lt_one_of_le_of_pos_of_lt_inv {a b r : _root_.Rat}
    (har : a <= r) (hb : 0 < b) (hr : 0 < r) (hbr : b < r⁻¹) :
    a * b < 1 := by
  have hleft : a * b <= r * b :=
    _root_.Rat.mul_le_mul_of_nonneg_right har (_root_.Rat.le_of_lt hb)
  have hright : r * b < r * r⁻¹ :=
    _root_.Rat.mul_lt_mul_of_pos_left (a := b) (b := r⁻¹) (c := r) hbr hr
  rw [mul_inv_cancel_of_pos hr] at hright
  exact lt_of_le_of_lt hleft hright

private theorem sub_sub_self (b c : _root_.Rat) :
    b - (b - c) = c := by
  rw [_root_.Rat.sub_eq_add_neg]
  rw [_root_.Rat.sub_eq_add_neg]
  rw [_root_.Rat.neg_add]
  rw [← _root_.Rat.add_assoc]
  rw [_root_.Rat.add_neg_cancel]
  rw [_root_.Rat.zero_add]
  rw [_root_.Rat.neg_neg]

private theorem mul_complement (q b : _root_.Rat) :
    q * b + (1 - q) * b = b := by
  rw [← _root_.Rat.add_mul]
  have h : q + (1 - q) = 1 := by
    rw [_root_.Rat.sub_eq_add_neg]
    rw [← _root_.Rat.add_assoc]
    rw [_root_.Rat.add_comm q 1]
    rw [_root_.Rat.add_assoc]
    rw [_root_.Rat.add_neg_cancel]
    rw [_root_.Rat.add_zero]
  rw [h]
  rw [_root_.Rat.one_mul]

/-- A convex-combination estimate: if the gap `b - c` falls below the
complementary share `(1 - q) * l` of some `l < b`, then `q * b < c`. It runs
on the identity `q * b + (1 - q) * b = b`; the lower half of the inverse law
for positive cuts in the Dedekind backend converts rational gaps through
it. -/
public theorem mul_lt_of_gap {q c b l : _root_.Rat}
    (hq1 : q < 1) (hlb : l < b) (hgap : b - c < (1 - q) * l) :
    q * b < c := by
  have hpos : 0 < 1 - q := (_root_.Rat.lt_iff_sub_pos q 1).mp hq1
  have hfactor : (1 - q) * l < (1 - q) * b :=
    _root_.Rat.mul_lt_mul_of_pos_left (a := l) (b := b) (c := 1 - q) hlb hpos
  have hgap2 : b - c < (1 - q) * b := lt_trans hgap hfactor
  have hsum : q * b + (b - c) < q * b + (1 - q) * b :=
    (_root_.Rat.add_lt_add_left
      (a := b - c) (b := (1 - q) * b) (c := q * b)).mpr hgap2
  rw [mul_complement q b] at hsum
  have hsub : q * b < b - (b - c) :=
    (_root_.Rat.lt_sub_right_iff_add_lt
      (a := q * b) (b := b - c) (c := b)).mpr hsum
  rw [sub_sub_self b c] at hsub
  exact hsub

public theorem sub_lt_sub_left_of_lt {a c b : _root_.Rat} (hac : a < c) :
    b - c < b - a := by
  apply (_root_.Rat.sub_lt_iff (a := b) (b := b - a) (c := c)).mpr
  have h : (b - a) + a < (b - a) + c :=
    (_root_.Rat.add_lt_add_left (a := a) (b := c) (c := b - a)).mpr hac
  rw [_root_.Rat.sub_add_cancel] at h
  exact h

end Rat
end ModuleBackend
end RealBasic
end Tautology
