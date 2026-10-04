import Tengoku
import Tengoku.Certifyinginvariantsnf.IdealArithmetic.DedekindProject.Polynomial.PolynomialsAsLists

open Polynomial

/- !

# Sturm's Theorem

In this file, we develop some theory about real closed fields and prove a version of Sturm's theorem to
count the roots of a polynomial in an interval.

## Remark
Note that an alternative definition `IsRealClosed` now exists in Mathlib by
Artie Khovanov, which was developed in parallel to this formalization.
Some of our formalized results, like the proofs leading to `mean_value_theorem`,
are now part of the repository mantained by Artie Khovanov on real closed fields,
for an  eventual PR to Mathlib.

## Main Definitions:
- `IsRealClosedField`: A totally ordered field is a real closed field if it satisfies
  the intermediate value theorem for polynomial functions.
- `signChanges` : The number of sign changes in a sequence.
- `IsSturmSequence` : A predicate on a list of polynomials, stating that it is a sturm sequence.
- `SturmBuilderOfList`: a structure that builds a sturm sequence in a computable way.

## Main Results:
- `mean_value_theorem` : the mean value theorem for polynomial functions in real closed fields.
- `sturm_theorem` : given a sturm sequence starting with `f` and `derivative f`,
  the number of roots of the polynomial in an interval `[a,b]` is given by the difference of
  sign changes in the sequence evaluated at `a` and `b`.
  * We assume that none of the polynomials in the sequence vanish at `a` nor `b`. This is to avoid the
    technical difficulties of working with the sign changes of lists with zeros.
- `sturm_theorem_total` : Sturm's theorem for the interval `(-∞, ∞)`.
- `sturm_theorem_map`: if the polynomial is defined over a subring of a real closed field, then this result allows
  us to perform all of the computations in this subring. This is useful for polynomials over `ℤ` as
  we do not want to compute in `ℝ` where we do not have decidable equality.

## Examples:
- `real_roots1`: the polynomial `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` has `1` real root in `(-∞, ∞)`.
- `real_roots2`: the polynomial `X ^ 8 - X ^ 7 - 3 * X ^ 6 + 3 * X ^ 5 + 3 * X ^ 4 - 6 * X ^ 3 - 2 * X ^ 2 + 3 * X + 1`
    has `4` real root in `(-∞, ∞)`.

## Notes
- The remark in `sturm_theorem` does not represent a big impediment in applications.
  If one wants to prove that the number of roots of `P` in the interval `[a,b]`
  (where `a` and `b` are not roots of `P`) is equal to `n`, and `a` happens to be a root of one of the
  polynomials in the sequence, then one can choose an appropiate
  `ε > 0` and count roots in `[a - ε, b + ε ]`and `[a + ε, b - ε ]`.
- For the proof of Sturm's theorem, we follows a similar path to `John Harrison` proof in HOL.
- For proving `Rolle's theorem` and the `Mean value theorem` we follow a similar strategy as
  `Assia Mahboubi` and `Cyril Cohen's`, Formal proofs in real algebraic geometry.

## Related work:
* Verifying accuracy of polynomial approximations in HOl -- `John Harrison` (1997).
  Sturm's theorem is proven over the real numbers.
* A Formalisation of Sturm’s Theorem -- `Manuel Eberl` (2014)
* It has also been formalized by NASA researchers in Langley (2014)
* `Assia Mahboubi` and `Cyril Cohen` formalized sign changes of pseudo-remainder sequences
 in Coq over real closed fields. Sturm theorem is a corollary of these results.-/

def IsRealClosedField (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
    ∀ {a b t : F} , ∀ {P : F[X]},
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b) → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t

lemma Real.IsRealClosedField : IsRealClosedField ℝ := by
  rintro a b t P hab h
  let f : ℝ → ℝ := fun x => P.eval x
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo hab (f := f) (Polynomial.continuousOn P ) h)

namespace IsRealClosedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
open Set

lemma polynomial_has_root_of_le_zero_of_pos (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩

lemma intermediate_value_theorem_swap (hc : IsRealClosedField F) {a b t : F} (hab : a ≤ b)
    {P : F[X]} (hmem : t ∈ Set.Ioo (P.eval b) (P.eval a)) : ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b (-t) (- P) hab (by simp [hmem.1, hmem.2])
  simp at hs2
  exact ⟨s, hs1, hs2⟩

lemma sign_ne_eq_iff_of_ne_zero {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ≠ b ↔ a * b = - 1 := by
  cases a ;
  cases b ; simp ; simp at ha ; simp at ha
  cases b ; simp at hb ; simp ; simp
  cases b ; simp at hb ; simp ; simp

lemma polynomial_has_root_of_mul_neg (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (habm : (P.eval a) * (P.eval b) < 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rcases lt_trichotomy (P.eval a) 0 with hl1 | hl2 | hl3
  · have : eval b P > 0 := by nlinarith
    exact polynomial_has_root_of_le_zero_of_pos hc hab hl1 this
  · simp[hl2] at habm
  · have : eval b P < 0 := by nlinarith
    exact polynomial_has_root_of_pos_le_zero hc hab hl3 this

lemma polynomial_has_root_of_ne_sign (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hne : SignType.sign (P.eval a) ≠ SignType.sign (P.eval b)) (hanz : P.eval a ≠ 0)
    (hbnz : P.eval b ≠ 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rw [sign_ne_eq_iff_of_ne_zero (by simp[hanz]) (by simp[hbnz] ), ← sign_mul,
    sign_eq_neg_one_iff] at hne
  exact polynomial_has_root_of_mul_neg hc hab hne

lemma neg_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Ioo a b , P.eval x < 0 := by
  intro x hx
  by_contra! hc'
  rcases le_iff_lt_or_eq.1 hc' with hz1 | hz2
  · rcases le_or_gt m x with hm1 | hm2
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc hm1 hneg hz1
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hm.1 hs1.1, lt_trans hs1.2 hx.2⟩
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm2) hz1 hneg
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hx.1 hs1.1, lt_trans hs1.2 hm.2⟩
  · exact hP x hx hz2.symm

lemma nonpos_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Icc a b , P.eval x ≤ 0 := by
  intro x hmem
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
  · rw [ha]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm.1) hc' hneg
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
  · rw [hb]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm.2) hneg hc'
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
  · exact le_of_lt (neg_of_ne_zero_of_exists_neg hc hP hm hneg x hx)

lemma pos_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  have := neg_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma nonneg_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Icc a b , P.eval x ≥ 0 := by
  have := nonpos_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma constant_sign_of_ne_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Ioo a b , P.eval x > 0) ∨ (∀ x ∈ Ioo a b , P.eval x < 0)  := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact neg_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact pos_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2]

lemma constant_sign_of_ne_zero' (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Icc a b , P.eval x ≥ 0) ∨ (∀ x ∈ Icc a b , P.eval x ≤ 0) := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact nonpos_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact nonneg_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2, LinearOrder.le_total 0 (eval b P)]

/- Weak version of Rolle's theorem for successive roots. -/
open Finset

/- Rolle's  theorem for polynomials  -/

/- Mean value theorem for polynomials -/

end IsRealClosedField

section signChanges

section

variable {R : Type*}  [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]

-- Similar to Coq (residue sequences)
def signChanges' (L : List R) : ℕ :=
  match L  with
  | [] => 0
  | (a :: as) => if SignType.sign a * SignType.sign (as.headD 0) < 0 then 1 + signChanges' as else signChanges' as

def signChanges (L : List R) : ℕ  :=
  signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L)

lemma signChanges_def (L : List R) : signChanges L = signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L) := by
  rfl

lemma signChanges_eq_signChanges' (L : List R) (hz : ∀ x ∈ L, x ≠ 0) : signChanges L = signChanges' L := by
  rw [signChanges_def]
  congr ; simp ; exact hz

end

--set_option trace.profiler true

--#count_heartbeats
--example : SignType.sign (123457738291098765612345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656 : ℚ)* SignType.sign (-345678998765678912345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656) < 0 := by decide

-- unseal Rat.mul
-- example : (123457738291098765612345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656 : ℚ) * (-345678998765678912345773829109876561234577382910987656123457738291098765612345773829109876561234577382910987656) < 0 := by decide

section
variable{R : Type*} [CommRing R] [LinearOrder R]

open SignType

/- The sign changes of a polynomial sequence at `a` is simply the sign changes of the resulting
list when evaluating the polys at `a` -/
def signChangesPolySeq (P : List R[X]) (a : R) : ℕ :=
  signChanges (List.map (fun x => x.eval a) P)

lemma signChangesPolySeq_def (P : List R[X]) (a : R) :
  signChangesPolySeq P a = signChanges (List.map (fun x => x.eval a) P) := rfl

def signChangesInfty (P : List R[X]) : ℕ :=
  signChanges (List.map (fun p => p.leadingCoeff) P)

lemma signChangesInfty_def (P : List R[X]) : signChangesInfty P =
  signChanges (List.map (fun p => p.leadingCoeff) P) := rfl

def signChangesNInfty (P : List R[X]) : ℕ :=
  signChanges (List.map (fun p => (-1) ^ (p.natDegree) * p.leadingCoeff) P)

end

section

variable [CommRing R]
/-- A list of polynomials is a sturm sequence starting with `p` and `q`
  if it has length at least two, it ends in a non-zero constant polynomial, it has strictly decreasing degree
  and `Pᵢ₊₁ ∣ (e₁ * Pᵢ + fᵢ * Pᵢ₊₂)` with `eᵢ` and `f₁` strictly positive numbers. -/
structure IsSturmSequence [LinearOrder R] (P : List R[X]) (p q : R[X])  where
  hlen : 2 ≤ P.length
  h0 : P[0] = p
  h1 : P[1] = q
  hc : ∃ c : R, c ≠ 0 ∧ P.getLastD 0 = C c
  hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree
  hrem : ∀ i, ∀ h2 : i + 2 < P.length ,
    (∃ e f : R, ∃ Q : R[X], 0 < e ∧ 0 < f ∧ C e * P[i] = Q * P[i + 1] - C f * P[i + 2] )

lemma sturm_sequence_ne_nil [LinearOrder R] {P : List R[X]} {p q : R[X]}
  (hs : IsSturmSequence P p q) : P ≠ [] := by
  have := hs.hlen
  intro h
  simp only [h, List.length_nil, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at this

lemma getLastD_eq_getLast_of_ne_nil {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
  l.getLastD a = l.getLast h := by
  match l with
  | [] => contradiction
  | (b :: bs) =>
    match bs with
    | [] => simp
    | (c :: cs) =>
    rw [List.getLast_eq_getLastD, List.getLastD_cons]

lemma zero_not_member_of_mono {P : List R[X]}
  (hlen : 2 ≤ P.length)
  (hc : ∃ c : R, c ≠ 0 ∧ P.getLastD 0 = C c)
  (hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree) : ¬ 0 ∈ P := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hile, hi⟩ := h
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    have hsl :=hlen
    obtain ⟨c, hcz, hzl⟩ := hc
    rw [← List.getLast_eq_getElem (fun  h => by simp [h] at hsl)] at hi
    rw [getLastD_eq_getLast_of_ne_nil (by grind), hi, Eq.comm,
      Polynomial.C_eq_zero] at hzl
    exact hcz hzl
  · have := hmono i (by omega)
    rw [hi] at this
    simp at this

variable [LinearOrder R]

/-- The zero polynomial is not in a sturm sequence. -/
lemma zero_not_member {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : ¬ 0 ∈ P := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hile, hi⟩ := h
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    have hsl := hs.hlen
    obtain ⟨c, hcz, hzl⟩ := hs.hc
    rw [← List.getLast_eq_getElem (fun  h => by simp [h] at hsl)] at hi
    rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil hs), hi, Eq.comm,
      Polynomial.C_eq_zero] at hzl
    exact hcz hzl
  · have := hs.hmono i (by omega)
    rw [hi] at this
    simp at this

lemma zero_not_member' {P : List R[X]} {p q : R[X]}
  (hs : IsSturmSequence P p q) (i : ℕ) (hi : i < P.length) : P[i] ≠ 0 := by
  intro h
  have : P[i] ∈ P := List.getElem_mem hi
  exact zero_not_member hs (h ▸ this)

lemma p_ne_zero {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : p ≠ 0 := by
  rw [← hs.h0]
  have hPl := hs.hlen
  have : P[0] ∈ P := by simp
  intro h
  rw [h] at this
  exact zero_not_member hs this

lemma q_ne_zero {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : q ≠ 0 := by
  rw [← hs.h1]
  have hPl := hs.hlen
  have : P[1] ∈ P := by simp
  intro h
  rw [h] at this
  exact zero_not_member hs this

 lemma IsSturmSequence_map {S : Type*} [CommRing S] [LinearOrder S]  {P : List R[X]}
    {p q : R[X]} (h : IsSturmSequence P p q) (f : R →+* S) (hmono : StrictMono f) :
    IsSturmSequence (List.map (Polynomial.map f) P) (map f p) (map f q) where
  hlen := by simp[h.hlen]
  h0 := by simp [h.h0]
  h1 := by simp only [List.getElem_map]  ; simp_rw [← h.h1]
  hc := by
    obtain ⟨c, hc1, hc2⟩ := h.hc
    use f c
    constructor
    · refine (map_ne_zero_iff f (StrictMono.injective hmono)).mpr hc1
    · rw [getLastD_eq_getLast_of_ne_nil (by simp ; exact sturm_sequence_ne_nil h)]
      simp
      rw[← getLastD_eq_getLast_of_ne_nil (a := 0) (sturm_sequence_ne_nil h), hc2, map_C]
  hmono := by
    intro i hi
    simp at hi
    simp only [List.getElem_map, Polynomial.natDegree_map_eq_of_injective (StrictMono.injective hmono)]
    exact h.hmono i hi
  hrem := by
    intro i hi
    simp at hi
    obtain ⟨e, ft, Q, hepos, hfpos, heq⟩ := h.hrem i hi
    use f e, f ft , map f Q
    refine ⟨?_, ?_, ?_ ⟩
    · convert StrictMono.imp hmono hepos
      rw [map_zero]
    · convert StrictMono.imp hmono hfpos
      rw [map_zero]
    · simp
      rw[← map_C, ← Polynomial.map_mul, heq]
      simp

/-- A sturm sequence evaluated at any element `a` cannot have two consecutive zeros. -/
lemma no_consecutive_zero1 [IsStrictOrderedRing R] (P : List R[X]) (p q : R[X])
    (hs : IsSturmSequence P p q) (a : R) (i : ℕ)
    (hlen : i + 1 < P.length) (hz : P[i + 1].eval a = 0) : P[i].eval a ≠ 0 := by
  revert i
  by_contra! hc
  obtain ⟨i, hle, heval1, heval2⟩ := hc
  have hin : ∀ j, ∀ hj : i + j < P.length , P[i + j].eval a = 0 := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | h j hjin =>
      match j with
      | 0 => exact heval2
      | 1 => exact heval1
      | j + 1 + 1 =>
      have := hjin j (by omega) (by omega)
      have :=  hjin (j + 1) (by omega) (by omega)
      obtain ⟨e, f, Q, hepos, hfpos, hef⟩ := hs.hrem (i + j) (by omega)
      apply_fun (fun (x : R[X]) => x.eval a) at hef
      simp at hef
      simp_rw [ hjin j (by omega) (by omega), add_assoc, hjin (j + 1) (by omega) (by omega)  ] at hef
      simp[Ne.symm (ne_of_lt hfpos)] at hef
      exact hef
  obtain ⟨c, hcz, hzl⟩ := hs.hc
  rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil hs), List.getLast_eq_getElem] at hzl
  have aux := hin (P.length- 1 - i) (by omega)
  have : i + (P.length - 1 - i) = P.length - 1 := by omega
  simp_rw [this, hzl] at aux
  simp only [eval_C] at aux
  exact hcz aux

lemma sturm_sequence_cons (P : List R[X]) (p q : R[X]) (a : R[X]) (hPl : 2 ≤ P.length)
    (hs : IsSturmSequence (a :: P) p q) : IsSturmSequence P q P[1] where
  hlen := hPl
  h0 := by rw [← List.getElem_cons_succ a ] ; exact hs.h1
  h1 := rfl
  hc := by
    have : P ≠ [] := fun h => by rw [h] at hPl ; simp at hPl
    obtain ⟨c, neq, hcl⟩  := hs.hc
    rw [List.getLastD_cons, getLastD_eq_getLast_of_ne_nil this] at hcl
    simp_rw [getLastD_eq_getLast_of_ne_nil this]
    exact ⟨c, neq, hcl⟩
  hmono := by
    intro i h
    have := hs.hmono (i + 1) (by simp ; omega)
    simp at this
    exact this
  hrem := by
    intro i h
    obtain ⟨e, f, Q, hepos, hfpos, heq⟩  := hs.hrem (i + 1) (by simp ; omega)
    simp at heq
    exact ⟨e, f, Q, hepos, hfpos, heq⟩

end

open SignType

variable {R : Type*}

@[simp]
lemma signChanges_nil [Zero R] [Preorder R] [DecidableLT R]  [DecidableEq R]
  : signChanges (R := R) [] = 0 := rfl

@[simp]
lemma signChanges_single' [Zero R] [Preorder R] [DecidableLT R]  (a : R) : signChanges' [a] = 0 := by
  simp[signChanges']

@[simp]
lemma signChanges_single [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R] (a : R)
  : signChanges [a] = 0 := by
  by_cases ha : a ≠ 0
  · simp[signChanges, ha]
  · push Not at ha
    simp [signChanges, signChanges', ha]

lemma signChanges_zero_head [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  (as : List R)  : signChanges (0 :: as) = signChanges as := by
  unfold signChanges
  simp

lemma signChanges_zero_head' [Zero R] [Preorder R] [DecidableLT R] (as : List R) :
  signChanges' (0 :: as) = signChanges' as := by
  simp_rw [signChanges', sign_zero, zero_mul]
  rfl

lemma signChanges_length_two  [DecidableEq R] [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
   (a b : R) (hab : a * b < 0) : signChanges [a, b] = 1 := by
  have : a ≠ 0 ∧ b ≠ 0 := by
    by_contra! hc
    by_cases haz : a = 0
    · simp [haz] at hab
    · simp [hc haz] at hab
  rw [signChanges_eq_signChanges']
  simp [signChanges']
  simp [← sign_mul, hab]
  simp[this]

lemma signChanges_modify_zero [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  (a : R) (bs : List R) :
  signChanges (a :: 0 :: bs) = signChanges (a :: bs) := by
  by_cases ha : a = 0
  · rw [ha, signChanges_zero_head]
  · have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: 0 :: bs) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) bs) := by
      simp only [ne_eq, ite_not, Bool.ite_true_right, Bool.or_false, ha, decide_false,
        Bool.not_false, List.filter_cons_of_pos, decide_true, Bool.not_true, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg]
    simp_rw [signChanges, aux]
    simp[ha]

lemma signChanges_cons [Zero R] [Preorder R] [DecidableLT R] [DecidableEq R]
  {a : R} {as : List R} (ha : a ≠ 0) (hh : as.headD 0 ≠ 0) :
  signChanges (a :: as) = if sign a * sign (as.headD 0) < 0 then 1 + signChanges as else signChanges as := by
  have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: as) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) as) := by
    simp[ha]
  have aux2 : (List.filter (fun x => if x ≠ 0 then true else false) as).headD 0 = as.headD 0 := by
    match as with
    | [] => simp
    | (b :: bs) =>
    simp at hh
    simp[hh]
  unfold signChanges
  rw [aux]
  nth_rw 1 [signChanges']
  simp_rw [aux2]

lemma List.getElem_cons_pred {α : Type* } (a : α) (as : List α) (i : ℕ) (h : i  < (a :: as).length)
  (hi' : i - 1 < as.length) (hi : i ≠ 0) : (a :: as)[i] = as[i - 1] := by
  match i with
  | 0 => contradiction
  | i + 1 => simp

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

lemma signChanges_of_mul_neg [DecidableEq R] {a b c : R}
    (ha : a * c < 0) : signChanges [a, b, c] = 1 := by
    rcases lt_trichotomy b 0 with hb1 | hb2 | hb3
    swap
    · rw [hb2, signChanges_modify_zero, signChanges_length_two _ _ ha]
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb1, hapos.2]
        aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb1, haneg.2]
        aesop
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb3, hapos.2]
        simp ; aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb3, haneg.2]
        aesop

lemma List.three_le_length_iff {α : Type*} {l : List α} :  3 ≤ l.length ↔ ∃ (a b c : α), ∃ (as : List α) ,
  l = (a :: b :: c :: as) := by
  constructor
  · intro hlen
    match l with
    | [] => simp at hlen
    | [a] => simp at hlen
    | [a, b] => simp at hlen
    | (a :: b :: c :: as) =>
    use a , b, c, as
  · rintro ⟨a, b, c, as, has⟩
    simp [has]

-- If I just case match, the proof is too slow.

variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open Set IsRealClosedField

lemma polynomial_change_sign_aux (hc : IsRealClosedField F) {a b e f : F} (P0 P1 P2 Q : F[X])
  (hab : a < b) (hpose : 0 < e ) (hposf : 0 < f) (heq : C e * P0 = Q * P1 - C f * P2)
  (hz0 : ∀ x ∈ Icc a b , P0.eval x ≠ 0) (hz2 : ∀ x ∈ Icc a b , P2.eval x ≠ 0)
  (hP1a : P1.eval a ≠ 0) (hP1b : P1.eval b ≠ 0) (hneq : sign (P1.eval a) ≠ sign (P1.eval b)) :
    (P0.eval a) * (P2.eval a) < 0 ∧ sign (P0.eval a) = sign (P0.eval b) ∧
    sign (P2.eval a) = sign (P2.eval b) := by
  have : (P1.eval a) * (P1.eval b) < 0 := by
    rw [← sign_eq_neg_one_iff, sign_mul, ← sign_ne_eq_iff_of_ne_zero (sign_ne_zero.mpr hP1a)
      (sign_ne_zero.mpr hP1b )]
    exact hneq
  obtain ⟨r, hrmem, hrr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) this
  constructor
  · have aux2 : e * P0.eval r = - f * P2.eval r := by
      rw [← eval_C (x := r) (a := e), ← eval_mul, heq]
      simp[hrr]
    have aux3 : (P0.eval r) * (P2.eval r) < 0 := by
      rw [← (mul_lt_mul_iff_right₀ hpose), ← mul_assoc, aux2]
      simp
      rw [mul_assoc, mul_pos_iff_of_pos_left hposf]
      simp[hz2 _ (mem_Icc_of_Ioo hrmem)]
    refine lt_of_le_of_ne ?_ ?_
    · rw [← eval_mul]
      apply nonpos_of_ne_zero_of_exists_neg hc (P := P0 * P2) ?_ hrmem
      · rw [eval_mul]
        exact aux3
      · simp [le_of_lt hab]
      · simp only [eval_mul, ne_eq, mul_eq_zero, not_or]
        intro x hxmem
        exact ⟨hz0 x (mem_Icc_of_Ioo hxmem), hz2 x (mem_Icc_of_Ioo hxmem)⟩
    · simp
      exact ⟨hz0 a (by simp ; exact le_of_lt hab), hz2 a (by simp ; exact le_of_lt hab)⟩
  · constructor
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz0 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz0 a (by simp ; exact le_of_lt hab)]
      simp [hz0 b (by simp ; exact le_of_lt hab)]
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz2 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz2 a (by simp ; exact le_of_lt hab)]
      simp [hz2 b (by simp ; exact le_of_lt hab)]

open Finset

lemma roots_of_prod_mem_iff (a b : F) (P : List F[X]) (x : F) (hz : 0 ∉ P) :
  x ∈ (((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) ↔
  ∃ i : ℕ , (∃ h : i < P.length, P[i].eval x = 0 ∧ x ∈ Icc a b)  := by
  simp
  have : ∀ x, (Polynomial.aeval x) (P.prod) = (List.map (fun y => y.eval x) P).prod := by
    intro c
    simp [← List.prod_hom]
  rintro hle1 hle2
  simp at this
  simp [this, hz,  List.mem_iff_getElem]

omit [Field F] [IsStrictOrderedRing F]
lemma finset_card_add_interval {a b c : F} (hcmem : c ∈ Icc a b) {S : Finset F} (hcn : c ∉ S)  :
  #(S.filter (fun x => x ∈ Icc a b)) =
    #(S.filter (fun x => x ∈ Icc a c)) + #(S.filter (fun x => x ∈ Icc c b)) := by
  convert Finset.card_union_of_disjoint (α := F) ?_ using 2
  rw [Set.mem_Icc] at hcmem
  · ext x
    simp
    rcases LinearOrder.le_total x c with h1 | h2
    · constructor
      · intro h
        exact Or.inl ⟨h.1, ⟨h.2.1, h1⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h1 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
    · constructor
      · intro h
        exact Or.inr ⟨h.1, ⟨h2, h.2.2⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h3.2.2 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
  · rw [Finset.disjoint_iff_ne]
    intro u hu w hw
    simp at hu hw
    rcases lt_or_eq_of_le (le_trans hu.2.2  hw.2.1) with hc1 | hc2
    · exact ne_of_lt hc1
    · exfalso
      have aux : c = w := by
        rw [hc2] at hu
        grind
      rw [← aux] at hw
      exact hcn hw.1

lemma finset_sorted_list_cons_cons  {F : Type u_2} [Field F] [LinearOrder F]
    {u v : F} {as : List F} {S : Finset F} (heq : S.sort (fun x y => x ≤ y) = (u :: v :: as)) :
    ∀ x ∈ S , x = u ∨ v ≤ x := by
  have aux1 : List.Pairwise (fun x y => x ≤ y) (u :: v :: as) := by
    rw [← heq]
    simp only [pairwise_sort]
  intro x hxmem
  rw [← Finset.mem_sort (r := fun x y => x ≤ y), heq, List.mem_cons] at hxmem
  simp at hxmem
  rcases hxmem with h1 | h2 | h3
  · left
    exact h1
  · right
    exact le_of_eq (id (Eq.symm h2))
  · right
    simp at aux1
    grind

  lemma u_le_v_of_sort  {u v : F} {as : List F}
    {S : Finset F}  (heqc : (u :: v :: as) = (S.sort (fun x y => x ≤ y))) : u < v := by
    have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
    simp at hauxu
    have hauxv := getElem_congr_coll (w := by simp) (i := 1) heqc
    simp at hauxv
    refine lt_of_le_of_ne ?_ ?_
    · simp_rw [hauxu, hauxv]
      rw [Finset.sorted_zero_eq_min']
      refine Finset.min'_le _ _ ?_
      rw [← mem_sort (r := fun x y => x ≤ y) ]
      simp only [List.getElem_mem]
    · have := Finset.sort_nodup S (fun x y => x ≤ y)
      rw [← heqc] at this
      simp at this
      exact this.1.1

lemma not_mem_finset_card_eq_one_of_sorted_mem_interval {a b d u v : F} {as : List F}
  {S : Finset F}  (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∈ Icc a b := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have hauxv := getElem_congr_coll (w := by simp) (i := 1) heqc
  simp at hauxv
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  have hwmem : v ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxv]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem hwmem
  constructor
  · refine le_of_lt (lt_of_le_of_lt humem.2.1 hle1)
  · refine le_of_lt (lt_of_lt_of_le hle2 hwmem.2.2)

lemma not_mem_finset_card_eq_one_of_sorted  {a b d u v : F} [Field F] [IsStrictOrderedRing F] {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) (x : F) :
    x ∈ (S.filter (fun x => x ∈ Icc a d)) ↔ x = u := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem
  have hdmem : d ∈ Icc a b := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  constructor
  · intro h
    simp at h
    obtain ⟨hxmemS, hxa, hxd⟩ := h
    rcases finset_sorted_list_cons_cons heqc.symm x
      (by simp ; exact ⟨hxmemS, ⟨hxa, le_trans hxd hdmem.2⟩⟩) with h1 | h2
    · exact h1
    · linarith
  · intro heq
    simp [heq]
    exact ⟨humem.1, ⟨humem.2.1, le_of_lt hle1⟩⟩

lemma not_mem_finset_card_eq_one_of_sorted_not_mem  {a b d u v : F} [Field F]
  [IsStrictOrderedRing F] {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∉ S := by
  intro hc
  have aux1 := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  have aux2 := not_mem_finset_card_eq_one_of_sorted F heqc hle1 hle2 d
  simp at aux1 aux2
  rw [aux2.1 ⟨hc, aux1.1⟩] at hle1
  simp at hle1

lemma not_mem_finset_card_eq_one_of_sorted_single {a b u : F} {S : Finset F}
  (heq : [u] = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) )
  (x : F) : x ∈ (S.filter (fun x => x ∈ Icc a b)) ↔ x = u := by
  rw [← Finset.mem_sort (r := fun x y => x ≤ y) , ← heq]
  simp

-- Sturm over `(-∞ , ∞)`
lemma pos_at_infinity_of_leading_coeff_pos [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hP : P.leadingCoeff > 0) : ∃ N : F, ∀ x, (N < x → 0 < P.eval x) := by
  have hPnz : P ≠ 0 := by
    intro h
    rw [h] at hP
    simp at hP
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.1 hdeg
    rw [← hc] at hP ⊢
    simp at hP ⊢
    use 1 ; simp[hP]
  · let coeffs : Fin (P.natDegree + 1) → F := fun i => |P.coeff i|
    let y := ∑ i, coeffs i
    have aux : ∀ i : (Fin (P.natDegree + 1)), |P.coeff i| ≤ y := by
      intro i
      refine le_trans ?_ (Finset.sum_le_sum (f := fun j => if j = i then |P.coeff i| else 0) ?_ )
      · simp
      · intro j hj
        by_cases heq : j = i
        · simp [heq, coeffs]
        · simp [heq, coeffs]
    have hyn : - y ≤ 0 := by
      rw [Left.neg_nonpos_iff]
      refine le_trans ?_ (aux ⟨0, by simp⟩)
      exact abs_nonneg _
    have auxle : ∀ i < P.natDegree + 1, - y ≤ P.coeff i := by
      intro i hi
      refine le_trans (neg_le_neg (aux ⟨i, hi⟩ )) ?_
      exact neg_abs_le (P.coeff _)
    let N := (max 2 ((natDegree P) * y * (P.leadingCoeff )⁻¹))
    have None : 1 < N := by
      unfold N
      refine lt_of_lt_of_le (one_lt_two) ?_
      exact le_max_left 2 _
    use N
    intro x hx
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_comm]
    have :  ∑ i ∈ Finset.range P.natDegree, (- y) * x ^ (P.natDegree - 1)
      ≤  ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [mul_comm, mul_comm (P.coeff i)]
      apply mul_le_mul_of_nonneg_of_nonpos
      · refine pow_le_pow_right₀ (le_of_lt (lt_trans None hx)) (by simp at hi ; omega)
      · exact auxle i (by simp at hi ; exact Nat.lt_add_right 1 hi)
      · apply pow_nonneg ; linarith
      · exact hyn
    simp at this
    refine lt_of_lt_of_le ?_ (add_le_add_right this (P.coeff P.natDegree * x ^ P.natDegree))
    simp only [coeff_natDegree, lt_add_neg_iff_add_lt, zero_add]
    nth_rw 3 [← Nat.sub_one_add_one hdeg]
    rw [pow_add, pow_one, mul_comm _ x, ← mul_assoc P.leadingCoeff _, ← mul_assoc]
    refine mul_lt_mul_of_pos_right ?_ (by apply pow_pos ; linarith)
    have hN : (↑P.natDegree * y * P.leadingCoeff⁻¹) ≤ N := by
      unfold N
      exact Std.right_le_max
    suffices (↑P.natDegree * y ≤ P.leadingCoeff * ((↑P.natDegree * y * P.leadingCoeff⁻¹))) by nlinarith
    field_simp
    exact Std.IsPreorder.le_refl y

  lemma neg_at_infinity_of_leading_coeff_neg [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hP : P.leadingCoeff < 0) : ∃ N : F, ∀ x, (N < x → P.eval x < 0) := by
    have := pos_at_infinity_of_leading_coeff_pos F (-P)
    simp at this
    exact this hP

lemma sign_at_infinity_eq_sign_leading_coeff [Field F] [IsStrictOrderedRing F]
  (P : F[X]) (hn : P ≠ 0) : ∃ N : F, ∀ x, N < x  →
    sign (P.eval x) = sign (P.leadingCoeff) ∧ P.eval x ≠ 0 := by
  rcases lt_trichotomy (P.leadingCoeff) 0 with h1 | h2 | h3
  · obtain ⟨N, hn⟩ :=  neg_at_infinity_of_leading_coeff_neg F P h1
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h1]
    exact ne_of_lt hn
  · rw [← Polynomial.leadingCoeff_ne_zero] at hn ; contradiction
  · obtain ⟨N, hn⟩ := pos_at_infinity_of_leading_coeff_pos F P h3
    use N
    intro x hx
    specialize hn x hx
    simp [hn, h3]
    exact ne_of_gt hn

section SturmOfList

variable {R : Type*}  [CommRing R] [LinearOrder R]

structure SturmBuilderOfList (P : List (List R)) (p : List R) (q : List R) where
  hlen : 2 ≤ P.length
  h0 : P[0] = p
  h1 : P[1] = q
  hlast : (P.getLastD []).length = 1
  hdrop : ∀ i , ∀ h : i < P.length, P[i] = (P[i]).dropTrailingZeros'
  hmono :  ∀ i , ∀ h : i + 1 < P.length, P[i + 1].length < P[i].length
  e : List R
  epos : ∀ h : i < e.length , 0 < e[i]
  f : List R
  fpos : ∀ h : i < f.length, 0 < f[i]
  Q : List (List R)
  hel : P.length ≤ e.length + 2
  hfl : P.length ≤ f.length + 2
  hQl : P.length ≤ Q.length + 2
  hrem : ∀ i, ∀ h2 : i + 2 < P.length ,
    P[i].mulPointwise e[i] = Q[i] * P[i + 1] - P[i + 2].mulPointwise (f[i])

lemma SturmBuilderOfList_ne_nil {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) : P ≠ [] := by
  have := h.hlen
  rintro ⟨h, rfl⟩
  simp at this

lemma SturmBuilderOfList_not_mem_nil {P : List (List R)} {p : List R} {q : List R}
  (h : SturmBuilderOfList P p q) (i : ℕ) (hio : i < P.length) : P[i] ≠ [] := by
  intro hi
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    rw [← List.getLast_eq_getElem (SturmBuilderOfList_ne_nil h), ← getLastD_eq_getLast_of_ne_nil (a := [])] at hi
    have := hi ▸ h.hlast
    simp at this
  · have := h.hmono i (by omega)
    rw [hi] at this
    simp at this

def signChangesInftyOfList (P : List (List R)) :=
    signChanges (List.map (fun x => if h : x ≠ [] then x.getLast h else 0) P)

def signChangesNInftyOfList (P : List (List R)) :=
  signChanges (List.map (fun x => if h : x ≠ [] then ((-1 : R) ^ (x.length - 1)) * x.getLast h else 0) P)

def signChangesSeqOfList (P : List (List R)) (a : R) :=
  signChanges (List.map (fun x => x.eval a) P)

/-- EXAMPLE 1:  `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` -/

@[reducible]
def P1 : List (List ℤ):= [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]]

def SturmBuilderExample1 : SturmBuilderOfList [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]] [-8, 9, 0, -3, 0, 1] [9, 0, -9, 0, 5] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 5 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [25, 9, 3969, 9628609]
  f := [10, 3, 15, 208061595]
  epos := by decide
  fpos := by decide
  Q := [[0, 5], [0, 15], [-300, -189], [10924, -195489]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 4 := by omega
    interval_cases i <;> dsimp <;> decide

/-- EXAMPLE 2:  `X^8 - X^7 - 3*X^6 + 3*X^5 + 3*X^4 - 6*X^3 - 2*X^2 + 3*X + 1` -/

@[reducible]
def P2 : List (List ℤ):= [[1, 3, -2, -6, 3, 3, -3, -1, 1], [3, -4, -18, 12, 15, -18, -7, 8],
  [-67, -164, 114, 228, -111, -54, 55], [-191, -392, -193, 384, 777, 48], [971, 1944, 821, -2032, -3741],
  [-14243, -38910, 11875, 48646], [-11255, 808, 33203], [1649, 3522], [1]]

def SturmBuilderExample2 : SturmBuilderOfList P2 [1, 3, -2, -6, 3, 3, -3, -1, 1]
  [3, -4, -18, 12, 15, -18, -7, 8] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    unfold P2 ; dsimp
    intro i hic
    have hi : i < 8 := by omega
    interval_cases i <;> norm_num
  e := [64, 3025, 2304, 13995081, 2366433316, 1102439209, 12404484]
  f := [1, 64, 9075, 3840, 135285783, 7099299948, 54019521241]
  epos := by decide
  fpos := by decide
  Q := [[-1, 8], [47, 440], [-45327, 2640], [-2809221, -179568],
  [-54424297, -181984686], [354979657, 1615193138], [-51905971, 116940966]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    unfold P2 ; dsimp
    intro i hi
    have hi : i < 7 := by omega
    interval_cases i <;> dsimp <;> decide
