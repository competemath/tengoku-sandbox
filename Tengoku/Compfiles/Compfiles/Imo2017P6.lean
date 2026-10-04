/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2017, Problem 6

A point (x,y) ∈ ℤ × ℤ is called primitive if gcd(x,y) = 1.
Let S be a finite set of primitive points.
Prove that there exists n > 0 and integers a₀,a₁,...,aₙ
such that

  a₀xⁿ + a₁xⁿ⁻¹y + a₂xⁿ⁻²y² + ... + aₙ₋₁xyⁿ⁻¹ + aₙyⁿ = 1

for each (x,y) ∈ S.
-/

namespace Imo2017P6

/-- A homogeneous polynomial in two variables with integer coefficients,
represented by its degree and coefficient function. Evaluation is
`∑ i ∈ range (deg + 1), coeff i * x^i * y^(deg - i)`. -/
structure HForm where
  deg : ℕ
  coeff : ℕ → ℤ

namespace HForm

/-- Evaluation of a homogeneous form at a point. -/
def eval (f : HForm) (x y : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (f.deg + 1), f.coeff i * x ^ i * y ^ (f.deg - i)

/-- The constant form. -/
def const (c : ℤ) : HForm := ⟨0, fun _ => c⟩

/-- The linear form `α * x + β * y`. -/
def linear (α β : ℤ) : HForm := ⟨1, fun i => if i = 0 then β else α⟩

/-- Coefficient function truncated above the degree. -/
def trunc (f : HForm) : ℕ → ℤ := fun i => if i ≤ f.deg then f.coeff i else 0

lemma trunc_of_le (f : HForm) {i : ℕ} (h : i ≤ f.deg) : f.trunc i = f.coeff i :=
  ite_eq_left h

lemma trunc_of_lt (f : HForm) {i : ℕ} (h : f.deg < i) : f.trunc i = 0 :=
  ite_eq_right (not_le.mpr h)

lemma eval_const (c : ℤ) (x y : ℤ) : (const c).eval x y = c := by
  simp [eval, const]

lemma eval_linear (α β : ℤ) (x y : ℤ) : (linear α β).eval x y = α * x + β * y := by
  simp [eval, linear, Finset.sum_range_succ]
  ring

lemma eval_eq_trunc (f : HForm) (x y : ℤ) :
    f.eval x y = ∑ i ∈ Finset.range (f.deg + 1), f.trunc i * x ^ i * y ^ (f.deg - i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [trunc_of_le f hi]

/-- Multiplication of homogeneous forms (degrees add). -/
def mul (f g : HForm) : HForm where
  deg := f.deg + g.deg
  coeff := fun k => ∑ i ∈ Finset.range (k + 1), f.trunc i * g.trunc (k - i)

/-- Powers of a homogeneous form. -/
def pow (f : HForm) : ℕ → HForm
  | 0 => const 1
  | n + 1 => mul (pow f n) f

lemma pow_deg (f : HForm) : ∀ n : ℕ, (f.pow n).deg = n * f.deg
  | 0 => (Nat.zero_mul _).symm
  | n + 1 => by
    show (mul (f.pow n) f).deg = (n + 1) * f.deg
    rw [show (mul (f.pow n) f).deg = (f.pow n).deg + f.deg from rfl, pow_deg f n]
    ring

/-- Addition of two forms of the same degree. -/
def add (f g : HForm) (_h : f.deg = g.deg) : HForm :=
  ⟨f.deg, fun i => f.coeff i + g.coeff i⟩

lemma eval_add (f g : HForm) (h : f.deg = g.deg) (x y : ℤ) :
    (f.add g h).eval x y = f.eval x y + g.eval x y := by
  have hg : g.eval x y =
      ∑ i ∈ Finset.range (f.deg + 1), g.coeff i * x ^ i * y ^ (f.deg - i) := by
    rw [h]; rfl
  rw [hg]
  show ∑ i ∈ Finset.range (f.deg + 1), (f.coeff i + g.coeff i) * x ^ i * y ^ (f.deg - i) =
    (∑ i ∈ Finset.range (f.deg + 1), f.coeff i * x ^ i * y ^ (f.deg - i)) +
    ∑ i ∈ Finset.range (f.deg + 1), g.coeff i * x ^ i * y ^ (f.deg - i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Negation of a form. -/
def neg (f : HForm) : HForm := ⟨f.deg, fun i => -f.coeff i⟩

lemma eval_neg (f : HForm) (x y : ℤ) : (f.neg).eval x y = -f.eval x y := by
  have h : ∀ i : ℕ, (-f.coeff i) * x ^ i * y ^ (f.deg - i) =
      -(f.coeff i * x ^ i * y ^ (f.deg - i)) := fun i => by ring
  simp only [eval, neg, h, Finset.sum_neg_distrib]

/-- Subtraction of two forms of the same degree. -/
def sub (f g : HForm) (h : f.deg = g.deg) : HForm := f.add g.neg (by simp [neg, h])

lemma sub_deg (f g : HForm) (h : f.deg = g.deg) : (f.sub g h).deg = f.deg := rfl

lemma eval_sub (f g : HForm) (h : f.deg = g.deg) (x y : ℤ) :
    (f.sub g h).eval x y = f.eval x y - g.eval x y := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

/-- Scalar multiplication of a form by an integer. -/
def cmul (c : ℤ) (f : HForm) : HForm := mul (const c) f

lemma cmul_deg (c : ℤ) (f : HForm) : (cmul c f).deg = f.deg := zero_add _

/-- Sum of a family of forms of the same degree. -/
def sum {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (_h : ∀ i ∈ s, (F i).deg = n) : HForm :=
  ⟨n, fun k => ∑ i ∈ s, (F i).coeff k⟩

lemma sum_deg {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (h : ∀ i ∈ s, (F i).deg = n) : (sum s F n h).deg = n := rfl

lemma eval_sum {ι : Type*} (s : Finset ι) (F : ι → HForm) (n : ℕ)
    (h : ∀ i ∈ s, (F i).deg = n) (x y : ℤ) :
    (sum s F n h).eval x y = ∑ i ∈ s, (F i).eval x y := by
  simp only [eval, sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i hi]

/-- Evaluation at the antipode of a form of even degree. -/
lemma eval_neg_of_even (f : HForm) (hfe : Even f.deg) (x y : ℤ) :
    f.eval (-x) (-y) = f.eval x y := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have h1 : (-1 : ℤ) ^ (i + (f.deg - i)) = 1 := by
    rw [Nat.add_sub_cancel' hi]
    exact hfe.neg_one_pow
  calc f.coeff i * (-x) ^ i * (-y) ^ (f.deg - i)
      = f.coeff i * x ^ i * y ^ (f.deg - i) * ((-1) ^ i * (-1) ^ (f.deg - i)) := by
        rw [neg_pow, neg_pow]; ring
    _ = f.coeff i * x ^ i * y ^ (f.deg - i) := by rw [← pow_add, h1]; ring

end HForm

/-- Canonical orientation of a nonzero lattice point: exactly one of `s`, `-s`
satisfies `canon s`. -/
def canon (s : ℤ × ℤ) : Prop := 0 < s.1 ∨ (s.1 = 0 ∧ 0 < s.2)

instance (s : ℤ × ℤ) : Decidable (canon s) := by
  unfold canon
  infer_instance

lemma canon_iff_not_neg {s : ℤ × ℤ} (hs : s ≠ (0, 0)) : canon s ↔ ¬ canon (-s) := by
  have hf : (-s).1 = -s.1 := rfl
  have hd : (-s).2 = -s.2 := rfl
  have hs12 : ¬(s.1 = 0 ∧ s.2 = 0) := fun h => hs (Prod.ext h.1 h.2)
  unfold canon
  rw [hf, hd]
  constructor
  · rintro (h | ⟨e, h⟩) (h' | ⟨e', h'⟩) <;> lia
  · intro h
    by_cases e1 : s.1 = 0
    · by_cases e2 : 0 < s.2
      · exact Or.inr ⟨e1, e2⟩
      · exfalso
        have e2' : s.2 < 0 := by
          have hz : s.2 ≠ 0 := fun hz => hs12 ⟨e1, hz⟩
          lia
        apply h
        exact Or.inr ⟨by lia, by lia⟩
    · by_cases h1 : 0 < s.1
      · exact Or.inl h1
      · exfalso
        apply h
        exact Or.inl (by lia)

/-- Representative of the antipodal class of `s`, chosen inside `S`
whenever possible. -/
def rep (S : Finset (ℤ × ℤ)) (s : ℤ × ℤ) : ℤ × ℤ :=
  if canon s ∧ s ∈ S then s else if canon (-s) ∧ (-s) ∈ S then -s else s

lemma rep_mem {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) : rep S s ∈ S := by
  unfold rep
  by_cases h1 : canon s ∧ s ∈ S
  · rw [ite_eq_left h1]; exact hs
  · rw [ite_eq_right h1]
    by_cases h2 : canon (-s) ∧ (-s) ∈ S
    · rw [ite_eq_left h2]; exact h2.2
    · rw [ite_eq_right h2]; exact hs

lemma rep_eq_self_or_neg {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} :
    rep S s = s ∨ rep S s = -s := by
  unfold rep
  by_cases h1 : canon s ∧ s ∈ S
  · rw [ite_eq_left h1]; exact Or.inl rfl
  · rw [ite_eq_right h1]
    by_cases h2 : canon (-s) ∧ (-s) ∈ S
    · rw [ite_eq_left h2]; exact Or.inr rfl
    · rw [ite_eq_right h2]; exact Or.inl rfl

lemma rep_neg {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) (hns : -s ∈ S)
    (hs0 : s ≠ (0, 0)) : rep S (-s) = rep S s := by
  have hcan := canon_iff_not_neg hs0
  by_cases hA : canon s
  · have hB : ¬ canon (-s) := hcan.mp hA
    have hrep_s : rep S s = s := by unfold rep; rw [ite_eq_left ⟨hA, hs⟩]
    have hrep_ns : rep S (-s) = s := by
      unfold rep
      rw [ite_eq_right (fun h => hB h.1)]
      rw [ite_eq_left (by rw [neg_neg]; exact ⟨hA, hs⟩ : canon (-(-s)) ∧ (-(-s)) ∈ S)]
      exact neg_neg s
    rw [hrep_s, hrep_ns]
  · have hB : canon (-s) := by
      by_contra hB
      exact hA (hcan.mpr hB)
    have hrep_s : rep S s = -s := by
      unfold rep
      rw [ite_eq_right (fun h => hA h.1), ite_eq_left ⟨hB, hns⟩]
    have hrep_ns : rep S (-s) = -s := by
      unfold rep
      rw [ite_eq_left ⟨hB, hns⟩]
    rw [hrep_s, hrep_ns]

lemma rep_idem {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) (hs0 : s ≠ (0, 0)) :
    rep S (rep S s) = rep S s := by
  rcases rep_eq_self_or_neg (S := S) (s := s) with h | h
  · conv_lhs => rw [h]
  · have hns : -s ∈ S := by
      have hm := rep_mem hs
      rw [h] at hm
      exact hm
    calc rep S (rep S s) = rep S (-s) := by rw [h]
      _ = rep S s := rep_neg hs hns hs0

/-- The set of antipodal class representatives of `S`. -/
def T (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := S.image (rep S)

lemma T_subset {S : Finset (ℤ × ℤ)} : T S ⊆ S := by
  intro t ht
  rw [T, Finset.mem_image] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact rep_mem hs

lemma rep_mem_T {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (hs : s ∈ S) : rep S s ∈ T S :=
  Finset.mem_image_of_mem _ hs

lemma rep_spec {S : Finset (ℤ × ℤ)} {s : ℤ × ℤ} (_hs : s ∈ S) :
    s = rep S s ∨ s = -rep S s := by
  rcases rep_eq_self_or_neg (S := S) (s := s) with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

lemma ne_zero_of_isCoprime {s : ℤ × ℤ} (h : IsCoprime s.1 s.2) : s ≠ (0, 0) := by
  intro hz
  subst hz
  change IsCoprime (0 : ℤ) (0 : ℤ) at h
  rw [Int.isCoprime_iff_gcd_eq_one] at h
  simp at h

lemma T_ne_neg {S : Finset (ℤ × ℤ)} (hS : ∀ s ∈ S, IsCoprime s.1 s.2) {t₁ t₂ : ℤ × ℤ}
    (ht₁ : t₁ ∈ T S) (ht₂ : t₂ ∈ T S) (hne : t₁ ≠ t₂) : t₁ ≠ -t₂ := by
  intro h
  rw [T, Finset.mem_image] at ht₁ ht₂
  obtain ⟨s₁, hs₁, rfl⟩ := ht₁
  obtain ⟨s₂, hs₂, rfl⟩ := ht₂
  have hz₁ : s₁ ≠ (0, 0) := ne_zero_of_isCoprime (hS s₁ hs₁)
  have hz₂ : s₂ ≠ (0, 0) := ne_zero_of_isCoprime (hS s₂ hs₂)
  have hrz₂ : rep S s₂ ≠ (0, 0) := ne_zero_of_isCoprime (hS _ (rep_mem hs₂))
  have key : rep S s₁ = rep S s₂ := by
    calc rep S s₁ = rep S (rep S s₁) := (rep_idem hs₁ hz₁).symm
      _ = rep S (-rep S s₂) := by rw [h]
      _ = rep S (rep S s₂) :=
        rep_neg (rep_mem hs₂) (by rw [← h]; exact rep_mem hs₁) hrz₂
      _ = rep S s₂ := rep_idem hs₂ hz₂
  exact hne key

/-- If two primitive points have cross-product zero, they are equal or
antipodal. -/
lemma eq_or_neg_of_mul_eq {x₁ y₁ x₂ y₂ : ℤ} (h₁ : IsCoprime x₁ y₁) (h₂ : IsCoprime x₂ y₂)
    (h : x₁ * y₂ = x₂ * y₁) : (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = -x₂ ∧ y₁ = -y₂) := by
  have hdvd1 : x₁ ∣ x₂ :=
    h₁.dvd_of_dvd_mul_left ⟨y₂, by rw [mul_comm y₁ x₂]; exact h.symm⟩
  have hdvd2 : x₂ ∣ x₁ :=
    h₂.dvd_of_dvd_mul_left ⟨y₁, by rw [mul_comm y₂ x₁]; exact h⟩
  have hdvd3 : y₁ ∣ y₂ :=
    h₁.symm.dvd_of_dvd_mul_left ⟨x₂, by rw [mul_comm y₁ x₂]; exact h⟩
  have hdvd4 : y₂ ∣ y₁ :=
    h₂.symm.dvd_of_dvd_mul_left ⟨x₁, by rw [mul_comm y₂ x₁]; exact h.symm⟩
  have hx : x₁ = x₂ ∨ x₁ = -x₂ := by
    have h12 : x₁.natAbs ∣ x₂.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd1
    have h21 : x₂.natAbs ∣ x₁.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd2
    exact Int.natAbs_eq_natAbs_iff.mp (Nat.dvd_antisymm h12 h21)
  have hy : y₁ = y₂ ∨ y₁ = -y₂ := by
    have h12 : y₁.natAbs ∣ y₂.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd3
    have h21 : y₂.natAbs ∣ y₁.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd4
    exact Int.natAbs_eq_natAbs_iff.mp (Nat.dvd_antisymm h12 h21)
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · have h2 : x₂ * y₂ = 0 := by
      rw [hx, hy] at h
      have hh : (2 : ℤ) * (x₂ * y₂) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hh with h2' | h2'
      · norm_num at h2'
      · exact h2'
    rcases mul_eq_zero.mp h2 with hx0 | hy0
    · exact Or.inr ⟨by rw [hx, hx0, neg_zero], hy⟩
    · have hy10 : y₁ = 0 := by rw [hy, hy0, neg_zero]
      exact Or.inl ⟨hx, by rw [hy10, hy0]⟩
  · have h2 : x₂ * y₂ = 0 := by
      rw [hx, hy] at h
      have hh : (2 : ℤ) * (x₂ * y₂) = 0 := by linear_combination -h
      rcases mul_eq_zero.mp hh with h2' | h2'
      · norm_num at h2'
      · exact h2'
    rcases mul_eq_zero.mp h2 with hx0 | hy0
    · have hx10 : x₁ = 0 := by rw [hx, hx0, neg_zero]
      exact Or.inl ⟨by rw [hx10, hx0], hy⟩
    · have hy10 : y₁ = 0 := by rw [hy, hy0]
      exact Or.inr ⟨hx, by rw [hy10, hy0, neg_zero]⟩
  · exact Or.inr ⟨hx, hy⟩

/-- Points of distinct classes in `T` have nonzero determinant. -/
lemma det_ne_zero {S : Finset (ℤ × ℤ)} (hS : ∀ s ∈ S, IsCoprime s.1 s.2) {t t' : ℤ × ℤ}
    (ht : t ∈ T S) (ht' : t' ∈ T S) (hne : t' ≠ t) :
    t'.2 * t.1 - t'.1 * t.2 ≠ 0 := by
  intro h
  have hmem_t : t ∈ S := T_subset ht
  have hmem_t' : t' ∈ S := T_subset ht'
  have h1 : t'.2 * t.1 = t'.1 * t.2 := sub_eq_zero.mp h
  have h0 : t.1 * t'.2 = t'.1 * t.2 := by
    calc t.1 * t'.2 = t'.2 * t.1 := mul_comm _ _
      _ = t'.1 * t.2 := h1
  rcases eq_or_neg_of_mul_eq (hS t hmem_t) (hS t' hmem_t') h0 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hne (Prod.ext e1.symm e2.symm)
  · have h' : t' = -t := by
      have e : t = -t' := Prod.ext e1 e2
      rw [e, neg_neg]
    exact T_ne_neg hS ht' ht hne h'

/-- The coordinate form `x`. -/
def Xf : HForm := HForm.linear 1 0

/-- The coordinate form `y`. -/
def Yf : HForm := HForm.linear 0 1

lemma Xf_eval (x y : ℤ) : Xf.eval x y = x := by
  rw [Xf, HForm.eval_linear]
  ring

lemma Yf_eval (x y : ℤ) : Yf.eval x y = y := by
  rw [Yf, HForm.eval_linear]
  ring

lemma Xf_deg : Xf.deg = 1 := rfl

lemma Yf_deg : Yf.deg = 1 := rfl

lemma zmod_natCast_eq_zero_iff_dvd (a n : ℕ) : ((a : ZMod n)) = 0 ↔ n ∣ a := by
  rw [show ((a : ZMod n)) = ((a : ℤ) : ZMod n) by norm_cast,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]

lemma not_coprime_of_both_dvd {x y : ℤ} (h : IsCoprime x y) {c : ℤ}
    (hx : c ∣ x) (hy : c ∣ y) : c ∣ 1 := by
  obtain ⟨u, v, huv⟩ := h
  rw [← huv]
  exact dvd_add (hx.mul_left u) (hy.mul_left v)

/-- In `ZMod 2`, the form `x² + xy + y²` does not vanish at a primitive point. -/
lemma two_not_dvd_quad_zmod {x y : ℤ} (h : IsCoprime x y) :
    ((x ^ 2 + x * y + y ^ 2 : ℤ) : ZMod 2) ≠ 0 := by
  intro hcast
  push_cast at hcast
  have h2d : ∀ a b : ZMod 2, ¬(a = 0 ∧ b = 0) → a ^ 2 + a * b + b ^ 2 ≠ 0 := by decide
  have hab : ¬((x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0) := by
    rintro ⟨hx0, hy0⟩
    have h2x : (2 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    have h2y : (2 : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0
    have h21 := not_coprime_of_both_dvd h h2x h2y
    norm_num at h21
  exact h2d _ _ hab hcast

/-- In `ZMod p` for an odd prime `p`, the form `x^(p-1) + y^(p-1)` does not
vanish at a primitive point. -/
lemma odd_not_dvd_powsum_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y : ℤ}
    (h : IsCoprime x y) : ((x ^ (p - 1) + y ^ (p - 1) : ℤ) : ZMod p) ≠ 0 := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    lia
  have : Fact p.Prime := ⟨hp⟩
  intro hcast
  push_cast at hcast
  have hab : (x : ZMod p) = 0 → ¬(y : ZMod p) = 0 := by
    intro hx0 hy0
    have hpx : (p : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    have hpy : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0
    have hp1 := not_coprime_of_both_dvd h hpx hpy
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_cast, Int.natCast_dvd_natCast] at hp1
    have := Nat.le_of_dvd one_pos hp1
    lia
  by_cases hx0 : (x : ZMod p) = 0
  · have hy0 : (y : ZMod p) ≠ 0 := hab hx0
    rw [hx0, zero_pow (by lia : p - 1 ≠ 0), zero_add] at hcast
    rw [ZMod.pow_card_sub_one_eq_one hy0] at hcast
    exact one_ne_zero hcast
  · by_cases hy0 : (y : ZMod p) = 0
    · rw [hy0, zero_pow (by lia : p - 1 ≠ 0), add_zero] at hcast
      rw [ZMod.pow_card_sub_one_eq_one hx0] at hcast
      exact one_ne_zero hcast
    · rw [ZMod.pow_card_sub_one_eq_one hx0, ZMod.pow_card_sub_one_eq_one hy0] at hcast
      have h2ne : (2 : ZMod p) ≠ 0 := by
        have h2i : ¬ (p ∣ 2) := by
          intro hd2
          have := Nat.le_of_dvd (by norm_num) hd2
          lia
        intro h20
        apply h2i
        have h' : (((2 : ℕ) : ℤ) : ZMod p) = 0 := by
          rw [show (((2 : ℕ) : ℤ) : ZMod p) = (2 : ZMod p) by norm_cast]
          exact h20
        exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h')
      have h11 : (1 : ZMod p) + 1 = 2 := by norm_cast
      rw [h11] at hcast
      exact h2ne hcast

/-- The local form used modulo the prime `p`: `x² + xy + y²` for `p = 2` and
`x^(p-1) + y^(p-1)` for odd `p`. -/
def Gform (p : ℕ) : HForm :=
  if p = 2 then ((Xf.pow 2).add (Xf.mul Yf) (by rw [HForm.pow_deg]; rfl)).add (Yf.pow 2)
    (by show ((Xf.pow 2).add (Xf.mul Yf) _).deg = (Yf.pow 2).deg
        show (Xf.pow 2).deg = (Yf.pow 2).deg
        rw [HForm.pow_deg, HForm.pow_deg, Xf_deg, Yf_deg])
  else (Xf.pow (p - 1)).add (Yf.pow (p - 1))
    (by show (Xf.pow (p - 1)).deg = (Yf.pow (p - 1)).deg
        rw [HForm.pow_deg, HForm.pow_deg, Xf_deg, Yf_deg])

lemma Gform_deg (p : ℕ) : (Gform p).deg = if p = 2 then 2 else p - 1 := by
  rw [Gform]
  split_ifs with hp2
  · show (Xf.pow 2).deg = 2
    rw [HForm.pow_deg, Xf_deg]
  · show (Xf.pow (p - 1)).deg = p - 1
    rw [HForm.pow_deg, Xf_deg, mul_one]

end Imo2017P6
