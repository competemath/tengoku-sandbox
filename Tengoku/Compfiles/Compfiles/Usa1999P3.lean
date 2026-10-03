/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1999, Problem 3

Let p > 2 be a prime and let a, b, c, d be integers not divisible by p, such that

    {ra/p} + {rb/p} + {rc/p} + {rd/p} = 2

for any integer r not divisible by p. (Here, {t} = t − ⌊t⌋ is the fractional part.)
Prove that at least two of the numbers a + b, a + c, a + d, b + c, b + d, c + d
are divisible by p.
-/

namespace Usa1999P3

open Finset

/-!
## Proof sketch

We follow the classical root-of-unity filter solution (Michael J. Doré's write-up
on Kalva).

Let `ζ = exp (2πi / p)` and let `χ : ZMod p → ℂ` be the additive character
`χ j = ζ ^ j.val`. The hypothesis says that for every nonzero `n : ZMod p` the
residues `(n * a).val + (n * b).val + (n * c).val + (n * d).val` sum to `2p`.
Weighting by `χ (-(m * n))` and summing over all `n` gives, for every nonzero
`m`, the identity `∑_{x ∈ {a,b,c,d}} Sw (-(m * x⁻¹)) = -2p`, where
`Sw j = ∑ k, k.val * χ (j * k)` satisfies `(χ j - 1) * Sw j = p`. Hence
`∑ 1 / (χ (-(m * x⁻¹)) - 1) = -2`. Clearing denominators yields the symmetric
relation `2 + e₃ = e₁ + 2 e₄` in the four numbers `χ (-(m * xᵢ⁻¹))`; summing it
over `m : ZMod p` forces `a⁻¹ + b⁻¹ + c⁻¹ + d⁻¹ = 0` in `ZMod p`. The relation
then reads `∑ χ (m * xᵢ⁻¹) = ∑ χ (-(m * xᵢ⁻¹))`; multiplying by `χ (-(m * a⁻¹))`
and summing over `m` shows that one of `a⁻¹ + b⁻¹`, `a⁻¹ + c⁻¹`, `a⁻¹ + d⁻¹`
vanishes, and the complementary pair vanishes too because the total sum is zero.
Taking inverses once more yields the two required divisibilities.
-/

noncomputable section

/-- The primitive `p`-th root of unity used throughout the proof. -/
def rt (p : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

/-- The additive character `ZMod p → ℂ` given by `j ↦ ζ ^ j.val`. -/
def chi (p : ℕ) (j : ZMod p) : ℂ := rt p ^ j.val

/-- The weighted character sum `∑ k, k.val * χ (j * k)`. -/
def Sw (p : ℕ) [NeZero p] (j : ZMod p) : ℂ := ∑ k : ZMod p, (k.val : ℂ) * chi p (j * k)

lemma isPrimitiveRoot_rt {p : ℕ} (hp : p.Prime) : IsPrimitiveRoot (rt p) p := by
  unfold rt
  exact Complex.isPrimitiveRoot_exp p hp.pos.ne'

lemma chi_zero (p : ℕ) : chi p (0 : ZMod p) = 1 := by
  simp [chi, ZMod.val_zero]

lemma chi_add {p : ℕ} (hp : p.Prime) (j k : ZMod p) :
    chi p (j + k) = chi p j * chi p k := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hpow : rt p ^ p = 1 := (isPrimitiveRoot_rt hp).pow_eq_one
  have hlt : j.val + k.val < 2 * p := by
    have h1 := j.val_lt
    have h2 := k.val_lt
    lia
  show rt p ^ (j + k).val = rt p ^ j.val * rt p ^ k.val
  rw [ZMod.val_add]
  rcases lt_or_ge (j.val + k.val) p with h | h
  · rw [Nat.mod_eq_of_lt h, pow_add]
  · have hmod : (j.val + k.val) % p = j.val + k.val - p := by
      have h1 : j.val + k.val = j.val + k.val - p + p := by lia
      conv_lhs => rw [h1]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by lia : j.val + k.val - p < p)]
    rw [hmod]
    have h2 : rt p ^ (j.val + k.val - p) * rt p ^ p = rt p ^ j.val * rt p ^ k.val := by
      rw [← pow_add, Nat.sub_add_cancel h, pow_add]
    rw [hpow, mul_one] at h2
    exact h2

lemma chi_eq_one_iff {p : ℕ} (hp : p.Prime) (j : ZMod p) : chi p j = 1 ↔ j = 0 := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hζ := isPrimitiveRoot_rt hp
  constructor
  · intro h
    have hdvd : p ∣ j.val := (hζ.pow_eq_one_iff_dvd j.val).mp h
    have hz : j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd j.val_lt
    have hj0 : (j.val : ZMod p) = 0 := by rw [hz, Nat.cast_zero]
    rwa [ZMod.natCast_zmod_val] at hj0
  · rintro rfl
    exact chi_zero p

/-- Sums over `ZMod p` of a function of the residue can be written as sums over
`Finset.range p`. -/
lemma sum_zmod_val {p : ℕ} [NeZero p] (f : ℕ → ℂ) :
    ∑ j : ZMod p, f (j.val) = ∑ i ∈ Finset.range p, f i := by
  apply Finset.sum_bij (i := fun j _ => j.val)
  · intro j _
    exact Finset.mem_range.mpr j.val_lt
  · intro j _ j' _ hjj'
    have h1 : (j.val : ZMod p) = j := ZMod.natCast_zmod_val j
    have h2 : (j'.val : ZMod p) = j' := ZMod.natCast_zmod_val j'
    rw [← h1, ← h2, hjj']
  · intro k hk
    have hk2 : k < p := Finset.mem_range.mp hk
    exact ⟨(k : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt hk2⟩
  · intro j _
    rfl

lemma sum_chi_self {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) :
    ∑ j : ZMod p, chi p j = 0 := by
  have hζ := isPrimitiveRoot_rt hp
  show ∑ j : ZMod p, (fun k : ℕ => rt p ^ k) j.val = 0
  rw [sum_zmod_val]
  exact hζ.geom_sum_eq_zero (by lia)

lemma sum_chi {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) (c : ZMod p) :
    ∑ m : ZMod p, chi p (c * m) = if c = 0 then (p : ℂ) else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    have h1 : (∑ m : ZMod p, chi p ((0 : ZMod p) * m)) = ∑ _m : ZMod p, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [zero_mul]
      exact chi_zero p
    rw [h1, Finset.sum_const, Finset.card_univ, ZMod.card p, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right hc]
    have h2 : (∑ m : ZMod p, chi p (c * m)) = ∑ m : ZMod p, chi p m := by
      have e := Equiv.sum_comp (Units.mulLeft (Units.mk0 c hc)) (chi p)
      rw [← e]
      apply Finset.sum_congr rfl
      intro m _
      rfl
    rw [h2]
    exact sum_chi_self hp hp2

/-- The key identity `(χ j - 1) * Sw j = p` for nonzero `j`, obtained by
reindexing the sum defining `Sw` along `k ↦ k + 1`. -/
lemma Sw_mul_sub_one {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : 2 < p) {j : ZMod p} (hj : j ≠ 0) :
    (chi p j - 1) * Sw p j = (p : ℂ) := by
  have h1 : chi p j * Sw p j = ∑ k : ZMod p, ((k - 1).val : ℂ) * chi p (j * k) := by
    unfold Sw
    rw [Finset.mul_sum]
    have hstep : (∑ k : ZMod p, chi p j * ((k.val : ℂ) * chi p (j * k)))
        = ∑ k : ZMod p, (k.val : ℂ) * chi p (j * (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      calc chi p j * ((k.val : ℂ) * chi p (j * k))
          = (k.val : ℂ) * (chi p j * chi p (j * k)) := by ring
        _ = (k.val : ℂ) * chi p (j * (k + 1)) := by
          rw [← chi_add hp]
          congr 2
          ring
    rw [hstep]
    have e := Equiv.sum_comp (Equiv.addRight (1 : ZMod p))
      (fun k : ZMod p => ((k - 1).val : ℂ) * chi p (j * k))
    rw [← e]
    apply Finset.sum_congr rfl
    intro k _
    have hk1 : (Equiv.addRight (1 : ZMod p)) k = k + 1 := rfl
    rw [hk1, add_sub_cancel_right]
  have h4 : (chi p j - 1) * Sw p j
      = ∑ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k) := by
    rw [sub_mul, h1, one_mul]
    unfold Sw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h4]
  have hw : ∀ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k)
      = (-1 : ℂ) * chi p (j * k) + (if k = 0 then (p : ℂ) else 0) * chi p (j * k) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl]
      have hval : ((0 : ZMod p) - 1).val = p - 1 := by
        have h1 : (0 : ZMod p) - 1 = -1 := zero_sub 1
        rw [h1]
        have h2 := ZMod.val_neg_one (p - 1)
        rw [show (p - 1).succ = p from
          (Nat.succ_eq_add_one (p - 1)).trans (Nat.sub_add_cancel (by lia : 1 ≤ p))] at h2
        exact h2
      have hcast : (((p - 1 : ℕ) : ℂ)) = (p : ℂ) - 1 := by
        rw [Nat.cast_sub (by lia : 1 ≤ p), Nat.cast_one]
      rw [hval, ZMod.val_zero, Nat.cast_zero, hcast]
      ring
    · rw [ite_eq_right hk]
      have hkval : k.val ≠ 0 := by
        exact (ZMod.val_ne_zero k).mpr hk
      have hval : (k - 1).val = k.val - 1 := by
        have h4 : ((k.val - 1 + 1 : ℕ) : ZMod p) = (k.val : ZMod p) := by
          rw [Nat.sub_add_cancel (by lia : 1 ≤ k.val)]
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] at h4
        have h2 : ((k.val - 1 : ℕ) : ZMod p) = k - 1 := by
          rw [eq_sub_iff_add_eq]
          exact h4
        rw [← h2, ZMod.val_natCast_of_lt (by have := k.val_lt; lia : k.val - 1 < p)]
      rw [hval, Nat.cast_sub (by lia : 1 ≤ k.val), Nat.cast_one]
      ring
  have h6 : (∑ k : ZMod p, (((k - 1).val : ℂ) - (k.val : ℂ)) * chi p (j * k))
      = (∑ k : ZMod p, (-1 : ℂ) * chi p (j * k))
        + ∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hw k]
  rw [h6]
  have h7 : (∑ k : ZMod p, (-1 : ℂ) * chi p (j * k)) = 0 := by
    rw [← Finset.mul_sum]
    have h8 : (∑ k : ZMod p, chi p (j * k)) = 0 := by
      rw [sum_chi hp hp2 j, ite_eq_right hj]
    rw [h8, mul_zero]
  rw [h7, zero_add]
  have h9 : (∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k))
      = (p : ℂ) := by
    have h10 : (∑ k : ZMod p, (if k = 0 then (p : ℂ) else 0) * chi p (j * k))
        = ∑ k : ZMod p, (if k = 0 then (p : ℂ) * chi p (j * k) else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = 0
      · rw [ite_eq_left hk, ite_eq_left hk]
      · rw [ite_eq_right hk, ite_eq_right hk, zero_mul]
    rw [h10, Finset.sum_ite_eq']
    simp [chi_zero]
  exact h9

/-- The symmetric-polynomial identity obtained by clearing denominators in
`∑ 1 / (xᵢ - 1) = -2`. -/
lemma alg_symm {x₁ x₂ x₃ x₄ : ℂ} (h₁ : x₁ ≠ 1) (h₂ : x₂ ≠ 1) (h₃ : x₃ ≠ 1) (h₄ : x₄ ≠ 1)
    (h : 1 / (x₁ - 1) + 1 / (x₂ - 1) + 1 / (x₃ - 1) + 1 / (x₄ - 1) = -2) :
    2 + (x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄)
      = x₁ + x₂ + x₃ + x₄ + 2 * (x₁ * x₂ * x₃ * x₄) := by
  have d₁ : x₁ - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have d₂ : x₂ - 1 ≠ 0 := sub_ne_zero.mpr h₂
  have d₃ : x₃ - 1 ≠ 0 := sub_ne_zero.mpr h₃
  have d₄ : x₄ - 1 ≠ 0 := sub_ne_zero.mpr h₄
  field_simp at h
  linear_combination -h

end

end Usa1999P3
