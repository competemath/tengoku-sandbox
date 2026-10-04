/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku

/-!
# Surjectivity of the reduction map SL₂(ℤ) → SL₂(ℤ/dℤ)

This file proves that the natural reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective
(strong approximation for SL₂). This is a fundamental result in the theory of
congruence subgroups and Hecke operators.

## Main results

* `SL2_reduction_surjective` — the map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective.

## Proof strategy

Given `g = !![a, b; c, d] ∈ SL₂(ℤ/dℤ)` with `a * d - b * c = 1`:

1. **Coprime lifting**: Lift `a, c` to integers `a₁, c₀` with `a₁ ≡ a (mod d)`,
   `c₀ ≡ c (mod d)`, and `gcd(a₁, c₀) = 1`. This uses the stable range property of `ℤ`:
   since `gcd(a₀, c₀, d) = 1` for arbitrary lifts, we can adjust `a₀` by multiples of `d`
   to eliminate common factors with `c₀`.

2. **Bezout completion**: By `IsCoprime.exists_SL2_col`, find `σ ∈ SL₂(ℤ)` whose
   first column is `(a₁, c₀)`.

3. **Upper triangular remainder**: The matrix `map(σ)⁻¹ * g` has first column `(1, 0)`
   by direct computation, so it equals `!![1, t; 0, 1]` for some `t ∈ ℤ/dℤ`.

4. **Lift upper triangular**: `!![1, t; 0, 1]` is the image of `!![1, t'; 0, 1] ∈ SL₂(ℤ)`
   for any integer lift `t'` of `t`.

5. **Combine**: `g = map(σ) * !![1, t; 0, 1] = map(σ * !![1, t'; 0, 1])`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §1.6
* Serre, *A Course in Arithmetic*, Ch. VII, Lemma 15
-/

open Matrix SpecialLinearGroup

namespace SL2Reduction

private lemma natAbs_emod_lt (a c : ℤ) (hc : c ≠ 0) : (a % c).natAbs < c.natAbs := by
  rw [Int.natAbs_emod a hc]
  split
  · exact Nat.mod_lt _ (Int.natAbs_pos.mpr hc)
  · rename_i h
    push Not at h
    have : a.natAbs % c.natAbs ≠ 0 :=
      fun heq ↦ h.2 (Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mod_eq_zero heq))
    omega

private lemma isCoprime_emod {d : ℕ} [NeZero d] {a₁ c₁ : ℤ}
    (hac : IsCoprime (a₁ : ZMod d) (c₁ : ZMod d)) :
    IsCoprime (c₁ : ZMod d) ((a₁ % c₁ : ℤ) : ZMod d) := by
  rw [show (a₁ % c₁ : ℤ) = a₁ + c₁ * (-(a₁ / c₁)) from by rw [Int.emod_def]; ring]
  push_cast
  exact hac.symm.add_mul_left_right _

/-- **Coprime lifting (stable range of ℤ)**: the proof uses Euclidean descent.
Given `IsCoprime a₁ c₁` in `ZMod d`, apply the extended Euclidean algorithm to
`(a₁, c₁)` in `ℤ`, swapping at each step. The coprimality in `ZMod d` is preserved
under the Euclidean step `(a₁, c₁) ↦ (c₁, a₁ % c₁)`, and the back-substitution
`a₀ = r₀ + q * c₀` recovers the correct congruence class modulo `d`. -/
theorem IsCoprime.lift_to_int {d : ℕ} [NeZero d] {a c : ZMod d} (hac : IsCoprime a c) :
    ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a ∧ (c₀ : ZMod d) = c ∧ IsCoprime a₀ c₀ := by
  obtain ⟨a₁, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨c₁, rfl⟩ := ZMod.intCast_surjective c
  suffices h : ∀ n, ∀ a₁ c₁ : ℤ, c₁.natAbs ≤ n →
      IsCoprime (a₁ : ZMod d) (c₁ : ZMod d) →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = c₁ ∧ IsCoprime a₀ c₀ from
    h c₁.natAbs a₁ c₁ le_rfl hac
  -- Helper for the base case (c₁ = 0).
  have zero_case : ∀ a₁ : ℤ, IsCoprime (a₁ : ZMod d) 0 →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = 0 ∧ IsCoprime a₀ c₀ := fun a₁ hac ↦ by
    have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
    exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
  intro n
  induction n with
  | zero =>
    intro a₁ c₁ hle hac
    have hc₁ : c₁ = 0 := by omega
    subst hc₁
    simpa using zero_case a₁ (by simpa using hac)
  | succ n ih =>
    intro a₁ c₁ hle hac
    by_cases hc₁ : c₁ = 0
    · subst hc₁; simpa using zero_case a₁ (by simpa using hac)
    obtain ⟨c₀, r₀, hc₀, hr₀, hcop⟩ := ih c₁ (a₁ % c₁)
      (Nat.lt_succ_iff.mp ((natAbs_emod_lt a₁ c₁ hc₁).trans_le hle)) (isCoprime_emod hac)
    refine ⟨r₀ + a₁ / c₁ * c₀, c₀, ?_, hc₀, hcop.symm.add_mul_right_left _⟩
    change ((r₀ + a₁ / c₁ * c₀ : ℤ) : ZMod d) = (a₁ : ZMod d)
    conv_rhs => rw [show a₁ = a₁ % c₁ + a₁ / c₁ * c₁ from by
      have := Int.mul_ediv_add_emod a₁ c₁; linarith]
    push_cast
    rw [hr₀, hc₀]

/-- The first column of an SL₂ matrix is coprime (from the determinant condition). -/
theorem isCoprime_of_det_eq_one {R : Type*} [CommRing R]
    {a b c d : R} (h : a * d - b * c = 1) : IsCoprime a c :=
  ⟨d, -b, by linear_combination h⟩

/-- An SL₂ element with first column `(1, 0)` is upper unitriangular. -/
theorem SL2_eq_upperUniTri {R : Type*} [CommRing R] (h : SpecialLinearGroup (Fin 2) R)
    (h00 : h 0 0 = 1) (h10 : h 1 0 = 0) :
    h = ⟨!![1, h 0 1; 0, 1], by
      rw [det_fin_two]; simp [cons_val_zero, cons_val_one]⟩ := by
  ext i j
  induction h using fin_two_induction with
  | _ a b c dd hdet =>
    simp at h00 h10
    subst h00; subst h10
    fin_cases i <;> fin_cases j <;> simp [cons_val_zero, cons_val_one]
    linear_combination hdet

end SL2Reduction
