/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku

/-!
# Index of Congruence Subgroups

Computes the index `[SL₂(ℤ) : Γ₀(pᵏ)] = pᵏ⁻¹(p + 1)` for prime `p` and `k ≥ 1`.

## Main results

* `Gamma0_prime_index` : `(Gamma0 p).index = p + 1` for prime `p`
* `Gamma0_relindex_step` : `(Gamma0 (p^(k+1))).relIndex (Gamma0 (p^k)) = p`
* `Gamma0_prime_power_index` : `(Gamma0 (p^k)).index = p^(k-1) * (p + 1)` for `k ≥ 1`

## References

* Shimura, Theorem 3.24
-/

open Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

private lemma dvd_sub_val_mul (p : ℕ) (hp : Nat.Prime p) (a b : ℤ) (hb : (b : ZMod p) ≠ 0) :
    (p : ℤ) ∣ a - (((a : ZMod p) * (b : ZMod p)⁻¹).val : ℤ) * b := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hb, mul_one, sub_self]

private lemma SL2_entry_mul (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B).1 i j = A.1 i 0 * B.1 0 j + A.1 i 1 * B.1 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma TjS_inv_10 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 0 = -1 := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_inv_11 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 1 = j := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_00 (j : ℤ) : (T ^ j * S).1 0 0 = j := by
  simp [coe_T_zpow, coe_S]

private lemma TjS_10 (j : ℤ) : (T ^ j * S).1 1 0 = 1 := by
  simp [coe_S]

private lemma TjS_inv_mul_10 (j : ℤ) (σ : SL(2, ℤ)) :
    ((T ^ j * S)⁻¹ * σ).1 1 0 = j * σ.1 1 0 - σ.1 0 0 := by
  rw [SL2_entry_mul, TjS_inv_10, TjS_inv_11]
  ring

private lemma rep_diff_10 (i j : ℤ) :
    ((T ^ j * S)⁻¹ * (T ^ i * S)).1 1 0 = j - i := by
  rw [TjS_inv_mul_10, TjS_10, TjS_00]
  ring

section BaseCase

variable (p : ℕ) (hp : Nat.Prime p)
include hp

private def Gamma0Rep (j : Fin (p + 1)) : SL(2, ℤ) :=
  if j.val < p then T ^ (j.val : ℤ) * S else 1

private lemma Gamma0_prime_index_inj :
    Function.Injective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ hf
  rw [QuotientGroup.eq, Gamma0_mem] at hf
  simp only [Gamma0Rep] at hf
  split_ifs at hf with h1 h2
  · rw [rep_diff_10, ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by lia)
    exact Fin.mk_eq_mk.mpr (by lia)
  · rw [mul_one, TjS_inv_10] at hf
    exact absurd hf (by norm_num)
  · rw [inv_one, one_mul, TjS_10] at hf
    exact absurd hf (by norm_num)
  · exact Fin.mk_eq_mk.mpr (by lia)

private lemma Gamma0_prime_index_surj :
    Function.Surjective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  by_cases h : ((σ.1 1 0 : ℤ) : ZMod p) = 0
  · refine ⟨⟨p, p.lt_succ_self⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simpa [Gamma0Rep] using h
  · obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ZMod p, (p : ℤ) ∣ σ.1 0 0 - (j₀.val : ℤ) * σ.1 1 0 :=
      ⟨_, dvd_sub_val_mul p hp _ _ h⟩
    refine ⟨⟨j₀.val, Nat.lt_succ_of_lt (ZMod.val_lt j₀)⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simp only [Gamma0Rep, ZMod.val_lt j₀, ite_true]
    rwa [TjS_inv_mul_10, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_sub_comm]

/-- `[SL₂(ℤ) : Γ₀(p)] = p + 1` for prime `p`. -/
theorem Gamma0_prime_index : (Gamma0 p).index = p + 1 :=
  Nat.card_eq_of_equiv_fin (Equiv.ofBijective _
    ⟨Gamma0_prime_index_inj p hp, Gamma0_prime_index_surj p hp⟩).symm

end BaseCase

section InductiveStep

variable (p : ℕ)

private def lowerTriRep (k : ℕ) (c : Fin p) : SL(2, ℤ) :=
  ⟨!![1, 0; (c : ℤ) * (p : ℤ) ^ k, 1], by simp [det_fin_two_of]⟩

variable (hp : Nat.Prime p)
include hp

end InductiveStep

end HeckeRing.GL2
