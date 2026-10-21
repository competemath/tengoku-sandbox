/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.ArchonFirstproofResults.FirstProof.FirstProof6.Auxiliary.ColoringFramework
import Tengoku.ArchonFirstproofResults.FirstProof.FirstProof6.Auxiliary.LoewnerPullback

/-!
# Problem 6: Large epsilon-light vertex subsets -- Dynamic Coloring

Key infrastructure for the dynamic BSS coloring:
1. `inducedLaplacian_le_graphLaplacian`: L_S <= L (Loewner)
2. `hermitian_mulVec_zero_of_sq_zero`: kernel transfer
3. `pinv_pullback_eq`: pseudo-inverse pullback identity
4. `inducedLaplacian_posSemidef`, `normalized_mono_psd`

## Main theorems

- `Problem6.inducedLaplacian_posSemidef`: induced Laplacian PSD
- `Problem6.inducedLaplacian_le_graphLaplacian`: Loewner bound
- `Problem6.hermitian_mulVec_zero_of_sq_zero`: kernel transfer
- `Problem6.pinv_pullback_eq`: pseudo-inverse pullback
- `Problem6.normalized_laplacian_eq_proj`: projection identity
- `Problem6.proj_le_one`: projection bounded by identity
- `Problem6.normalized_mono_psd`: normalized monochromatic PSD
- `Problem6.inducedLaplacian_mono`: monotonicity in subsets
- `Problem6.psd_sub_sum_le`: PSD extraction from sum bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Loewner bound: induced Laplacian ≤ graph Laplacian -/

/-! ### Kernel transfer: ker(Lhalf²) = ker(Lhalf) for Hermitian matrices -/

omit [DecidableEq V] in
/-- For a Hermitian matrix Lhalf over ℝ, if Lhalf * Lhalf * x = 0 then Lhalf * x = 0.
    Proof: ‖Lhalf x‖² = xᵀ Lhalf² x = xᵀ 0 = 0.
@isnad1 id=eq.2h3v.s7.dd0dc81ba7f6 from=translated src=- shape=f2fc3e78 vocab=12b68fe3
-/
lemma hermitian_mulVec_zero_of_sq_zero
    (Lhalf : Matrix V V ℝ) (hLhalf_herm : Lhalf.IsHermitian) (x : V → ℝ)
    (hx : (Lhalf * Lhalf) *ᵥ x = 0) :
    Lhalf *ᵥ x = 0 := by
  -- ‖Lhalf x‖² = ∑ i, ((Lhalf x) i)² = 0 implies Lhalf x = 0
  -- Key: ∑ i, ((Lhalf x) i)² = (Lhalf x)^T (Lhalf x) = x^T Lhalf^T Lhalf x
  --   = x^T Lhalf² x = x^T 0 = 0 (using Lhalf^T = Lhalf since Hermitian over ℝ)
  suffices h_zero : ∀ i, (Lhalf *ᵥ x) i = 0 by ext i; exact h_zero i
  intro i
  -- Compute the squared norm
  have h_sq_sum : ∑ j, (Lhalf *ᵥ x) j * (Lhalf *ᵥ x) j = 0 := by
    -- Key: ‖Lhalf x‖² = (Lhalf x) ⬝ (Lhalf x) = x ⬝ (Lhalf² x) = x ⬝ 0 = 0
    change (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = 0
    -- Since Lhalf is Hermitian, (Lhalf*x) ⬝ (Lhalf*x) = x ⬝ (Lhalf² x)
    have h2 : (Lhalf *ᵥ x) ⬝ᵥ (Lhalf *ᵥ x) = x ⬝ᵥ ((Lhalf * Lhalf) *ᵥ x) := by
      -- Rewrite Lhalf * Lhalf = Lhalfᴴ * Lhalf (Hermiticity)
      -- Then (Lhalfᴴ * Lhalf) *ᵥ x = Lhalfᴴ *ᵥ (Lhalf *ᵥ x) [← mulVec_mulVec]
      -- Then x ⬝ᵥ (Lhalfᴴ *ᵥ y) = (x ᵥ* Lhalfᴴ) ⬝ᵥ y [dotProduct_mulVec]
      -- Then x v* LhalfH = star (Lhalf *v star x) = Lhalf *v x
      rw [show Lhalf * Lhalf = Lhalfᴴ * Lhalf from by rw [hLhalf_herm.eq]]
      simp only [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
      simp [star_trivial]
    rw [h2, hx, dotProduct_zero]
  -- From ∑ ((Lhalf x) j)² = 0 and each term ≥ 0, each term = 0
  have h_nn : ∀ j, 0 ≤ (Lhalf *ᵥ x) j * (Lhalf *ᵥ x) j :=
    fun j => mul_self_nonneg _
  exact mul_self_eq_zero.mp
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nn j) |>.mp h_sq_sum i (Finset.mem_univ i))

/-! ### Pseudo-inverse pullback identity -/

/-! ### Normalized monochromatic matrix -/

/-! ### Normalized projection sum: Lhalf_pinv * L * Lhalf_pinv = P -/

/-- The normalized graph Laplacian equals the projection P = Lhalf * Lhalf_pinv.
    Proof: Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv)
    = P * P = P (using MP4 for commutativity, MP3 for idempotence).
@isnad1 id=eq.3h4v.s8.7936ed564f9d from=translated src=- shape=b0dfe274 vocab=8d0f2673
-/
lemma normalized_laplacian_eq_proj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Lhalf Lhalf_pinv : Matrix V V ℝ)
    (hLhalf_sq : Lhalf * Lhalf = graphLaplacian G)
    (hMP3 : (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) = Lhalf * Lhalf_pinv)
    (hMP4 : Lhalf * Lhalf_pinv = Lhalf_pinv * Lhalf) :
    Lhalf_pinv * graphLaplacian G * Lhalf_pinv = Lhalf * Lhalf_pinv := by
  rw [← hLhalf_sq]
  -- Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv
  -- = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv)   [by mul_assoc]
  -- = P * P = P  [by MP4 and MP3]
  calc Lhalf_pinv * (Lhalf * Lhalf) * Lhalf_pinv
      = (Lhalf_pinv * Lhalf) * (Lhalf * Lhalf_pinv) := by
        simp only [Matrix.mul_assoc]
    _ = (Lhalf * Lhalf_pinv) * (Lhalf * Lhalf_pinv) := by rw [← hMP4]
    _ = Lhalf * Lhalf_pinv := hMP3

/-- P ≤ I in Loewner order (since P is an orthogonal projection).
    Proof: (I - P) is PSD because (I - P) = (I - P)^2 for idempotent Hermitian P,
    and X^2 is PSD for any Hermitian X.
@isnad1 id=possemid.2h2v.s6.62b3819b41a9 from=translated src=- shape=a77836bc vocab=40e1d062
-/
lemma proj_le_one
    (P : Matrix V V ℝ)
    (hP_herm : P.IsHermitian)
    (hP_idem : P * P = P) :
    ((1 : Matrix V V ℝ) - P).PosSemidef := by
  -- (I - P)^2 = I - 2P + P^2 = I - 2P + P = I - P
  -- So I - P = (I - P)^T * (I - P) is PSD
  have hQ_herm : ((1 : Matrix V V ℝ) - P).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hP_herm.eq]
  have hQ_idem : ((1 : Matrix V V ℝ) - P) * ((1 : Matrix V V ℝ) - P) =
      (1 : Matrix V V ℝ) - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP_idem, sub_self, sub_zero]
  rw [show (1 : Matrix V V ℝ) - P =
    ((1 : Matrix V V ℝ) - P)ᴴ * ((1 : Matrix V V ℝ) - P) from by
      rw [hQ_herm.eq, hQ_idem]]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### Monotonicity and extraction for the BSS coloring -/

omit [Fintype V] in
/-- PSD extraction: if the total sum ∑_γ M_γ is bounded by u·I and each M_γ is PSD,
    then each individual M_γ is bounded by u·I.
    Proof: u·I - M_γ = (u·I - ∑ M_γ') + ∑_{γ'≠γ} M_γ' = PSD + PSD.
@isnad1 id=possemid.2h5v.s7.bae27bdd96e3 from=translated src=- shape=3df99f17 vocab=e063f62b
-/
lemma psd_sub_sum_le {r : ℕ} (M : Fin r → Matrix V V ℝ) (u : ℝ)
    (hM_psd : ∀ γ, (M γ).PosSemidef)
    (h_total : (u • (1 : Matrix V V ℝ) - ∑ γ : Fin r, M γ).PosSemidef) :
    ∀ γ : Fin r, (u • (1 : Matrix V V ℝ) - M γ).PosSemidef := by
  intro γ
  have h_split : u • (1 : Matrix V V ℝ) - M γ =
      (u • (1 : Matrix V V ℝ) - ∑ γ' : Fin r, M γ') +
      ∑ γ' ∈ Finset.univ.erase γ, M γ' := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ γ)]; abel
  rw [h_split]
  exact h_total.add (Finset.sum_induction _ (fun (A : Matrix V V ℝ) => A.PosSemidef)
    (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun γ' _ => hM_psd γ'))

end Problem6

end
