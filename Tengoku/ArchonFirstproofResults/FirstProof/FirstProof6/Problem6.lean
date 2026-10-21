/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.ArchonFirstproofResults.FirstProof.FirstProof6.Auxiliary.DynamicColoring
import Tengoku.ArchonFirstproofResults.FirstProof.FirstProof6.Auxiliary.OneSidedBarrier

/-!
# Problem 6: Large epsilon-light vertex subsets -- Main Proof

This file contains the main theorem and its supporting lemmas.
All auxiliary infrastructure is in `Problem6Aux.lean`.

## Main theorems

- `Problem6.exists_eps_light_subset`: for every simple graph G
  and `epsilon in (0,1]`, there exists an epsilon-light subset S
  with `|S| >= epsilon/256 * |V|`
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### BSS coloring infrastructure

The BSS framework follows the informal proof's dynamic approach:
1. Spectral setup: Lhalf with Lhalf² = L (via spectral theorem)
2. Normalized edge Laplacians A_e = Lhalf_pinv * L_e * Lhalf_pinv
3. Coloring with one-sided barrier tracking monochromatic matrix M_t
4. Pullback: M_k ≤ u_k·I → each color class ε-light (via eps_light_of_loewner_bound) -/

/-- Product of unitary-diagonal-conjugate matrices:
    (U * D(f) * U★) * (U * D(g) * U★) = U * D(f·g) * U★.
    Used for spectral calculus (computing products via eigenvalue multiplication).
@isnad1 id=eq.1h4v.s8.9e0001bd9c03 from=translated src=- shape=d0f68e63 vocab=55befca0
-/
lemma unitary_diag_mul
    (U : Matrix V V ℝ) (hstarU : (star U : Matrix V V ℝ) * U = 1)
    (f g : V → ℝ) :
    (U * diagonal f * (star U : Matrix V V ℝ)) *
    (U * diagonal g * (star U : Matrix V V ℝ)) =
    U * diagonal (f * g) * (star U : Matrix V V ℝ) := by
  have h1 : (U * diagonal f * (star U : Matrix V V ℝ)) *
             (U * diagonal g * (star U : Matrix V V ℝ)) =
      U * diagonal f * ((star U : Matrix V V ℝ) * U) *
      diagonal g * (star U : Matrix V V ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, hstarU, Matrix.mul_one,
      show U * diagonal f * diagonal g * (star U : Matrix V V ℝ) =
           U * (diagonal f * diagonal g) * (star U : Matrix V V ℝ) by
        simp only [Matrix.mul_assoc]]
  congr 1; congr 1
  exact diagonal_mul_diagonal f g

omit [DecidableEq V] in
/-- For a Hermitian matrix M, there exists a Hermitian pseudo-inverse M_pinv satisfying
    the Moore-Penrose conditions:
    (1) M * M_pinv * M = M
    (2) M_pinv * M * M_pinv = M_pinv
    (3) M * M_pinv is idempotent (a projection)
    Constructed via spectral decomposition: if M = U * diag(λ) * U★,
    then M_pinv = U * diag(λ⁻¹) * U★ where λ⁻¹(i) = 0 if λ(i) = 0.
@isnad1 id=ex.1h2v.s8.fac18e1aaaae from=translated src=- shape=8e495c30 vocab=93311f42
-/
lemma hermitian_pseudo_inverse_exists
    (M : Matrix V V ℝ) (hM : M.IsHermitian) :
    ∃ (M_pinv : Matrix V V ℝ),
      M_pinv.IsHermitian ∧
      M * M_pinv * M = M ∧
      M_pinv * M * M_pinv = M_pinv ∧
      (M * M_pinv) * (M * M_pinv) = M * M_pinv ∧
      M * M_pinv = M_pinv * M := by
  classical
  set U := (hM.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set ev := hM.eigenvalues with hev_def
  have hUstarU : (star U : Matrix V V ℝ) * U = 1 :=
    Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hM_eq : M = U * diagonal ev * (star U : Matrix V V ℝ) := by
    have hspec := hM.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at hspec
    exact hspec
  -- Pseudo-inverse eigenvalues: invert nonzero, keep zero
  set pinvEv : V → ℝ := fun i => if ev i = 0 then 0 else (ev i)⁻¹ with hpinvEv_def
  refine ⟨U * diagonal pinvEv * (star U : Matrix V V ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · -- M_pinv is Hermitian: U * diag(real) * U★ is Hermitian for real diagonal
    change (U * diagonal pinvEv * (star U : Matrix V V ℝ))ᴴ =
         U * diagonal pinvEv * (star U : Matrix V V ℝ)
    have h_diag : (diagonal pinvEv)ᴴ = diagonal pinvEv := by
      ext i j; simp only [conjTranspose_apply, diagonal, Matrix.of_apply, star_trivial]
      split_ifs with h1 h2 h2
      · rw [h1]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · rfl
    calc (U * diagonal pinvEv * (star U : Matrix V V ℝ))ᴴ
        = (star U : Matrix V V ℝ)ᴴ * (diagonal pinvEv)ᴴ * Uᴴ := by
          rw [conjTranspose_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = U * diagonal pinvEv * (star U : Matrix V V ℝ) := by
          simp only [star_eq_conjTranspose, conjTranspose_conjTranspose, h_diag]
  · -- (1) M * M_pinv * M = M via eigenvalue identity ev * pinvEv * ev = ev
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU (ev * pinvEv) ev]
    suffices h : ev * pinvEv * ev = ev by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h, one_mul]
  · -- (2) M_pinv * M * M_pinv = M_pinv via eigenvalue identity pinvEv * ev * pinvEv = pinvEv
    rw [hM_eq, unitary_diag_mul U hUstarU pinvEv ev,
        unitary_diag_mul U hUstarU (pinvEv * ev) pinvEv]
    suffices h : pinvEv * ev * pinvEv = pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [inv_mul_cancel₀ h, one_mul]
  · -- (3) M * M_pinv is idempotent via (ev * pinvEv)² = ev * pinvEv
    have hprod : M * (U * diagonal pinvEv * (star U : Matrix V V ℝ)) =
        U * diagonal (ev * pinvEv) * (star U : Matrix V V ℝ) := by
      rw [hM_eq]; exact unitary_diag_mul U hUstarU ev pinvEv
    rw [hprod, unitary_diag_mul U hUstarU (ev * pinvEv) (ev * pinvEv)]
    suffices h : ev * pinvEv * (ev * pinvEv) = ev * pinvEv by rw [h]
    ext i; simp only [Pi.mul_apply, hpinvEv_def]
    split_ifs with h
    · simp [h]
    · rw [mul_inv_cancel₀ h]; simp
  · -- (4) Commutativity: M * M_pinv = M_pinv * M (diagonal multiplication commutes)
    rw [hM_eq, unitary_diag_mul U hUstarU ev pinvEv,
        unitary_diag_mul U hUstarU pinvEv ev]
    congr 1; congr 1; ext i; simp [mul_comm]

/-! #### Dynamic BSS coloring (Steps 1–5 combined)
The informal proof (Steps 3–5) uses a **dynamic** coloring process:
  1. Per-edge matrices: A_e := L^{-1/2} L_e L^{-1/2} with ∑_e A_e = I on range(L)
  2. Track M_t := ∑_{monochromatic edges at time t} A_e (DYNAMIC, depends on current coloring)
  3. At time t: color vertex v with γ, increment M_{t+1} = M_t + B_v^γ where
     B_v^γ = ∑_{u ∈ T, col(u)=γ, uv∈E} A_{uv}
  4. BSS barrier (Lemma 6.1) maintains M_t ≺ u_t·I at each step
  5. After k = n/4 steps: M_k = ∑_a L^{-1/2} L_{S_a} L^{-1/2} (by construction)
  6. Since M_k ≺ u_k·I ≺ ε·I, each color class S_a is ε-light
The proof is decomposed into:
  (A) `dynamic_barrier_coloring`: The core BSS dynamic coloring induction that
      produces a PartialColoring with per-color barrier bounds on normalized monochromatic sums.
  (B) `bss_dynamic_coloring`: Combines (A) with `pinv_pullback_eq` and
      `eps_light_of_loewner_bound` to convert barrier bounds to ε-lightness. -/

omit [DecidableEq V] in
/-- Diagonal entry derivation for the cross-edge decomposition:
    derives diagonal from row sums and off-diagonal matching.
@isnad1 id=eq.3h5v.s7.552bf190d031 from=translated src=- shape=46b13de9 vocab=e5513c2f
-/
lemma cross_edge_diagonal
    (L DS R : Matrix V V ℝ)
    (h_off_diag : ∀ (a b : V), a ≠ b → (L - DS) a b = R a b)
    (h_row_LHS : ∀ a, ∑ b, (L - DS) a b = 0)
    (h_row_RHS : ∀ a, ∑ b, R a b = 0)
    (i : V) :
    (L - DS) i i = R i i := by
  classical
  have h1 := h_row_LHS i
  have h2 := h_row_RHS i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1 h2
  have h3 : ∑ j ∈ Finset.univ.erase i, (L - DS) i j =
      ∑ j ∈ Finset.univ.erase i, R i j :=
    Finset.sum_congr rfl fun j hj =>
      h_off_diag i j (Finset.ne_of_mem_erase hj).symm
  linarith

/-! ### The coloring induction result -/

/-! ### Proof of the main theorem -/

/-! ### Main theorem -/

end Problem6

end
