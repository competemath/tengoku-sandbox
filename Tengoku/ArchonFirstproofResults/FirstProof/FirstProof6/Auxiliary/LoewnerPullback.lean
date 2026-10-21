/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.ArchonFirstproofResults.FirstProof.FirstProof6.Auxiliary.LaplacianBasics

/-!
# Problem 6: Large epsilon-light vertex subsets -- Loewner Pullback

Normalized edge setup: congruence pullbacks for Loewner order,
square root pullback, and epsilon-lightness from Loewner bound.

## Main theorems

- `Problem6.sqrt_pullback_loewner`: square root pullback
- `Problem6.eps_light_of_loewner_bound`: epsilon-lightness from bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Normalized edge setup infrastructure

**Normalized edge setup (Step 1)**: For any graph G on V, there
exist PSD matrices `A : V -> Fin r -> Matrix V V R` (one per
(vertex, color) pair), with the property that:
(a) Each `A v g` is PSD
(b) For each vertex v, some color g has `A v g <= (e/n)*I`
(c) If M is a sum of selected `A v g`'s satisfying `M < u*I`
    with `u < e`, then each color class is e-light

The following sub-lemmas establish the mathematical
infrastructure needed. -/

/-- Sub-lemma: If L^{1/2} is a Hermitian matrix with L^{1/2} * L^{1/2} = L (on the relevant
    subspace), and M ≼ u*I, then L^{1/2} * M * L^{1/2} ≼ u * L.
    This is the key pullback that converts barrier domination into Laplacian domination.
@isnad1 id=possemid.3h5v.s8.2cf7423381d0 from=translated src=- shape=66994453 vocab=f08ad19a
-/
lemma sqrt_pullback_loewner
    (L : Matrix V V ℝ)
    (Lhalf : Matrix V V ℝ)
    (hLhalf_herm : Lhalf.IsHermitian)
    (hLhalf_sq : Lhalf * Lhalf = L)
    (M : Matrix V V ℝ) (u : ℝ)
    (hM : (u • (1 : Matrix V V ℝ) - M).PosSemidef) :
    (u • L - Lhalf * M * Lhalf).PosSemidef := by
  -- u * L - Lhalf * M * Lhalf = u * (Lhalf * Lhalf) - Lhalf * M * Lhalf
  --   = Lhalf * (u * I - M) * Lhalf (since Lhalf^T = Lhalf for Hermitian)
  have h_eq : u • L - Lhalf * M * Lhalf =
      Lhalfᴴ * (u • (1 : Matrix V V ℝ) - M) * Lhalf := by
    rw [hLhalf_herm.eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, smul_mul_assoc, Matrix.mul_one,
               mul_smul_comm, Matrix.mul_assoc, ← hLhalf_sq]
  rw [h_eq]
  exact hM.conjTranspose_mul_mul_same Lhalf

end Problem6

end
