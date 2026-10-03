/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.FlatnessConditions

/-!
# Chord-to-tangent bounds from flatness

For a curve `γ` flat of order `n` at `t₀` with `γ(t₀) = s` and one-sided
derivative `L ≠ 0`, this file derives bounds on the chord from `γ(t)` to the
"natural" tangent point on the radius-ε circle at distance `ε = ‖γ(t) - s‖`.

The natural tangent point is `s + (ε/‖L‖) • L`, i.e., the unique point on the
ray `s + ℝ₊ · L` at distance `ε`. The chord
`‖γ(t) - s - (ε/‖L‖) • L‖`
decomposes via Pythagoras into:
- An orthogonal piece (= `tangentDeviation (γ(t)-s) L`), of size `o(ε^n)` by
  flatness.
- A parallel correction (deviation of the parallel projection from `ε/‖L‖`),
  of size `o(ε^{2n-1})` by Pythagoras + sqrt asymptotic.

Both are dominated by `o(ε^n)` for `n ≥ 1`, giving `chord = o(ε^n)`.

## Phase 3 context

This is Phase 3.3 of the HW Theorem 3.3 higher-order proof (Sub-phase 3 in the
plan). It bridges the parameter-based flatness condition (`IsFlatOfOrder`) to
the radius-based bound needed for the connecting-arc analysis.

For now we provide the **orthogonal deviation bound** directly from the
definition, which is the cleanest extraction. The full chord bound (orthogonal
plus parallel correction) is left as a documented sub-task: it requires
Pythagoras + sqrt asymptotic.
-/

open Set Filter Topology Asymptotics

namespace LeanModularForms

/-- **Pythagoras for `orthogonalProjectionComplex` and `tangentDeviation`.**
The squared norm of `w` decomposes into the squared norms of its parallel
projection on `L` and its orthogonal complement: this is the standard
orthogonal-decomposition identity in ℝ² (viewing ℂ as ℝ²). -/
theorem orthogonal_pythagoras (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖^2 + ‖tangentDeviation w L‖^2 = ‖w‖^2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [orthogonalProjectionComplex, tangentDeviation]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  unfold tangentDeviation orthogonalProjectionComplex
  simp only [Complex.real_smul]
  set u := (w * starRingEnd ℂ L).re with hu
  set N := Complex.normSq L
  have hN_ne : N ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  have h1 : Complex.normSq ((↑(u / N) : ℂ) * L) = (u / N) ^ 2 * N := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h2 : (w * starRingEnd ℂ ((↑(u / N) : ℂ) * L)).re = (u / N) * u := by
    rw [map_mul, Complex.conj_ofReal,
      show w * ((↑(u / N) : ℂ) * starRingEnd ℂ L) =
        (↑(u / N) : ℂ) * (w * starRingEnd ℂ L) by ring,
      Complex.mul_re]
    simp [hu]
  rw [Complex.normSq_sub, h1, h2]
  field_simp
  ring

/-- **Same-direction shortfall.** If `Re(w · conj L) ≥ 0`, then the parallel
projection's distance to the same-magnitude target on the +L ray equals the
difference in magnitudes:

`‖orthogonalProj w L − (‖w‖/‖L‖) • L‖ = ‖w‖ − ‖orthogonalProj w L‖`. -/
theorem norm_orthogonalProjection_minus_target_eq {w L : ℂ} (hL : L ≠ 0)
    (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖orthogonalProjectionComplex w L - (‖w‖ / ‖L‖ : ℝ) • L‖ =
      ‖w‖ - ‖orthogonalProjectionComplex w L‖ := by
  set c := (w * starRingEnd ℂ L).re / Complex.normSq L
  have hc_nonneg : 0 ≤ c := div_nonneg h_pos (Complex.normSq_pos.mpr hL).le
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_proj_norm : ‖orthogonalProjectionComplex w L‖ = c * ‖L‖ := by
    change ‖(c : ℝ) • L‖ = c * ‖L‖
    rw [norm_smul]
    simp [abs_of_nonneg hc_nonneg]
  have h_proj_le_w : ‖orthogonalProjectionComplex w L‖ ≤ ‖w‖ := by
    have h_sq : ‖orthogonalProjectionComplex w L‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      linarith [orthogonal_pythagoras w L, sq_nonneg ‖tangentDeviation w L‖]
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg w)).2
  have h_c_le_div : c ≤ ‖w‖ / ‖L‖ := by
    rw [le_div_iff₀ hL_norm_pos, ← h_proj_norm]; exact h_proj_le_w
  change ‖(c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L‖ = ‖w‖ - ‖orthogonalProjectionComplex w L‖
  rw [show (c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L = (c - ‖w‖ / ‖L‖ : ℝ) • L by module,
    norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h_c_le_div), h_proj_norm]
  field_simp
  ring

end LeanModularForms
