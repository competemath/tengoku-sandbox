/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Gaussian moments

Small, shared moment facts for real Gaussians used across the Brownian-motion
foundations (`BrownianMartingale`, `BrownianQuadraticVariation`, the L² quadratic
variation). Kept in one place so each identity is proved exactly once.

The fourth moment reuses Degenne's `(2n)`-th central-moment formula
(`ProbabilityTheory.centralMoment_two_mul_gaussianReal`) rather than re-deriving the
Gaussian integral — coherence with the upstream `brownian-motion` package.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`.
For a mean-zero law the second moment is the variance (`variance_id_gaussianReal`). -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

/-- **A centered squared Gaussian has mean zero**: `∫ (x² − v) ∂N(0,v) = 0`, i.e.
`E[X² − Var] = 0` for `X ~ N(0,v)`. (`E[X²] = v`.) -/
lemma integral_sq_sub_var_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ∂(gaussianReal 0 v) = 0 := by
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have huniv : (gaussianReal 0 v).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [integral_sub hint2 (integrable_const _), integral_sq_gaussianReal, integral_const, huniv,
      one_smul, sub_self]

end MathFin
