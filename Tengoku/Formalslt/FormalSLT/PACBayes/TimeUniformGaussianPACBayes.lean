/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Tengoku.Formalslt.FormalSLT.PACBayes.GaussianMeasureKL
import Tengoku.Formalslt.FormalSLT.PACBayes.TimeUniformContinuousPACBayes

/-!
# Time-uniform spherical-Gaussian PAC-Bayes bound

This module specializes the continuous process-level PAC-Bayes theorem to the
repository's finite-dimensional spherical Gaussian measures.  The abstract
measure-theoretic `klDiv` penalty is replaced by the explicit closed form

`(d * (posteriorVariance / priorVariance - 1 +
    log (priorVariance / posteriorVariance)) +
    squaredMeanDistance posteriorMean priorMean / priorVariance) / 2`.

The Gaussian probability-measure instances, posterior-to-prior absolute
continuity, log-likelihood-ratio integrability, and KL identification are all
discharged by the measure-theoretic Gaussian bridge.  The score-process and
Fubini integrability assumptions remain explicit.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FormalSLT.PACBayes.TimeUniformGaussian

open TimeUniformContinuous

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Failure event for the spherical-Gaussian specialization, with the Gaussian
KL penalty written in the repository's explicit finite-dimensional closed
form. -/
def timeUniformSphericalGaussianPACBayesUpperFailure {d : ℕ}
    (prior posterior : SphericalGaussianParams d)
    (score : GaussianParameterSpace d → ℕ → Ω → ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    sphericalGaussianKLClosedForm posterior prior + Real.log (1 / delta)
      ≤ ∫ θ, score θ n ω ∂sphericalGaussianMeasure posterior}

/-- The explicit spherical-Gaussian failure event is exactly the abstract
continuous PAC-Bayes failure event for the corresponding Gaussian measures. -/
theorem timeUniformSphericalGaussianPACBayesUpperFailure_eq_continuous
    {d : ℕ} (prior posterior : SphericalGaussianParams d)
    (score : GaussianParameterSpace d → ℕ → Ω → ℝ) (delta : ℝ) :
    timeUniformSphericalGaussianPACBayesUpperFailure
        prior posterior score delta =
      timeUniformContinuousPACBayesUpperFailure
        (sphericalGaussianMeasure prior)
        (sphericalGaussianMeasure posterior) score delta := by
  ext ω
  simp [timeUniformSphericalGaussianPACBayesUpperFailure,
    timeUniformContinuousPACBayesUpperFailure,
    sphericalGaussianMeasure_klDiv_toReal_eq,
    sphericalGaussianKL_eq_closedForm]

end

end FormalSLT.PACBayes.TimeUniformGaussian
