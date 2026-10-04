/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Tengoku

/-!
# Supermartingale Ville maximal inequality

Mathlib exposes only the submartingale maximal inequality `MeasureTheory.maximal_ineq`. This
file provides the nonnegative-supermartingale form (Ville's inequality): for a nonnegative
supermartingale `M` and any threshold `a`,

`a * μ.real {ω | a ≤ max_{k ≤ n} M_k ω} ≤ ∫ ω, M 0 ω ∂μ`.

The intended use is `a > 0`, where dividing by `a` gives `μ.real {max ≥ a} ≤ E[M 0] / a`; the
inequality itself needs no sign hypothesis. It is derived from the same hitting-time route that
underlies `maximal_ineq`, with the final step using the supermartingale optional-stopping bound
`E[M_τ] ≤ E[M_0]` (obtained by applying `Submartingale.expected_stoppedValue_mono` to `-M`).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace FormalSLT.AnytimeValid

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

end FormalSLT.AnytimeValid
