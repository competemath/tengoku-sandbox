/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Analytic.Linear
public import Tengoku.Seed.Analysis.Normed.Lp.PiLp

/-!
# Analyticity on `WithLp`
-/

public section

open WithLp

open scoped ENNReal

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s :=
  (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s

lemma analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

end WithLp

namespace PiLp

variable {𝕜 ι : Type*} [Fintype ι] {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s :=
  (continuousLinearEquiv p 𝕜 E).analyticOn s

lemma analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s :=
  (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

end PiLp
