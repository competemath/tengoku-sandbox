/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.ExerciseRegion
public import Tengoku

/-!
# A constructed Brownian model for the American stopping value

The dependency constructs a continuous Brownian motion on its Gaussian
probability space. We use its natural filtration, prove the filtered Brownian
property, and instantiate the finite-horizon American value. No existence of
a PDE solution is assumed or proved here. Equality with a value defined using
the usual augmented filtration is a separate verification obligation.

## Result

Public entry points include `brownianFiltration`, `brownian_filtered`, `brownian_adapted`, `brownianAmericanPut`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory ProbabilityTheory
open scoped NNReal

end MathFin.BlackScholes.AmericanPut.Stopping
