/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.CompactHeatFlow
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel

/-! # Heat evolution as an actual Brownian expectation, including time zero 
## Result

Public entry points include `brownianHeatFlow`, `brownianHeatFlow_zero`, `brownianHeatFlow_continuous`, `brownianHeatFlow_bound`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open MathFin.FeynmanKacHeatEquation
open scoped NNReal Topology

end MathFin.BlackScholes.AmericanPut.Stopping
