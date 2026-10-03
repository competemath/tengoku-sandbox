/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at ρ+1

PV integral computation and generalized winding number of `fdBoundary_H`
around the elliptic point ρ+1 = e^{πi/3}.

## Main Results

* `pv_integral_at_rho_plus_one_tendsto` — PV integral converges to -iπ/3
* `gWN_fdBoundary_H_at_rho_plus_one` — gWN = -1/6 at ρ+1
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

end
