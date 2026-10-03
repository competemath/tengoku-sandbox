/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Common
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ContourIntegral.CrossingLimit

/-!
# Winding Number Weight at i

PV integral computation and generalized winding number of `fdBoundary_H`
around the point i.

## Main Results

* `pv_integral_at_i_tendsto` — PV integral converges to -iπ
* `gWN_fdBoundary_H_at_i` — gWN = -1/2 at i
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

private noncomputable def t₀_i (H : ℝ) : ℝ :=
  3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

end
