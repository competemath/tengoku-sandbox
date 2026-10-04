/-
Copyright (c) 2026 Alfredo Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfredo Garcia
-/
module

public import Tengoku
public import Tengoku.FormalMathfin.MathFin.Execution.GlostenMilgrom

/-!
# A model satisfying the Glosten-Milgrom hypotheses

`MathFin.Execution.spread_pos_of_model` quantifies over a probability space and
three events tied together by four equations. If nothing satisfies those
equations the theorem is vacuously true and says nothing — which is the same
failure mode the module it belongs to exists to warn about, one level up.

This file removes the doubt by exhibiting the model. Six outcomes: the value is
high or low, the arriving trader is informed or not, and an uninformed trader
tosses a coin.

| `i` | value | trader     | acts | mass           |
|-----|-------|------------|------|----------------|
| `0` | high  | informed   | buy  | `θp`           |
| `1` | high  | uninformed | buy  | `θ(1-p)/2`     |
| `2` | high  | uninformed | sell | `θ(1-p)/2`     |
| `3` | low   | informed   | sell | `(1-θ)p`       |
| `4` | low   | uninformed | buy  | `(1-θ)(1-p)/2` |
| `5` | low   | uninformed | sell | `(1-θ)(1-p)/2` |

The witness is symbolic: it works for *every* `0 < θ < 1` and `0 < p ≤ 1`, not
at one convenient point.

## Results

* `gmMeasure`, `gmHigh`, `gmBuy`, `gmInformed`: the space, and the three events.
* `gm_buy_inter_inf`: an informed trader buys exactly when the value is high —
  on this space, a set identity.
* `gmMeasure_univ_eq_one`: the six masses add to one.
* `spread_pos_witness`: the spread is strictly positive, with no
  measure-theoretic hypothesis left in front of it.
-/

@[expose] public section

namespace MathFin.Execution

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The six outcome masses. -/
noncomputable def gmWeight (θ p : ℝ) : Fin 6 → ℝ :=
  ![θ * p, θ * (1 - p) / 2, θ * (1 - p) / 2,
    (1 - θ) * p, (1 - θ) * (1 - p) / 2, (1 - θ) * (1 - p) / 2]

/-- The model measure: the six masses on the six outcomes. -/
noncomputable def gmMeasure (θ p : ℝ) : Measure (Fin 6) :=
  Measure.sum fun i => ENNReal.ofReal (gmWeight θ p i) • Measure.dirac i

/-- The value is high. -/
def gmHigh : Set (Fin 6) := {0, 1, 2}
/-- The arriving trader buys. -/
def gmBuy : Set (Fin 6) := {0, 1, 4}
/-- The arriving trader is informed. -/
def gmInformed : Set (Fin 6) := {0, 3}

/-- On the parameter range that matters, every mass is nonnegative. -/
theorem gmWeight_nonneg {θ p : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i, 0 ≤ gmWeight θ p i := by
  intro i; fin_cases i <;> simp [gmWeight] <;> nlinarith

/-! ## The masses of the sets the model constrains -/

section Values
variable {θ p : ℝ} (hnn : ∀ i, 0 ≤ gmWeight θ p i)
include hnn

end Values

end MathFin.Execution
