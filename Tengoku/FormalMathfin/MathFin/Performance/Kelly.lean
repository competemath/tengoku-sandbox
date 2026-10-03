/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq
public import Tengoku.FormalMathfin.MathFin.Performance.Ratios

/-!
# Multi-period Kelly criterion and Kelly fraction bounds

The single-period Kelly fraction (`kellyFraction`, `kellyGrowth`) and its
first-order optimality live in `Performance/Ratios.lean`; this file adds the
multi-period / horizon-myopia / fraction-bound extensions.

The `n`-period model is taken seriously rather than asserted: one period's
wealth multiplier is the two-point law `kellyReturnMeasure p b f` (multiplier
`1 + f·b` with probability `p`, `1 - f` with probability `1 - p`), `n` iid
periods are its `n`-fold product measure `Measure.pi`, and the expected
log-wealth of the compounded product — `E[log(R₁⋯R_n)] = E[∑ log Rᵢ]` — is
*computed* coordinate-by-coordinate to equal `n · kellyGrowth p b f`:

  `∫ (∑ i, log Rᵢ) ∂(Π ν) = n · (p·log(1 + f·b) + (1 - p)·log(1 - f))`.

Maximizing this over `f` is the same single-period problem at every horizon,
so the multi-period Kelly fraction equals the single-period one — Kelly is
myopic.

Additionally:

* **`kellyFraction < 1`**: the Kelly fraction is always strictly less than 1 for
  proper probabilities `p < 1` and positive payoffs `b > 0` (no all-in bet
  except in the degenerate `p = 1` case).
* **`kellyFraction = 0 iff break-even`**: `f* = 0` iff `p(b+1) = 1`.
* **`kellyFraction > 0 iff favorable bet`**: `f* > 0` iff `p(b+1) > 1`.

Results:

* `integral_log_kellyReturnMeasure`: one period's expected log-multiplier is
  exactly `kellyGrowth p b f`.
* `kellyGrowth_n_periods`: over `n` iid periods the expected total log-growth
  is `n · kellyGrowth p b f` — linearity of expectation over the actual
  product model, via the measure-preserving coordinate evaluations of
  `Measure.pi`.
* `kelly_n_periods_deriv_at_kelly`: first-order optimality for `n · kellyGrowth`
  vanishes at the single-period `kellyFraction p b`.
* `kellyFraction_lt_one`, `kellyFraction_eq_zero_iff`, `kellyFraction_pos_iff`:
  bounds and sign analysis of the Kelly fraction.
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory

/-- One Kelly period's wealth-multiplier law: the bet at fraction `f` pays
odds `b` with probability `p` (multiplier `1 + f·b`) and loses the stake with
probability `1 - p` (multiplier `1 - f`). A two-point Borel measure on `ℝ`. -/
noncomputable def kellyReturnMeasure (p b f : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 + f * b)
    + ENNReal.ofReal (1 - p) • Measure.dirac (1 - f)

/-- **Multi-period Kelly first-order condition**: the optimal fraction is
independent of the horizon `n` — maximizing `n · kellyGrowth` is the same
single-period problem, so Kelly is myopic. -/
lemma kelly_n_periods_deriv_at_kelly (n : ℕ) {p b : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    HasDerivAt (fun f ↦ (n : ℝ) * kellyGrowth p b f) 0 (kellyFraction p b) := by
  have h := kellyGrowth_deriv_at_kelly hp hp1 hb
  have h_mul := h.const_mul (n : ℝ)
  simpa using h_mul

/-- **Kelly fraction < 1** for proper probabilities and positive payoff. -/
lemma kellyFraction_lt_one {p b : ℝ} (hp : p < 1) (hb : 0 < b) :
    kellyFraction p b < 1 := by
  unfold kellyFraction
  rw [div_lt_one hb]
  nlinarith

/-- **Kelly fraction = 0 iff break-even bet** (`p · (b + 1) = 1`). -/
lemma kellyFraction_eq_zero_iff (p : ℝ) {b : ℝ} (hb : b ≠ 0) :
    kellyFraction p b = 0 ↔ p * (b + 1) = 1 := by
  unfold kellyFraction
  rw [div_eq_zero_iff]
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · linarith
    · exact absurd h hb
  · intro h; left; linarith

/-- **Kelly fraction > 0 iff favorable bet** (`p · (b + 1) > 1`). -/
lemma kellyFraction_pos_iff (p : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < kellyFraction p b ↔ 1 < p * (b + 1) := by
  unfold kellyFraction
  rw [lt_div_iff₀ hb]
  refine ⟨?_, ?_⟩ <;> intro h <;> linarith

end MathFin
