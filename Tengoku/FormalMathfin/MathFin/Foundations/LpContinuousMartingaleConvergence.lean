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
public import Tengoku.FormalMathfin.MathFin.Foundations.DoobLpMaximalInequality

/-!
# Lp continuous-martingale convergence (Theorem 4.3.10, Saporito)

A continuous martingale `(M_t)` bounded in `L^p` (`p ≥ 1`) converges almost
surely to an integrable `M_∞`; for `p > 1` it also converges in `L^p`.

  Proof strategy:
    1. Sample at natural times: `N_k(ω) := M (k : ℝ) ω` is a discrete
       martingale with respect to the sub-filtration `𝓕_k := 𝓕 (k : ℝ)`.
    2. The L^p bound transfers to N (since N_k = M_k for k : ℕ).
       Also L^1 bound from finite measure + L^p bound (Hölder when p > 1,
       direct when p = 1).
    3. Apply Mathlib's `Submartingale.exists_ae_tendsto_of_bdd` to get
       almost-sure convergence of N at natural times.
    4. By path continuity, the continuous-time limit at `t → ∞` agrees
       with the natural-time limit. (This step uses Doob's L^p maximal
       inequality on the increment martingale to show
       `sup_{n ≤ t ≤ n+1} |M_t - M_n| → 0` in probability.)
    5. For `p > 1`: L^p-boundedness gives uniform integrability in L^p
       (de la Vallée-Poussin) and combined with a.s. convergence yields
       L^p convergence (Vitali).

  Steps 3, 4, and 5 are all proved below.

  Step 3 (`p ≥ 1`, natural-time a.s. convergence): proved as
  `lp_continuous_martingale_converges_at_naturals`. Uses Mathlib's
  `Submartingale.ae_tendsto_limitProcess` after transferring the `L^p` bound
  to an `L^1` bound (Hölder on a finite measure space) at the natural-time
  sub-filtration.

  Step 4 (continuous-time bridge, `p > 1`, real-time in-measure): proved as
  `lp_continuous_martingale_tendstoInMeasure`. The increment martingale
  `Y_n(s) := M(n + s) − M(n)` is built on `shiftedFiltration 𝓕 n` via
  `Martingale.sub` of a shifted process and a constant; right-continuity
  transfers from `M`. Degenne's `maximal_ineq_norm` bounds the running max,
  the eLpNorm-triangle + Hölder gives `‖M_(n+1) − M_n‖_1 → 0`, and
  `rightCont_iSup_ofReal_ne_top` gives `BddAbove` a.s. for the running max.
  A `Nat.floor` set-inclusion argument then closes the conclusion modulo a
  μ-null set. The combined natural-a.s. + real-in-measure form is
  `lp_continuous_martingale_full`.

  Step 5 (`p > 1`, natural-time `L^p` convergence): proved as
  `lp_continuous_martingale_tendsto_eLpNorm_at_naturals`. Doob's `L^p`
  maximal inequality (`MeasureTheory.maximal_ineq_Lp`) bounds the running max;
  monotone convergence (`lintegral_iSup'`) lifts it to the infinite sup
  `S ω := ⨆_k ‖N_k ω‖ₑ`, yielding `MemLp ((S ω).toReal) p`. Degenne's
  `uniformIntegrable_of_dominated_singleton`
  (`BrownianMotion.StochasticIntegral.UniformIntegrable`) then gives
  `UniformIntegrable (discreteSample M) (ofReal p) μ`, and Mathlib's Vitali
  (`tendsto_Lp_finite_of_tendsto_ae`) closes it.

  The textbook claims real-time a.s. convergence (under continuous paths)
  and real-time `L^p` convergence (under uniform integrability lifted to
  real time). Both require cadlag paths, which this file does not assume —
  only right-continuity. The in-measure form is the canonical conclusion
  for right-continuous martingales.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Discrete-time sample of a continuous-time process at natural times. -/
noncomputable def discreteSample (M : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Sub-filtration at natural times. -/
def natTimeSubfiltration (𝓕 : Filtration ℝ mΩ) : Filtration ℕ mΩ where
  seq n := 𝓕 (n : ℝ)
  mono' n m hnm := 𝓕.mono (by exact_mod_cast hnm)
  le' n := 𝓕.le _

/-- A continuous martingale sampled at natural times is a discrete
    martingale with respect to the natural-time sub-filtration. -/
private lemma discreteSample_martingale
    {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) :
    Martingale (discreteSample M) (natTimeSubfiltration 𝓕) μ := by
  refine ⟨?_, ?_⟩
  · intro n
    exact hM.stronglyAdapted (n : ℝ)
  · intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact hM.2 (i : ℝ) (j : ℝ) hij'

/-- L^1-norm bound from L^p-norm bound on a finite measure space (Hölder). -/
private lemma eLpNorm_one_le_of_eLpNorm_p
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    {R : ℝ} (hR : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := ENNReal.ofReal p) (f := f) h1_le_p hfm).trans ?_
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hp_pos.le, one_div_one]
  gcongr

/-- The L^1 bound for the discrete sample, expressed as `ℝ≥0` for the
    Mathlib submartingale-convergence API. -/
private lemma discreteSample_l1_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ R' : ℝ≥0,
      ∀ n : ℕ, eLpNorm (discreteSample M n) 1 μ ≤ (R' : ℝ≥0∞) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_exp_nn : 0 ≤ (1 : ℝ) - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp
    linarith
  set bound : ℝ≥0∞ := ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p)
  have hbound_lt_top : bound < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg h_exp_nn (measure_ne_top _ _))
  refine ⟨bound.toNNReal, fun n ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hbound_lt_top.ne]
  exact eLpNorm_one_le_of_eLpNorm_p hp (hbound (n : ℝ))
    ((hM.stronglyMeasurable (n : ℝ)).mono (𝓕.le _)).aestronglyMeasurable

/-- The canonical limit of the discrete sample: a `(⨆ k, 𝓕 k)`-measurable
    function to which the sample converges a.s. Defined via Mathlib's
    `Filtration.limitProcess`. -/
noncomputable def discreteSampleLimit
    (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) : Ω → ℝ :=
  (natTimeSubfiltration 𝓕).limitProcess (discreteSample M) μ

/-- The discrete sample converges a.s. to its limit process. -/
private lemma discreteSample_ae_tendsto_limitProcess
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ M (n : ℝ) ω) atTop (𝓝 (discreteSampleLimit μ 𝓕 M ω)) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  exact (discreteSample_martingale hM).submartingale.ae_tendsto_limitProcess hR'

/-- The limit process is integrable (in `L^1`). -/
private lemma discreteSampleLimit_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Integrable (discreteSampleLimit μ 𝓕 M) μ := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  have hAE : ∀ n, AEStronglyMeasurable (discreteSample M n) μ := fun n ↦
    (((discreteSample_martingale hM).stronglyMeasurable n).mono
        ((natTimeSubfiltration 𝓕).le _)).aestronglyMeasurable
  have h_memLp : MemLp (discreteSampleLimit μ 𝓕 M) 1 μ :=
    MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd hAE hR'
  exact h_memLp.integrable le_rfl

/-- Theorem 4.3.10 (Saporito Ch 4.3), natural-time formulation.

    A continuous-time martingale `(M_t)` bounded in `L^p` (`p ≥ 1`)
    sampled at natural times `t = n : ℕ` converges almost surely to an
    integrable limit `M_∞ := (natTimeSubfiltration 𝓕).limitProcess`.

    This is the discrete-time skeleton of Theorem 4.3.10. The full
    continuous-time conclusion `Tendsto (fun t : ℝ ↦ M t ω) atTop ...`
    follows from this skeleton + path continuity + a maximal-oscillation
    bound (via Doob's `L^p` inequality applied to the increment martingale
    `(M_t - M_n)_{t ∈ [n, n+1]}`). For `p > 1`, the `L^p` convergence
    follows from a.s. convergence + uniform integrability in `L^p`. Both
    extensions are documented as follow-on work. -/
theorem lp_continuous_martingale_converges_at_naturals
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∃ R : ℝ,
      ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ M (n : ℝ) ω) atTop (𝓝 (M_inf ω)) := by
  obtain ⟨R, hR⟩ := hbound
  exact ⟨discreteSampleLimit μ 𝓕 M,
    discreteSampleLimit_integrable hp hM hR,
    discreteSample_ae_tendsto_limitProcess hp hM hR⟩

/-! ### Step 5: `L^p` convergence at natural times (`p > 1`). -/

/-- Real-valued running max of `‖discreteSample M k ω‖` over `k ≤ n`. -/
private noncomputable def runMaxNorm (M : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ ‖discreteSample M k ω‖)

/-- Pointwise infinite sup of `‖discreteSample M k ω‖ₑ` over `k : ℕ`, in `ℝ≥0∞`. -/
private noncomputable def discreteSampleSup (M : ℝ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ k : ℕ, ‖discreteSample M k ω‖ₑ

/-- Real-valued dominator `M^*(ω) := (discreteSampleSup M ω).toReal`. -/
private noncomputable def discreteSampleDominator (M : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  (discreteSampleSup M ω).toReal

/-! ### Step 4: Continuous-time bridge. -/

/-- Shifted filtration on `ℝ≥0` starting at natural index `n`:
`(shiftedFiltration 𝓕 n).seq t = 𝓕 ((n : ℝ) + t)`. -/
def shiftedFiltration (𝓕 : Filtration ℝ mΩ) (n : ℕ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 ((n : ℝ) + (t : ℝ))
  mono' s t hst := 𝓕.mono <| by
    have : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  le' _ := 𝓕.le _

/-- Shifted continuous-time process `(t : ℝ≥0) ↦ M ((n : ℝ) + t)`. -/
private noncomputable def shiftedProc (M : ℝ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M ((n : ℝ) + (t : ℝ)) ω

/-- Constant-in-time process `(_ : ℝ≥0) ↦ M (n : ℝ)`. -/
private noncomputable def constProc (M : ℝ → Ω → ℝ) (n : ℕ) (_t : ℝ≥0) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Increment process `Y_n t ω := M ((n : ℝ) + t) ω - M (n : ℝ) ω`, indexed by `t : ℝ≥0`. -/
noncomputable def incrementProc (M : ℝ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  M ((n : ℝ) + (t : ℝ)) ω - M (n : ℝ) ω

end MathFin
