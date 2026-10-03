/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
import Tengoku.Formalslt.FormalSLT.AnytimeValid.SubGaussianCS

/-!
# Countable-time confidence sequences

This file lifts the finite-horizon Ville layer from
`Finset.range (n + 1)` to the countable crossing event
`{omega | exists n, a <= M n omega}`.  The proof applies the existing
optional-stopping finite Ville theorem to the increasing finite crossing
events and passes to the countable union by continuity from below.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- Countable-time crossing event for a real-valued process. -/
def atTopCrossingEvent (M : ℕ → Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, a ≤ M n ω}

/-- Finite running-max crossing events exhaust the countable crossing event. -/
theorem finiteRunningMax_event_iUnion_eq_atTopCrossingEvent
    (M : ℕ → Ω → ℝ) (a : ℝ) :
    (⋃ n : ℕ, {ω | a ≤ finiteRunningMax M n ω})
      = atTopCrossingEvent M a := by
  classical
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨n, hn⟩
    dsimp [finiteRunningMax] at hn
    rw [Finset.le_sup'_iff] at hn
    rcases hn with ⟨k, _hk_mem, hk_le⟩
    exact ⟨k, hk_le⟩
  · rintro ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    dsimp [finiteRunningMax]
    exact hn.trans <| Finset.le_sup'
      (f := fun k => M k ω)
      (s := Finset.range (n + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- The finite running-max crossing events are monotone in the horizon. -/
theorem finiteRunningMax_event_mono (M : ℕ → Ω → ℝ) (a : ℝ) :
    Monotone fun n : ℕ => {ω | a ≤ finiteRunningMax M n ω} := by
  classical
  intro n m hnm ω hω
  dsimp [finiteRunningMax] at hω ⊢
  rw [Finset.le_sup'_iff] at hω ⊢
  rcases hω with ⟨k, hk_mem, hk_le⟩
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk_mem
  refine ⟨k, ?_, hk_le⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact hk_mem.trans hnm

/-- Fixed-lambda atTop upper boundary for the centered running mean. -/
def atTopSubGammaUpperFailure {Ω : Type*}
    (X : ℕ → Ω → ℝ) (sigma2 b lam delta : ℝ) : Set Ω :=
  {ω | ∃ n : ℕ, 0 < n ∧
    subGammaCgf sigma2 b lam / lam
      + Real.log (1 / delta) / ((n : ℝ) * lam)
      ≤ runningMean X n ω}

/--
The fixed-lambda running-mean atTop boundary is contained in the fixed
exponential-process crossing event.
-/
theorem atTopSubGammaUpperFailure_subset_exponential_crossing
    {Ω : Type*} {X : ℕ → Ω → ℝ} {sigma2 b lam delta : ℝ}
    (hδ : 0 < delta) (hlam : 0 < lam) :
    atTopSubGammaUpperFailure X sigma2 b lam delta
      ⊆
    atTopCrossingEvent (subGammaExponentialProcess X sigma2 b lam) (1 / delta) := by
  intro ω hω
  rcases hω with ⟨n, hn_pos, hn_boundary⟩
  refine ⟨n, ?_⟩
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hden_pos : 0 < (n : ℝ) * lam := mul_pos (Nat.cast_pos.mpr hn_pos) hlam
  have hmul := mul_le_mul_of_nonneg_left hn_boundary hden_pos.le
  have hlog_le :
      Real.log (1 / delta)
        ≤ lam * runningSum X n ω - (n : ℝ) * subGammaCgf sigma2 b lam := by
    rw [runningMean] at hmul
    field_simp [hn_ne, hlam_ne] at hmul
    nlinarith
  have hdelta_inv_pos : 0 < 1 / delta := one_div_pos.mpr hδ
  rw [← Real.exp_log hdelta_inv_pos]
  exact Real.exp_le_exp.2 hlog_le

/--
The fixed-lambda atTop boundary is not vacuous: for the zero process with
zero variance proxy and confidence level `exp (-1)`, the upper failure event is
empty.
-/
theorem atTopSubGammaUpperFailure_zero_process_empty {lam : ℝ} (hlam : 0 < lam) :
    atTopSubGammaUpperFailure
      (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) 0 0 lam (Real.exp (-1))
      = ∅ := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨n, hn_pos, hn_boundary⟩
    have hn_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hden_pos : 0 < (n : ℝ) * lam := mul_pos hn_cast_pos hlam
    have hlog : Real.log (1 / Real.exp (-1)) = 1 := by
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    have hpos : 0 < Real.log (1 / Real.exp (-1)) / ((n : ℝ) * lam) :=
      div_pos (by rw [hlog]; norm_num) hden_pos
    have hle :
        Real.log (1 / Real.exp (-1)) / ((n : ℝ) * lam) ≤ 0 := by
      simpa [subGammaCgf, runningMean, runningSum] using hn_boundary
    exact False.elim ((not_lt_of_ge hle) hpos)
  · intro hω
    exact False.elim hω

end

end FormalSLT.AnytimeValid
