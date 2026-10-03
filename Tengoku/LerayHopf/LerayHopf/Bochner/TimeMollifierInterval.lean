/-
# LerayHopf.Bochner.TimeMollifierInterval — Stream D / PR-F3 (S1 sub-module 2: interval layer)

**Stream:** D (abstract Bochner–Sobolev-in-time). **Origin:** the S1 wall isolated in
`LerayHopf/Bochner/TimeMollification.lean` (`timeMollification_exists`), decomposed by the
team-lead into bounded sub-modules. This file is the SECOND sub-module — the interval layer —
resting on the now-PROVED whole-line Young bound `timeConvL2_norm_le` of
`LerayHopf/Bochner/TimeConvolution.lean`.

Domain-NEUTRAL and abstract in the Banach space `E` (so it serves both `V` and `V'` of a
Gelfand triple).

## What this file provides (this sub-module)

1. **`timeConvL2_tendsto_self`** — the **ε/3 mollification convergence**
   `‖timeConvL2 ρₙ g − g‖₂ → 0` as the kernel concentrates, for `g : Lp E 2 volume`. Proved
   sorry-free via the *translation-modulus* route (the whole-space spatial model
   `FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`, transported to the time line
   and abstracted in `E`): the mollification defect is bounded by the kernel-weighted average
   of the translation modulus `‖τ_h g − g‖`, which the proved Young bound + continuity of
   `h ↦ τ_h g` at `0` (`continuous_timeTranslateL2`) drive to `0` as the support shrinks. This
   route needs NO pointwise/`Lp` coeFn bridge, so it is genuinely closeable here.

2. `isWeakTimeDerivℝ_smul_cutoff` (B2) — the **cutoff/Leibniz product rule** for whole-line
   Banach-valued weak derivatives. **PROVED sorry-free** (corrected signature: added the
   `LocallyIntegrable u`/`LocallyIntegrable v` Fubini/`integral_add` hypotheses).

3. `timeConvL2_weakDeriv_comm` (WALL A) — the commutation `(ρ ⋆ u)' = ρ ⋆ v` in the **whole-line**
   `IsWeakTimeDerivℝ` sense. **Corrected signature (codex P1):** the global predicate `+`
   `LocallyIntegrable u`/`LocallyIntegrable v` (the box-Fubini soundness hypotheses). The
   soundness-critical commutation identity (shift-substitution + `hwd (ψ(·+s))`) is **PROVED
   unconditionally**; only the standard compact-box L¹ Fubini side-condition is isolated as a
   single non-soundness `ALLOW_SORRY` in the private helper `timeConv_prod_integrable`.

4. `weakTimeDerivℝ_even_reflection` (B1) — even reflection reflects the whole-line weak derivative
   with sign flip, NO Dirac. The no-Dirac identity genuinely requires the Bochner-valued
   1D-Sobolev FTC/continuous-representative (trace at `0`) pillar (the same months-class residual
   as `w1pTime_continuous_in_H`); precise `ALLOW_SORRY` with the corrected blocker analysis.

5. `w1pTime_lineExtension` (WALL B assembly) — the **W1pTime-preserving whole-line extension** of
   a curve on `[0,T]` (even reflection × cutoff). Conclusion uses the **global** `IsWeakTimeDerivℝ`
   (codex P2 / §2a). Blocked transitively on B1's FTC pillar plus the double-endpoint reflection
   `MemLp`/`=ᵐ` bookkeeping; precise `ALLOW_SORRY`. Glue pieces (B2 + `isWeakTimeDerivℝ_comp_clm`)
   are PROVED.

## Assumptions

No new `axiom`/`opaque`/`constant`. Theorem 1 and B2 are fully proved; WALL A's commutation
identity is proved (only its Fubini side-condition is isolated). The genuinely-missing pillar is
the Bochner 1D-Sobolev FTC/trace (B1 no-Dirac), which transitively blocks the assembly. Each gap
carries a precise same-line `-- ALLOW_SORRY: <blocker>`; no statement is weakened and no axiom is
added.
-/

import Tengoku.LerayHopf.LerayHopf.Bochner.TimeConvolution
import Tengoku.LerayHopf.LerayHopf.Bochner.TimeSobolev
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq
import Tengoku.Data.Real.Sign

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology Metric
open scoped ENNReal

section IntervalLayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The translation-modulus bound (time-line port of the FK spatial model)

`timeConvL2 ρ g − g = ∫ h, ρ h • (τ_h g − g)` for a unit-mass kernel, so by `‖∫ F‖ ≤ ∫ ‖F‖`
the mollification defect is controlled by the kernel-weighted integral of the translation
modulus `‖τ_h g − g‖`. This is the abstract-`E` time-line transport of
`FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`. -/

/-- The defect `timeConvL2 ρ g − g` equals the single Bochner integral
`∫ h, ρ h • (τ_h g − g)` (using `∫ ρ = 1` to write `g = ∫ h, ρ h • g`). -/
theorem timeConvL2_sub_eq_integral {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    timeConvL2 ρ g - g
      = ∫ h : ℝ, ρ h • (timeTranslateL2 h g - g) ∂(volume : Measure ℝ) := by
  have hI1 : Integrable (fun h : ℝ => ρ h • timeTranslateL2 h g) (volume : Measure ℝ) :=
    integrable_timeMollifier_smul_translate hρ g
  have hηL1 : Integrable ρ (volume : Measure ℝ) :=
    hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport
  have hI2 : Integrable (fun h : ℝ => ρ h • g) (volume : Measure ℝ) := hηL1.smul_const g
  have hg_int : (∫ h : ℝ, ρ h • g ∂(volume : Measure ℝ)) = g := by
    rw [integral_smul_const, hρ.mass_one, one_smul]
  have e1 : timeConvL2 ρ g - g
      = (∫ h : ℝ, ρ h • timeTranslateL2 h g ∂(volume : Measure ℝ))
        - ∫ h : ℝ, ρ h • g ∂(volume : Measure ℝ) := by
    rw [timeConvL2, hg_int]
  rw [e1, ← integral_sub hI1 hI2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [smul_sub]

/-- **Translation-modulus bound** (time-line, `E`-abstract):
`‖timeConvL2 ρ g − g‖ ≤ ∫ h, ρ h • ‖τ_h g − g‖`. Direct port of
`FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`. -/
theorem timeConvL2_sub_le_translation_modulus {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeConvL2 ρ g - g‖
      ≤ ∫ h : ℝ, ρ h • ‖timeTranslateL2 h g - g‖ ∂(volume : Measure ℝ) := by
  rw [timeConvL2_sub_eq_integral hρ g]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only []
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg h), smul_eq_mul]

/-! ### The translation modulus and its continuity at `0`

`M g h := ‖τ_h g − g‖` is continuous (translation `h ↦ τ_h g` is continuous into `L²`,
`continuous_timeTranslateL2`, and the norm is continuous) and vanishes at `h = 0`
(`τ_0 g = g`). These two facts drive the kernel-weighted average to `0` as the support of `ρ`
concentrates at `0`. -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The translation modulus `h ↦ ‖τ_h g − g‖` is continuous. -/
theorem continuous_translationModulus (g : Lp E 2 (volume : Measure ℝ)) :
    Continuous (fun h : ℝ => ‖timeTranslateL2 h g - g‖) :=
  ((continuous_timeTranslateL2 g).sub continuous_const).norm

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The translation modulus vanishes at `h = 0`: `τ_0 g = g`. -/
theorem translationModulus_zero (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeTranslateL2 (0 : ℝ) g - g‖ = 0 := by
  have h0 : timeTranslateL2 (0 : ℝ) g = g := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving g _).trans ?_
    filter_upwards with x
    simp
  rw [h0, sub_self, norm_zero]

/-! ### The mollification convergence (Theorem 1)

For a bump sequence `φ` with `(φ n).rOut → 0`, the normalized kernels `ρ n := (φ n).normed`
are time-mollifiers (`ContDiffBump.isTimeMollifier`) whose support is `ball 0 (φ n).rOut`. The
modulus bound gives `‖timeConvL2 (ρ n) g − g‖ ≤ ∫ h, ρ n h • ‖τ_h g − g‖`. Since `∫ ρ n = 1`
and `‖τ_h g − g‖ ≤ εₙ` on the shrinking support (continuity at `0`, value `0`), the RHS → 0. -/

/-- **Mollification convergence (Theorem 1, sorry-free).**

`‖timeConvL2 ((φ n).normed volume) g − g‖ → 0` as the bump radius `(φ n).rOut → 0`, for any
`g : L²(ℝ; E)`. This is the genuinely-new assembled `eLpNorm`-mollification theorem the S1
pillar needed, proved here via the translation-modulus route (no pointwise/`Lp` coeFn bridge):

* `timeConvL2_sub_le_translation_modulus` bounds the defect by `∫ h, ρ n h • ‖τ_h g − g‖`;
* on `supp (ρ n) = ball 0 (φ n).rOut`, continuity of the modulus at `0` (value `0`,
  `translationModulus_zero`) makes `‖τ_h g − g‖ ≤ ε` for `n` large;
* `∫ ρ n = 1` (`mass_one`) collapses `∫ ρ n • ε = ε`, so the defect is `≤ ε` eventually. -/
theorem timeConvL2_tendsto_self (g : Lp E 2 (volume : Measure ℝ))
    (φ : ℕ → ContDiffBump (0 : ℝ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ‖timeConvL2 ((φ n).normed (volume : Measure ℝ)) g - g‖) atTop (𝓝 0) := by
  set M : ℝ → ℝ := fun h => ‖timeTranslateL2 h g - g‖ with hM
  have hMcont : Continuous M := continuous_translationModulus g
  have hM0 : M 0 = 0 := translationModulus_zero g
  have hMnonneg : ∀ h, 0 ≤ M h := fun h => norm_nonneg _
  -- It suffices to squeeze the defect between `0` and a sequence `→ 0`.
  -- Bound: `defect n ≤ ∫ h, ρ n h • M h`, and that integral `≤ εₙ` where `εₙ → 0`.
  -- We prove the `ε`-`δ` form directly.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- By continuity of `M` at `0` (with `M 0 = 0`), pick `δ` so `|h| < δ → M h < ε/2`.
  -- The `ε/2` threshold yields `∫ ρ • M ≤ ε/2 < ε` (the integral inequality is non-strict).
  have hε2 : 0 < ε / 2 := by linarith
  have hcont0 : Tendsto M (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have := hMcont.tendsto (0 : ℝ); rwa [hM0] at this
  have hδ : ∀ᶠ h in 𝓝 (0 : ℝ), M h < ε / 2 := hcont0 (Iio_mem_nhds hε2)
  rw [Metric.eventually_nhds_iff] at hδ
  obtain ⟨δ, hδpos, hδlt⟩ := hδ
  -- Eventually `(φ n).rOut < δ`, so the kernel support sits in `ball 0 δ`.
  have hrOut : ∀ᶠ n in atTop, (φ n).rOut < δ := hφ (Iio_mem_nhds hδpos)
  rw [Filter.eventually_atTop] at hrOut
  obtain ⟨N, hN⟩ := hrOut
  refine ⟨N, fun n hnN => ?_⟩
  have hn : (φ n).rOut < δ := hN n hnN
  set ρ : ℝ → ℝ := (φ n).normed (volume : Measure ℝ) with hρdef
  have hρmoll : IsTimeMollifier ρ := ContDiffBump.isTimeMollifier (φ n)
  -- `dist (defect n) 0 = defect n` (nonneg); bound it by `∫ ρ • M ≤ ε`.
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt (timeConvL2_sub_le_translation_modulus hρmoll g) ?_
  -- `∫ h, ρ h • M h ≤ ∫ h, ρ h • ε = ε` (using `M h ≤ ε` on the support, `ρ ≥ 0`, `∫ ρ = 1`).
  have hρL1 : Integrable ρ (volume : Measure ℝ) :=
    hρmoll.continuous.integrable_of_hasCompactSupport hρmoll.hasCompactSupport
  have hbound : ∀ h, ρ h • M h ≤ ρ h • (ε / 2) := by
    intro h
    rcases eq_or_ne (ρ h) 0 with hzero | hne
    · simp [hzero]
    · -- `ρ h ≠ 0 ⇒ h ∈ support ρ = ball 0 rOut ⊆ ball 0 δ ⇒ M h < ε`.
      have hmem : h ∈ Function.support ρ := by simpa using hne
      rw [hρdef, (φ n).support_normed_eq] at hmem
      have hball : h ∈ ball (0 : ℝ) δ := ball_subset_ball hn.le hmem
      have : M h < ε / 2 := hδlt (by simpa [Real.dist_eq, dist_zero_right] using hball)
      have hρpos : 0 ≤ ρ h := hρmoll.nonneg h
      simp only [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left this.le hρpos
  have hint_le : (∫ h : ℝ, ρ h • M h ∂(volume : Measure ℝ))
      ≤ ∫ h : ℝ, ρ h • (ε / 2) ∂(volume : Measure ℝ) := by
    refine integral_mono ?_ ?_ hbound
    · -- `ρ • M` integrable: `M` continuous so the `smul` is continuous w/ compact support `⊆ supp ρ`.
      have hcont : Continuous (fun h : ℝ => ρ h • M h) := hρmoll.continuous.smul hMcont
      refine hcont.integrable_of_hasCompactSupport ?_
      apply HasCompactSupport.intro hρmoll.hasCompactSupport.isCompact (fun h hh => ?_)
      have : ρ h = 0 := by
        by_contra hh'; exact hh (subset_tsupport ρ (by simpa using hh'))
      simp [this]
    · simpa only [smul_eq_mul] using hρL1.mul_const (ε / 2)
  calc (∫ h : ℝ, ρ h • M h ∂(volume : Measure ℝ))
      ≤ ∫ h : ℝ, ρ h • (ε / 2) ∂(volume : Measure ℝ) := hint_le
    _ = ε / 2 := by rw [integral_smul_const, hρmoll.mass_one, one_smul]
    _ < ε := by linarith

end IntervalLayer

/-! ### Pointwise time-convolution of a Banach-valued curve

For Theorem 3 (the weak-derivative commutation) the convolution must act on a *pointwise*
curve `u : ℝ → X`, not an `Lp` element: `(ρ ⋆ₜ u)(x) = ∫ s, ρ s • u (x − s)`. This is mathlib's
`convolution f g (lsmul ℝ ℝ) volume` with the scalar kernel on the left. -/

section WeakDerivComm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

open scoped Convolution

end WeakDerivComm

/-! ### WALL B sub-lemma scaffolds (s1-walls-design.md §2)

The bounded foundational layer that WALL B's assembly (`w1pTime_lineExtension`) rests on.
Each sub-lemma carries a precise statement from the design note and a same-line `ALLOW_SORRY`
tagged with the note's §-reference and prover tier. Proof bodies are deferred to tiered provers.

Sub-lemma order per recommended dispatch (§3 of design note):
- B0 / §2a: the `IsWeakTimeDerivℝ` conclusion for `w1pTime_lineExtension` (signature update).
- B1 / §2b: even-reflection reflects the weak derivative with sign flip (no Dirac at 0).
- B2 / §2c: cutoff (Leibniz) product rule for whole-line weak derivatives.
- B2e-global / §2e: `isWeakTimeDerivℝ_comp_clm` is in `TimeSobolev.lean`.
- B3 / §2d: assembly: ūV := χ • (reflection of uV), all three properties + weak-deriv identity.
-/

section LineExtension

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Sub-lemma B2 — cutoff (Leibniz) product rule for whole-line Banach-valued weak derivatives.**

For a globally `C¹` cutoff `χ : ℝ → ℝ` (not assumed compactly supported), curves
`u v : ℝ → X` that are **locally integrable** (`hu`, `hv` — the genuine soundness/Fubini
hypotheses: without local integrability the Bochner integrals in `IsWeakTimeDerivℝ` are junk
and `integral_add` cannot split), and `IsWeakTimeDerivℝ u v`,

  `IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t)`.

**Corrected signature.** The added `LocallyIntegrable u`, `LocallyIntegrable v` hypotheses are
the minimal honest domain restriction making the `integral_add` split sound; they are available
downstream (the `W1pTime` `MemLp` fields give local integrability after even reflection). No
mathematical content is weakened — the Leibniz identity is exactly as before.

The proof transfers `χ` onto the test function `ψ`: the product `χ · ψ` is `C¹` and compactly
supported (compact support of `ψ` wins), `deriv (χ · ψ) = χ' · ψ + χ · ψ'`, so
`∫ (χψ)'• u = ∫ (χ'ψ)•u + ∫ (χψ')•u`. Apply `hwd (χ · ψ)` on the left, regroup; each summand is
`(continuous compactly-supported scalar) • (locally integrable)`, hence integrable
(`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`). -/
theorem isWeakTimeDerivℝ_smul_cutoff (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (u v : ℝ → X) (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hv : LocallyIntegrable v (volume : Measure ℝ)) (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t) := by
  intro ψ hψcs hψC1
  -- The transferred test function `φ := χ · ψ` is `C¹` and compactly supported.
  set φ : ℝ → ℝ := fun t => χ t * ψ t with hφdef
  have hχcont : Continuous χ := hχ.continuous
  have hψcont : Continuous ψ := hψC1.continuous
  have hχ'cont : Continuous (deriv χ) := hχ.continuous_deriv_one
  have hψ'cont : Continuous (deriv ψ) := hψC1.continuous_deriv_one
  have hφC1 : ContDiff ℝ 1 φ := hχ.mul hψC1
  have hφcs : HasCompactSupport φ := hψcs.mul_left
  -- Leibniz: `deriv φ t = deriv χ t * ψ t + χ t * deriv ψ t`.
  have hderivφ : ∀ t, deriv φ t = deriv χ t * ψ t + χ t * deriv ψ t := by
    intro t
    have hχd : DifferentiableAt ℝ χ t := (hχ.differentiable one_ne_zero).differentiableAt
    have hψd : DifferentiableAt ℝ ψ t := (hψC1.differentiable one_ne_zero).differentiableAt
    have hpi : φ = χ * ψ := by funext s; rfl
    rw [hpi]; exact deriv_mul hχd hψd
  -- `hwd φ`: `∫ deriv φ • u = - ∫ φ • v`.
  have hwφ := hwd φ hφcs hφC1
  -- Integrability of the three summands: (compactly-supported continuous scalar) • (loc-integrable).
  have hcs_χ'ψ : HasCompactSupport (fun t => deriv χ t * ψ t) := hψcs.mul_left
  have hcs_χψ' : HasCompactSupport (fun t => χ t * deriv ψ t) :=
    (HasCompactSupport.deriv hψcs).mul_left
  have hint_χ'ψ : Integrable (fun t => (deriv χ t * ψ t) • u t) (volume : Measure ℝ) :=
    hu.integrable_smul_left_of_hasCompactSupport (hχ'cont.mul hψcont) hcs_χ'ψ
  have hint_χψ' : Integrable (fun t => (χ t * deriv ψ t) • u t) (volume : Measure ℝ) :=
    hu.integrable_smul_left_of_hasCompactSupport (hχcont.mul hψ'cont) hcs_χψ'
  -- Rewrite `∫ deriv φ • u` using Leibniz and split via `integral_add`.
  have hsplit : (∫ t, deriv φ t • u t)
      = (∫ t, (deriv χ t * ψ t) • u t) + ∫ t, (χ t * deriv ψ t) • u t := by
    rw [← integral_add hint_χ'ψ hint_χψ']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hderivφ t, add_smul]
  -- The goal LHS `∫ deriv ψ • (χ • u) = ∫ (χ ψ') • u`.
  have hLHS : (∫ t, deriv ψ t • (χ t • u t)) = ∫ t, (χ t * deriv ψ t) • u t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [smul_smul, mul_comm (deriv ψ t) (χ t)]
  -- The goal RHS `∫ ψ • (χ•v + χ'•u) = ∫ φ•v + ∫ (χ'ψ)•u`.
  have hint_φv : Integrable (fun t => φ t • v t) (volume : Measure ℝ) :=
    hv.integrable_smul_left_of_hasCompactSupport hφC1.continuous hφcs
  have hRHS : (∫ t, ψ t • (χ t • v t + deriv χ t • u t))
      = (∫ t, φ t • v t) + ∫ t, (deriv χ t * ψ t) • u t := by
    rw [← integral_add hint_φv hint_χ'ψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hφdef, smul_add, smul_smul, mul_comm (ψ t) (deriv χ t), mul_comm (ψ t) (χ t)]
  -- Combine: from `hwφ` (`∫ φ' • u = -∫ φ•v`), `hsplit` gives the relation between the pieces.
  rw [hLHS, hRHS]
  -- `hsplit` + `hwφ`: `A + B = -C` where A = ∫(χ'ψ)•u, B = ∫(χψ')•u, C = ∫φ•v.
  -- Goal: `B = -(C + A)`. Additive-group algebra.
  rw [hsplit] at hwφ
  refine eq_neg_of_add_eq_zero_left ?_
  -- `B + (C + A) = 0` follows from `A + B = -C`.
  have : (∫ t, (χ t * deriv ψ t) • u t) + ((∫ t, φ t • v t) + ∫ t, (deriv χ t * ψ t) • u t)
      = ((∫ t, (deriv χ t * ψ t) • u t) + ∫ t, (χ t * deriv ψ t) • u t)
        + ∫ t, φ t • v t := by abel
  rw [this, hwφ, neg_add_cancel]

end LineExtension

end LerayHopf.Bochner
