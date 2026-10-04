/-
# LerayHopf.Bochner.TimeConvolution — Stream D / PR-F3 (S1 sub-module 1: whole-line Young)

**Stream:** D (abstract Bochner–Sobolev-in-time). **Origin:** the SPIKE-1 S1 wall isolated in
`LerayHopf/Bochner/TimeMollification.lean` (`timeMollification_exists`). The team-lead sequenced
the S1 build into bounded sub-modules; THIS file is the FIRST one: the whole-line `eLpNorm`
Young bound for a Banach-valued time-convolution, plus the documented interval-boundary design.

This file is domain-NEUTRAL and abstract in the Banach space `E`, so it applies to both the
regularity space `V` and the dual `V'` of a Gelfand triple (the two convergences
`conv_uV : L²(0,T;V)` and `conv_uV' : L²(0,T;V')` reuse the same bound).

## What this file provides (this sub-module)

- `IsTimeMollifier ρ` — the abstract mollifier bundle: `ρ : ℝ → ℝ` continuous, nonnegative,
  with compact support and unit mass `∫ ρ = 1`. `ContDiffBump.normed volume` is the canonical
  instance (continuous, nonneg, compact support, `integral_normed = 1`); keeping the predicate
  abstract makes the bound reusable and avoids committing to a specific bump at this layer.
- `timeTranslateL2 h g` — the time-translation `τ_h g = g(· + h)` on the Bochner space
  `Lp E 2 (volume : Measure ℝ)`, realized as `Lp.compMeasurePreserving` of the
  measure-preserving shift (an isometry).
- `timeConvL2 ρ g` — the time-convolution `ρ ⋆ₜ g` realized as a genuine element of
  `Lp E 2 (volume : Measure ℝ)`, the Bochner integral `∫ h, ρ h • τ_h g ∂volume` valued in
  that Banach space (no `MemLp` side-condition: the integrand is Bochner integrable because it
  is continuous with compact support — the mollifier kills the tails).
- **`timeConvL2_norm_le`** — the **`eLpNorm` Young bound** at the `Lp`-element level:
  `‖ρ ⋆ₜ g‖ ≤ ‖g‖`. This is the entire norm content of Young's inequality for a unit-mass
  kernel, via `‖∫ F‖ ≤ ∫ ‖F‖` (`norm_integral_le_integral_norm`) + translation isometry +
  `∫ ρ = 1`. **Proved sorry-free.** (Mirrors `FrechetKolmogorov.convL2_norm_le`, the whole-space
  spatial model, transported to the time line and abstracted in `E`.)

## Interval-boundary design (the crux — documented, scaffolded for the next sub-module)

The whole-line bound above is clean precisely because time-translation preserves `volume` on
`ℝ`. The genuine S1 wall is the INTERVAL `[0,T]`: a `W1pTime` curve lives on `[0,T]`, and
time-translation does NOT preserve `[0,T]`; naive zero-extension off `[0,T]` injects a boundary
jump that the weak `V'`-derivative sees (a Dirac term at `0` and `T`), breaking the commutation
`(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'`. The chosen sound approach and the lemma signatures the next sub-module
must fill are written out as a DESIGN NOTE in the closing `section`-comment of this file (prose,
not `sorry`-bearing declarations — they belong to the next sub-module's file, keeping THIS file
fully `sorry`-free).

## Assumptions

No new `axiom`/`opaque`/`constant`, and **zero `sorry`**. The whole-line Young bound
(`timeConvL2_norm_le`) and all its supporting lemmas are fully proved. The interval-boundary
approach is a documented design note only; nothing is weakened and no axiom is introduced.
-/

import Tengoku.Analysis.Calculus.BumpFunction.Normed
import Tengoku.Analysis.Calculus.BumpFunction.FiniteDimension
import Tengoku.MeasureTheory.Function.LpSpace.Basic
import Tengoku.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Tengoku.MeasureTheory.Integral.Bochner.Basic
import Tengoku.MeasureTheory.Integral.CompactlySupported

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Abstract mollifier bundle

`IsTimeMollifier ρ` packages exactly the four properties of a normalized mollifier that the
Young bound consumes. `ContDiffBump.normed volume` satisfies all four. -/

/-- A **normalized time mollifier**: a continuous, nonnegative, compactly-supported scalar
kernel on the line with unit mass. This is precisely what `ContDiffBump.normed volume` provides
(`continuous_normed`, `nonneg_normed`, `hasCompactSupport_normed`, `integral_normed = 1`), kept
abstract so the Young bound applies to any such kernel. -/
structure IsTimeMollifier (ρ : ℝ → ℝ) : Prop where
  /-- Continuity of the kernel. -/
  continuous : Continuous ρ
  /-- Nonnegativity. -/
  nonneg : ∀ x, 0 ≤ ρ x
  /-- Compact support (so the convolution integrand is integrable, tails killed). -/
  hasCompactSupport : HasCompactSupport ρ
  /-- Unit mass `∫ ρ = 1` (the Young constant `‖ρ‖₁ = 1`). -/
  mass_one : ∫ x, ρ x = 1

/-- `ContDiffBump.normed volume` is a normalized time mollifier. -/
theorem ContDiffBump.isTimeMollifier {c : ℝ} (φ : ContDiffBump c) :
    IsTimeMollifier (φ.normed (volume : Measure ℝ)) where
  continuous := φ.continuous_normed
  nonneg := fun x => φ.nonneg_normed x
  hasCompactSupport := φ.hasCompactSupport_normed
  mass_one := φ.integral_normed

section Young

-- `[CompleteSpace E]` is required: the Bochner convolution API (`timeConvL2`,
-- `timeConvL2_norm_le`, etc.) is only semantically sound for complete spaces — without
-- completeness the Bochner integral can collapse to a junk fallback while the Young
-- norm bound still typechecks. All intended GelfandTriple consumers already provide
-- `CompleteSpace`. Lemmas that do NOT use completeness carry `omit [CompleteSpace E]`.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Time-translation on `L²(ℝ; E)`**: `τ_h g = g(· + h)`, realized as
`Lp.compMeasurePreserving` of the measure-preserving shift `(· + h)`. It is a linear isometry
(`Lp.norm_compMeasurePreserving`), the time-line mirror of `FrechetKolmogorov.translate_L2VF`. -/
noncomputable def timeTranslateL2 (h : ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure ℝ) h) g

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Translation is an isometry on `L²(ℝ;E)`: `‖τ_h g‖ = ‖g‖`. -/
theorem timeTranslateL2_norm (h : ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeTranslateL2 h g‖ = ‖g‖ := by
  rw [timeTranslateL2, Lp.norm_compMeasurePreserving]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- `h ↦ τ_h g` is continuous from `ℝ` into `L²(ℝ;E)` (mathlib's translation continuity in
`Lp`, `Continuous.compMeasurePreservingLp`). Needed for strong measurability / integrability of
the convolution integrand. -/
theorem continuous_timeTranslateL2 (g : Lp E 2 (volume : Measure ℝ)) :
    Continuous (fun h : ℝ => timeTranslateL2 h g) := by
  set sh : ℝ → C(ℝ, ℝ) := fun h => ⟨(· + h), continuous_id.add continuous_const⟩ with hsh
  have hgm : ∀ h : ℝ, MeasurePreserving (sh h) (volume : Measure ℝ) volume :=
    fun h => measurePreserving_add_right (volume : Measure ℝ) h
  have hshcont : Continuous sh := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : ℝ × ℝ => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  exact Continuous.compMeasurePreservingLp (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (E := E) (p := 2)
    (f := fun _ : ℝ => g) (g := sh) continuous_const hshcont hgm (by simp)

/-- **Time-convolution as an `L²(ℝ;E)`-element**: `ρ ⋆ₜ g := ∫ h, ρ h • τ_h g ∂volume`, the
Bochner integral of the `Lp`-valued kernel-weighted-translate family. No `MemLp` side-condition
is needed: the integrand is Bochner integrable (continuous with compact support, since `ρ` has
compact support). Time-line mirror of `FrechetKolmogorov.convL2`. -/
noncomputable def timeConvL2 (ρ : ℝ → ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    Lp E 2 (volume : Measure ℝ) :=
  ∫ h : ℝ, ρ h • timeTranslateL2 h g ∂(volume : Measure ℝ)

omit [CompleteSpace E] in
/-- The kernel-weighted-translate family `h ↦ ρ h • τ_h g` is Bochner integrable as an
`L²(ℝ;E)`-valued map: continuous (so strongly measurable), with compact support
(`tsupport ρ`, since outside it the scalar factor vanishes). -/
theorem integrable_timeMollifier_smul_translate {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    Integrable (fun h : ℝ => ρ h • timeTranslateL2 h g) (volume : Measure ℝ) := by
  have hcont : Continuous (fun h : ℝ => ρ h • timeTranslateL2 h g) :=
    hρ.continuous.smul (continuous_timeTranslateL2 g)
  have hsupp : HasCompactSupport (fun h : ℝ => ρ h • timeTranslateL2 h g) := by
    apply HasCompactSupport.intro hρ.hasCompactSupport.isCompact (fun h hh => ?_)
    have : ρ h = 0 := by
      by_contra hne
      exact hh (subset_tsupport ρ (by simpa using hne))
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hsupp

omit [CompleteSpace E] in
/-- `‖ρ h • τ_h g‖ = ρ h · ‖g‖` (using `hρ.nonneg` so `|ρ h| = ρ h`, and translation isometry). -/
theorem norm_timeMollifier_smul_translate {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) (h : ℝ) :
    ‖ρ h • timeTranslateL2 h g‖ = ρ h * ‖g‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg h), timeTranslateL2_norm]

-- `CompleteSpace E` is a *semantic* guard here, not a proof dependency: without it the
-- Bochner integral defining `timeConvL2` collapses to junk-`0`, making the bound vacuous.
-- We `omit` the auto-included section variable (whose only effect would be an
-- `unusedSectionVars` warning) and re-add it as an explicit binder so it stays in the
-- public type in the same position, without a linter suppression.
omit [CompleteSpace E] in
/-- **The whole-line `eLpNorm` Young bound (PROVED, sorry-free).**

`‖ρ ⋆ₜ g‖ ≤ ‖g‖` for a unit-mass mollifier `ρ`. This is the entire norm content of Young's
convolution inequality `‖ρ ⋆ g‖₂ ≤ ‖ρ‖₁ · ‖g‖₂` with `‖ρ‖₁ = ∫ ρ = 1`: it follows from
`‖∫ F‖ ≤ ∫ ‖F‖` in the Banach space `L²(ℝ;E)` (`norm_integral_le_integral_norm`),
`‖ρ h • τ_h g‖ = ρ h · ‖g‖` (translation isometry + nonneg kernel), and `∫ ρ = 1`.

This is the time-line, `E`-abstract transport of `FrechetKolmogorov.convL2_norm_le` (the
whole-space spatial model). It is the foundational reusable piece of the S1 build: the same
bound serves the `L²(0,T;V)` and `L²(0,T;V')` convergences once the interval layer lands. -/
theorem timeConvL2_norm_le [CompleteSpace E] {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeConvL2 ρ g‖ ≤ ‖g‖ := by
  have hle : ‖timeConvL2 ρ g‖
      ≤ ∫ h : ℝ, ‖ρ h • timeTranslateL2 h g‖ ∂(volume : Measure ℝ) :=
    norm_integral_le_integral_norm _
  have hcongr : (∫ h : ℝ, ‖ρ h • timeTranslateL2 h g‖ ∂(volume : Measure ℝ))
      = ∫ h : ℝ, ρ h * ‖g‖ ∂(volume : Measure ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    exact norm_timeMollifier_smul_translate hρ g h
  rw [hcongr, integral_mul_const, hρ.mass_one, one_mul] at hle
  exact hle

end Young

/-! ### Interval-boundary design (scaffold for the next S1 sub-module)

**The wall.** A `W1pTime GT 2 2 T uV` curve `uV : ℝ → V` is controlled only on `[0,T]`
(`MemLp` on `volume.restrict (Icc 0 T)`), with a weak `V'`-derivative `u'` likewise on `[0,T]`.
The whole-line Young bound above needs a curve on all of `ℝ`. Time-translation does not preserve
`[0,T]`, and zero-extension off `[0,T]` is UNSOUND for the derivative: the extended curve jumps
at the endpoints, so its weak `V'`-derivative acquires boundary Dirac terms and the commutation
`(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'` FAILS.

**Chosen sound approach: a `W1pTime`-preserving whole-line extension.** Extend `uV` to
`ūV : ℝ → V` on all of `ℝ` so that (i) `ūV = uV` a.e. on `[0,T]`, (ii) `ūV ∈ L²(ℝ;V)`, and
(iii) the `V'`-image `t ↦ ι(ūV t)` has a whole-line weak `V'`-derivative `ū'` with
`ū' = u'` a.e. on `[0,T]` and `ū' ∈ L²(ℝ;V')`. The standard construction is a **Sobolev
reflection/extension** (even reflection at each endpoint, multiplied by a fixed cutoff to keep
compact support), which is bounded `L²(ℝ;V) ∩ {u' ∈ L²(ℝ;V')}` and matches the trace so no
boundary jump is created — the weak derivative of the reflected extension is the reflection of
the derivative (no Dirac term). Then mollify the EXTENSION on the whole line with the bound
above, and RESTRICT the result back to `[0,T]`: on `[0,T]` the restriction sees only the genuine
curve, and the convergence transfers because `eLpNorm` over `Icc 0 T ⊆ ℝ` is monotone under
`eLpNorm` over `ℝ` (`eLpNorm_mono_measure` / `restrict_le_self`).

The lemma signatures the next sub-module must build and discharge (in its OWN file, so this
file stays `sorry`-free):

- `w1pTime_lineExtension` — the extension `ūV` with the three properties above;
- `eLpNorm_restrict_le_line` — convergence transfer `[0,T] ⊆ ℝ` (a one-line `eLpNorm_mono_measure`);
- `timeConvL2_tendsto_self` — the `eLpNorm`-mollification convergence `‖ρᵋ ⋆ₜ g − g‖₂ → 0` on the
  whole line (ε/3: continuous-dense `MemLp.exists_boundedContinuous_eLpNorm_sub_le` + the Young
  bound above + `ContDiffBump.convolution_tendsto_right` pointwise; the genuinely-new assembled
  theorem, but now resting on the proved Young bound);
- `timeConvL2_weakDeriv_comm` — the commutation `(ρᵋ ⋆ₜ ιu)' = ρᵋ ⋆ₜ u'` in the
  `IsWeakTimeDeriv` sense, via `isWeakTimeDeriv_comp_clm` / `hToVprimeCLM` (convolution is a
  continuous-linear time operation).

These are stated in `TimeMollification.lean`'s eventual constructor, not here; this file's
contract is the whole-line Young bound, which is proved. The design note above fixes the
interval approach so the next sub-module does not re-litigate soundness. -/

end LerayHopf.Bochner
