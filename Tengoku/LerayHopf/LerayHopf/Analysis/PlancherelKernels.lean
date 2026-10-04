import Tengoku.LerayHopf.LerayHopf.R3.Domain
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

/-!
# PlancherelKernels — shared gradient–Fourier Plancherel kernels (issue #111 PR-2)

**File:** `LerayHopf/Analysis/PlancherelKernels.lean`

## What this file is

Four call sites in the `R3` lane build the gradient–Fourier Plancherel control
`∫ ‖fderiv ℝ φ x‖² dx ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖² dξ` for a complex Schwartz function `φ`, the
analytic heart of the `H¹ ↪ L⁶` GNS embedding, and the quantitative `L²∩L⁶ ↪ L³`
interpolation it feeds into `convFormH1`'s trilinear bound. Two of those call sites
(`R3/SobolevEmbedding.lean`, `R3/EnergyClassConvection.lean`) had it as `private` — so a
third (`R3/GalerkinTrilinearBound.lean`) re-derived the whole chain byte-for-byte as "Fresh
copy" declarations (the file's own header flagged this duplication as risk R8). This file
extracts the chain once, as PUBLIC lemmas, so it can actually be shared. It is generic
multilinear/Fourier-analytic infrastructure over `Domain3 = EuclideanSpace ℝ (Fin 3)` — it
does not depend on anything Galerkin/NS-specific, hence lives under `LerayHopf.Analysis`
rather than `LerayHopf.R3`.

## The Plancherel-kernel quartet (+ 3 more)

- `opNorm_le_sqrt_sum_sq` — the operator norm of a real-linear functional `L : Domain3 →L[ℝ] ℂ`
  is bounded by the Euclidean (Hilbert–Schmidt) norm `√(∑ᵢ ‖L (bᵢ)‖²)` of its gradient
  covector, for any orthonormal basis `b` (Cauchy–Schwarz; the `≤` direction — the reverse
  equality is FALSE for ℂ-codomain).
- `normSq_toLp_two` — `‖g.toLp 2‖² = ∫ ‖g ξ‖²` for Schwartz `g` (via `inner_toL2_toL2_eq`).
- `normSq_lineDeriv_toLp` — per-direction Schwartz Plancherel:
  `‖(∂_{m}φ).toLp 2‖² = ∫ (2π)² ⟨ξ,m⟩² ‖𝓕 φ ξ‖²` (via `fourier_lineDerivOp_eq` + Plancherel).
- `integral_normSq_fderiv_le` — integrate the HS bound and sum over the standard basis
  (`∑ᵢ ⟨ξ,eᵢ⟩² = ‖ξ‖²`) to get the displayed inequality.
- `fderiv_apply_single_eq_lineDeriv` — `fderiv φ x (eᵢ) = (∂_{eᵢ}φ) x` for a complex Schwartz
  function (the `EuclideanSpace.single`/`lineDerivOpCLM` presentation, as consumed by the
  energy-class trilinear bound rather than the `∂_{m}`/`⟪,⟫` presentation above — same content,
  different index bookkeeping).
- `eLpNorm_fderiv_le_sum_lineDeriv` — `eLpNorm (fderiv φ) 2 ≤ ∑ᵢ eLpNorm (∂_{eᵢ}φ) 2`, the
  triangle-inequality corollary of `opNorm_le_sqrt_sum_sq` used to bound the full gradient by
  its three coordinate directional derivatives.
- `eLpNorm_three_le_interp` — quantitative `L²∩L⁶ ↪ L³` interpolation:
  `eLpNorm f 3 ≤ (eLpNorm f 2)^{1/2} · (eLpNorm f 6)^{1/2}` (Hölder `1/6+1/2=2/3` on `f*f`).
  Fully generic over `{F} [NormedAddCommGroup F]`; no Schwartz/Fourier dependence.

## Misc L² bridge (item (e) fold-in)

- `eLpNorm_two_eq_ofReal_sqrt` — for an a.e.-strongly-measurable `β`-valued curve `h : ℝ → β`
  with integrable pointwise squared norm, `eLpNorm h 2 μ = ENNReal.ofReal (√(∫ ‖h t‖² dμ))`.
  Fully generic over `{β} [NormedAddCommGroup β] {μ : Measure ℝ}`; unrelated to the Fourier
  kernels above except in being another small generic `eLpNorm`-unfolding fact that was
  privately duplicated (`R3/AubinLionsLimitPassage.lean`, `Torus/AubinLionsAssembly.lean`).

## Mathlib declarations consumed

- `SchwartzMap.inner_toL2_toL2_eq`, `SchwartzMap.norm_fourier_toL2_eq`,
  `SchwartzMap.fourier_lineDerivOp_eq`, `SchwartzMap.smulLeftCLM_apply_apply`
  (`Analysis/Distribution/SchwartzSpace/{Basic,Fourier}.lean`).
- `OrthonormalBasis.sum_repr'`, `OrthonormalBasis.sum_sq_norm_inner_right`, `stdOrthonormalBasis`,
  `EuclideanSpace.basisFun`, `EuclideanSpace.single` (`Analysis/InnerProductSpace/PiL2.lean`).
- `ENNReal.HolderTriple`, `Real.HolderTriple`, `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`
  (`MeasureTheory/Function/Holder.lean`).
- `memLp_two_iff_integrable_sq_norm`, `L2.integrable_inner`, `eLpNorm_norm_rpow`
  (`MeasureTheory/Function/L2Space.lean`).
-/

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

namespace LerayHopf.PlancherelKernels

/-! ### The gradient–Fourier Plancherel quartet -/

open FourierTransform
open scoped Real LineDeriv RealInnerProductSpace FourierTransform

/-- **Plancherel kernel 1.** Operator norm of a real-linear functional `L : Domain3 →L[ℝ] ℂ` is
bounded by the Euclidean norm `√(∑ᵢ ‖L (b i)‖²)` of its gradient covector, for any orthonormal
basis `b`. This is the Hilbert–Schmidt bound `‖L‖_op ≤ ‖L‖_HS`; the reverse inequality is false
for a ℂ-valued (rank-2) codomain, so only `≤` holds — which is the direction the GNS upper
bound needs. -/
theorem opNorm_le_sqrt_sum_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ Domain3) (L : Domain3 →L[ℝ] ℂ) :
    ‖L‖ ≤ Real.sqrt (∑ i, ‖L (b i)‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hn1 : (0:ℝ) ≤ ∑ i, ⟪b i, v⟫ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : L v = ∑ i, ⟪b i, v⟫ • L (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    rw [map_sum]; simp [map_smul]
  rw [hv, mul_comm]
  calc ‖∑ i, ⟪b i, v⟫ • L (b i)‖
      ≤ ∑ i, ‖⟪b i, v⟫ • L (b i)‖ := norm_sum_le _ _
    _ = ∑ i, |⟪b i, v⟫| * ‖L (b i)‖ := by simp [Real.norm_eq_abs]
    _ ≤ Real.sqrt ((∑ i, ⟪b i, v⟫ ^ 2) * (∑ i, ‖L (b i)‖ ^ 2)) := by
        apply Real.le_sqrt_of_sq_le
        calc (∑ i, |⟪b i, v⟫| * ‖L (b i)‖) ^ 2
            ≤ (∑ i, |⟪b i, v⟫| ^ 2) * (∑ i, ‖L (b i)‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = (∑ i, ⟪b i, v⟫ ^ 2) * (∑ i, ‖L (b i)‖ ^ 2) := by simp [sq_abs]
    _ = ‖v‖ * Real.sqrt (∑ i, ‖L (b i)‖ ^ 2) := by
        rw [Real.sqrt_mul hn1]
        congr 1
        have hvn : ∑ i, ⟪b i, v⟫ ^ 2 = ‖v‖ ^ 2 := by
          have := b.sum_sq_norm_inner_right v
          simpa [Real.norm_eq_abs, sq_abs] using this
        rw [hvn, Real.sqrt_sq (norm_nonneg _)]

/-- **Plancherel kernel 2.** For a Schwartz `g : 𝓢(ℝ³, ℂ)`, the squared `L²`-class norm is the
integral of the pointwise squared norm: `‖g.toLp 2‖² = ∫ ‖g ξ‖²`. (Via
`SchwartzMap.inner_toL2_toL2_eq`.) -/
theorem normSq_toLp_two (g : SchwartzMap Domain3 ℂ) :
    ‖g.toLp 2 (volume : Measure Domain3)‖ ^ 2
      = ∫ ξ : Domain3, ‖g ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  have hII : inner ℂ (g.toLp 2 (volume : Measure Domain3)) (g.toLp 2 (volume : Measure Domain3))
      = ∫ x, inner ℂ (g x) (g x) ∂(volume : Measure Domain3) := SchwartzMap.inner_toL2_toL2_eq g g _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hII, ← integral_re]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show RCLike.re (inner ℂ (g ξ) (g ξ)) = ‖g ξ‖ ^ 2
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  · refine (L2.integrable_inner (g.toLp 2 (volume:Measure Domain3))
      (g.toLp 2 (volume:Measure Domain3))).congr ?_
    filter_upwards [g.coeFn_toLp 2 (volume:Measure Domain3)] with x hx; rw [hx]

/-- **Plancherel kernel 3.** Per-direction Schwartz Plancherel: for `φ : 𝓢(ℝ³, ℂ)` and a
direction `m`, `‖(∂_{m}φ).toLp 2‖² = ∫ (2π)² ⟨ξ,m⟩² ‖𝓕 φ ξ‖²`. Uses `fourier_lineDerivOp_eq`
(`𝓕(∂_{m}φ) = 2πi⟨·,m⟩ 𝓕 φ`) + Plancherel (`norm_fourier_toL2_eq`) + `normSq_toLp_two`. -/
theorem normSq_lineDeriv_toLp (φ : SchwartzMap Domain3 ℂ) (m : Domain3) :
    ‖(∂_{m} φ).toLp 2 (volume : Measure Domain3)‖ ^ 2
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
        ∂(volume : Measure Domain3) := by
  rw [← norm_fourier_toL2_eq, normSq_toLp_two]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖(𝓕 (∂_{m} φ)) ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
  have hg : (inner ℝ · m : Domain3 → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hpt : (𝓕 (∂_{m} φ)) ξ = (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℝ) * (𝓕 φ) ξ := by
    rw [fourier_lineDerivOp_eq φ m, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [smul_eq_mul, Complex.real_smul]; ring
  rw [hpt, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hI]

/-- **Plancherel kernel 4.** Integrated gradient–Fourier bound for Schwartz `φ`:
`∫ ‖fderiv ℝ φ x‖² ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖²`. Combines the pointwise HS bound
(`opNorm_le_sqrt_sum_sq`, squared) with the summed per-direction Plancherel
(`normSq_lineDeriv_toLp`) over the standard basis (`∑ᵢ ⟨ξ,eᵢ⟩² = ‖ξ‖²`). -/
theorem integral_normSq_fderiv_le (φ : SchwartzMap Domain3 ℂ) :
    ∫ x : Domain3, ‖fderiv ℝ φ x‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  set b := stdOrthonormalBasis ℝ Domain3 with hb
  have hptwise : ∀ x : Domain3,
      ‖fderiv ℝ φ x‖ ^ 2 ≤ ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 := by
    intro x
    have h := opNorm_le_sqrt_sum_sq b (fderiv ℝ (φ : Domain3 → ℂ) x)
    have hsum_nonneg : (0:ℝ) ≤ ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heq : (∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2) = ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hle : ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2 ≤ ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 := by
      calc ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2
          ≤ (Real.sqrt (∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 := Real.sq_sqrt hsum_nonneg
    rw [heq] at hle
    exact hle
  have hintL : Integrable (fun x : Domain3 => ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2)
      (volume : Measure Domain3) :=
    (memLp_two_iff_integrable_sq_norm
      ((SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).continuous.aestronglyMeasurable)).mp
      ((SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).memLp 2 (volume:Measure Domain3))
  have hintR : ∀ i, Integrable (fun x : Domain3 => ‖(∂_{b i} φ) x‖ ^ 2)
      (volume : Measure Domain3) := fun i =>
    (memLp_two_iff_integrable_sq_norm ((∂_{b i} φ).continuous.aestronglyMeasurable)).mp
      ((∂_{b i} φ).memLp 2 (volume:Measure Domain3))
  have hsumint : Integrable (fun x : Domain3 => ∑ i, ‖(∂_{b i} φ) x‖ ^ 2)
      (volume : Measure Domain3) := integrable_finsetSum _ (fun i _ => hintR i)
  have hstep1 : ∫ x : Domain3, ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ ∫ x : Domain3, ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3) :=
    integral_mono hintL hsumint hptwise
  have hstep2 : ∫ x : Domain3, ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3)
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
    rw [integral_finsetSum _ (fun i _ => hintR i)]
    have hperdir : ∀ i, ∫ x : Domain3, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3)
        = ∫ ξ : Domain3, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2
          ∂(volume:Measure Domain3) := by
      intro i
      rw [← normSq_toLp_two (∂_{b i} φ), normSq_lineDeriv_toLp]
    simp_rw [hperdir]
    have hintP : ∀ i, Integrable
        (fun ξ : Domain3 => (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2)
        (volume : Measure Domain3) := by
      intro i
      have hFR : Integrable (fun ξ : Domain3 => ‖(𝓕 (∂_{b i} φ)) ξ‖^2)
          (volume : Measure Domain3) :=
        (memLp_two_iff_integrable_sq_norm
          ((𝓕 (∂_{b i} φ)).continuous.aestronglyMeasurable)).mp
          ((𝓕 (∂_{b i} φ)).memLp 2 (volume:Measure Domain3))
      refine hFR.congr ?_
      filter_upwards with ξ
      have hg : (inner ℝ · (b i) : Domain3 → ℝ).HasTemperateGrowth :=
        ((innerSL ℝ).flip (b i)).hasTemperateGrowth
      have hpt : (𝓕 (∂_{b i} φ)) ξ
          = (2 * Real.pi * Complex.I) * (inner ℝ ξ (b i) : ℝ) * (𝓕 φ) ξ := by
        rw [fourier_lineDerivOp_eq φ (b i), smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
        simp only [smul_eq_mul, Complex.real_smul]; ring
      rw [hpt, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hI : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
        rw [show (2 * Real.pi * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      rw [hI]
    rw [← integral_finsetSum _ (fun i _ => hintP i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hinner : ∑ i, (inner ℝ ξ (b i))^2 = ‖ξ‖^2 := by
      have := b.sum_sq_norm_inner_right ξ
      simp_rw [real_inner_comm] at this ⊢
      simpa [Real.norm_eq_abs, sq_abs] using this
    calc ∑ i, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2
        = ((2 * Real.pi)^2 * ‖(𝓕 φ) ξ‖^2) * ∑ i, (inner ℝ ξ (b i))^2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (2 * Real.pi)^2 * ‖ξ‖^2 * ‖(𝓕 φ) ξ‖^2 := by rw [hinner]; ring
  rw [hstep2] at hstep1
  exact hstep1

/-! ### The energy-class gradient bound (`EuclideanSpace.single`/`lineDerivOpCLM` presentation) -/

/-- **Plancherel kernel 5.** `fderiv φ x (eᵢ) = (∂_{eᵢ}φ) x` for a complex Schwartz function. -/
theorem fderiv_apply_single_eq_lineDeriv (φ : SchwartzMap Domain3 ℂ) (i : Fin 3) (x : Domain3) :
    fderiv ℝ (φ : Domain3 → ℂ) x (EuclideanSpace.single i (1 : ℝ))
      = (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) (EuclideanSpace.single i (1 : ℝ)) φ) x := by
  rw [LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply]
  exact ((SchwartzMap.hasFDerivAt φ x).hasLineDerivAt
    (EuclideanSpace.single i (1 : ℝ))).lineDeriv.symm

/-- **Plancherel kernel 6.** The `L²`-norm of the full gradient is bounded by the sum over the
three coordinate directions of the `L²`-norms of the directional derivatives:
`eLpNorm (fderiv φ) 2 ≤ ∑ᵢ eLpNorm (∂_{eᵢ}φ) 2`. -/
theorem eLpNorm_fderiv_le_sum_lineDeriv (φ : SchwartzMap Domain3 ℂ) :
    eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) ≤
      ∑ i : Fin 3, eLpNorm
        (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) φ) x) 2 (volume : Measure Domain3) := by
  set b : OrthonormalBasis (Fin 3) ℝ Domain3 := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  set d : Fin 3 → Domain3 → ℂ := fun i x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
    (EuclideanSpace.single i (1 : ℝ)) φ) x with hd
  -- pointwise: ‖fderiv φ x‖ ≤ ∑ᵢ ‖dᵢ x‖.
  have hpt : ∀ x, ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ ≤ ∑ i : Fin 3, ‖d i x‖ := by
    intro x
    refine (opNorm_le_sqrt_sum_sq b (fderiv ℝ (φ : Domain3 → ℂ) x)).trans ?_
    have hbi : ∀ i, (fderiv ℝ (φ : Domain3 → ℂ) x) (b i) = d i x := by
      intro i; rw [hb, EuclideanSpace.basisFun_apply, hd]
      exact fderiv_apply_single_eq_lineDeriv φ i x
    have hsum_nonneg : (0:ℝ) ≤ ∑ i, ‖d i x‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    calc Real.sqrt (∑ i, ‖(fderiv ℝ (φ : Domain3 → ℂ) x) (b i)‖ ^ 2)
        = Real.sqrt (∑ i, ‖d i x‖ ^ 2) := by
          refine congrArg Real.sqrt (Finset.sum_congr rfl (fun i _ => by rw [hbi i]))
      _ ≤ Real.sqrt ((∑ i, ‖d i x‖) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
      _ = ∑ i, ‖d i x‖ := Real.sqrt_sq hsum_nonneg
  -- eLpNorm bound: monotone (pointwise bound) + triangle over the finite sum.
  set e : Fin 3 → Domain3 → ℝ := fun i x => ‖d i x‖ with he
  have hmeas_e : ∀ i : Fin 3, AEStronglyMeasurable (e i) (volume : Measure Domain3) := by
    intro i; rw [he]
    exact ((SchwartzMap.continuous _).norm).aestronglyMeasurable
  -- eLpNorm (fderiv φ) 2 ≤ eLpNorm (∑ᵢ eᵢ) 2.
  have hmono : eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3)
      ≤ eLpNorm (fun x => ∑ i : Fin 3, e i x) 2 (volume : Measure Domain3) := by
    refine eLpNorm_mono_ae_real (Filter.Eventually.of_forall fun x => ?_)
    exact hpt x
  refine hmono.trans ?_
  have htri := eLpNorm_sum_le (μ := (volume : Measure Domain3)) (p := (2 : ENNReal))
    (s := (Finset.univ : Finset (Fin 3))) (f := e) (fun i _ => hmeas_e i) (by norm_num)
  refine htri.trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
  rw [he, hd, eLpNorm_norm]

/-! ### `L²∩L⁶ ↪ L³` interpolation (generic, no Schwartz/Fourier dependence) -/

/-- **Plancherel kernel 7 — quantitative `L²∩L⁶` interpolation at exponent 3.** For
`f : Domain3 → F`, `eLpNorm f 3 ≤ (eLpNorm f 2)^{1/2} · (eLpNorm f 6)^{1/2}`. The square route:
`(eLpNorm f 3)² = eLpNorm (‖f‖²) (3/2) ≤ eLpNorm ‖f‖ 6 · eLpNorm ‖f‖ 2` (Hölder `1/6+1/2=2/3`). -/
theorem eLpNorm_three_le_interp {F : Type*} [NormedAddCommGroup F] (f : Domain3 → F)
    (h2 : MemLp f 2 (volume : Measure Domain3))
    (h6 : MemLp f 6 (volume : Measure Domain3)) :
    eLpNorm f 3 (volume : Measure Domain3)
      ≤ (eLpNorm f 2 (volume : Measure Domain3)) ^ (1/2 : ℝ)
        * (eLpNorm f 6 (volume : Measure Domain3)) ^ (1/2 : ℝ) := by
  set g : Domain3 → ℝ := fun x => ‖f x‖ with hg
  have hg2 : MemLp g 2 (volume : Measure Domain3) := h2.norm
  have hg6 : MemLp g 6 (volume : Measure Domain3) := h6.norm
  haveI : ENNReal.HolderTriple 6 2 (3 / 2) := by
    have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3 / 2 : ℝ) := by constructor <;> norm_num
    have h2' := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, e32] using h2'
  -- Hölder bound on `g·g`: `eLpNorm (g·g) (3/2) ≤ eLpNorm g 6 · eLpNorm g 2`.
  have hholder : eLpNorm (fun x => g x * g x) (3 / 2) (volume : Measure Domain3)
      ≤ eLpNorm g 6 (volume : Measure Domain3) * eLpNorm g 2 (volume : Measure Domain3) := by
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := (6 : ENNReal))
      (q := (2 : ENNReal)) (r := (3 / 2 : ENNReal)) hg6.aestronglyMeasurable
      hg2.aestronglyMeasurable (fun a b : ℝ => a * b) 1
      (Filter.Eventually.of_forall fun x => by
        simp only [nnnorm_mul, one_mul]; exact le_refl _)
    simpa only [ENNReal.coe_one, one_mul] using this
  -- `eLpNorm (g·g) (3/2) = (eLpNorm f 3)²` and `eLpNorm g p = eLpNorm f p`.
  have hgg_eq : eLpNorm (fun x => g x * g x) (3 / 2) (volume : Measure Domain3)
      = eLpNorm f 3 (volume : Measure Domain3) ^ (2 : ℝ) := by
    have hpow : (fun x => ‖f x‖ ^ (2 : ℝ)) = (fun x => g x * g x) := by
      funext x; simp [hg, sq]
    have hkey : eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (3 / 2) (volume : Measure Domain3)
        = eLpNorm f ((3 / 2) * ENNReal.ofReal 2) (volume : Measure Domain3) ^ (2 : ℝ) :=
      eLpNorm_norm_rpow f (by norm_num)
    have h32 : ((3 : ENNReal) / 2) * ENNReal.ofReal 2 = 3 := by
      rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num [ENNReal.ofReal]]
      rw [ENNReal.div_mul_cancel] <;> norm_num
    rw [hpow, h32] at hkey
    exact hkey
  have hgn2 : eLpNorm g 2 (volume : Measure Domain3) = eLpNorm f 2 (volume : Measure Domain3) := by
    rw [hg, eLpNorm_norm]
  have hgn6 : eLpNorm g 6 (volume : Measure Domain3) = eLpNorm f 6 (volume : Measure Domain3) := by
    rw [hg, eLpNorm_norm]
  rw [hgg_eq, hgn2, hgn6] at hholder
  -- `(eLpNorm f 3)² ≤ eLpNorm f 6 · eLpNorm f 2`; take square roots (rpow 1/2).
  have hsq : eLpNorm f 3 (volume : Measure Domain3)
      ≤ (eLpNorm f 6 (volume : Measure Domain3) * eLpNorm f 2 (volume : Measure Domain3))
          ^ (1/2 : ℝ) := by
    have hmono := ENNReal.rpow_le_rpow hholder (by norm_num : (0:ℝ) ≤ 1/2)
    rwa [← ENNReal.rpow_mul, show (2 : ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one] at hmono
  refine hsq.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), mul_comm]

/-! ### Misc L² bridge (item (e) fold-in): `eLpNorm` at `p = 2` as `ofReal (√∫)` -/

end LerayHopf.PlancherelKernels
