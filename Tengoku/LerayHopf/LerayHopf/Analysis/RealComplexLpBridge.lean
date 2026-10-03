import Tengoku.LerayHopf.LerayHopf.R3.Regularity

namespace LerayHopf

open MeasureTheory

/-!
# Real/complex `L²` bridge: real-part CLM and bounded real multipliers

Generic `L²(ℝ³)` infrastructure extracted from `EnergyClassConvection.lean` (issue #113 PR-2):
the real-part continuous linear map `L²(ℝ³;ℂ) → L²(ℝ³;ℝ)`, and multiplication of a real `L²`
element by an essentially bounded real function (`mulRBdd`), landing back in `L²`. These are
pure real/complex-`Lp` facts with no convection-specific content, needed as supporting
infrastructure for the B6a weak-Leibniz IBP construction (`WeakLeibniz.lean`).

All ten declarations were `private` in `EnergyClassConvection.lean`; made public here.

## Declarations

- `reLp`, `reLp_coeFn`, `norm_reLp_le` — the real-part CLM and its basic properties
- `mulRBdd`, `mulRBdd_coeFn`, `mulRBdd_sub`, `norm_mulRBdd_le`, `tendsto_mulRBdd` —
  the bounded real multiplier and its properties
- `integral_mul_mul_eq_inner`, `tendsto_integral_mul_mul` — the core limit lemma:
  `aₙ·bₙ·h` integrates to a jointly-continuous real inner product

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-- The real-part map `L²(ℝ³;ℂ) → L²(ℝ³;ℝ)` as a continuous linear map (via `Complex.reCLM`). -/
noncomputable def reLp : L2C_R3 →L[ℝ] Lp ℝ 2 (volume : Measure Domain3) :=
  Complex.reCLM.compLpL 2 (volume : Measure Domain3)

/-- The `Lp`-coercion of `reLp f` agrees a.e. with the pointwise real part of `f`. -/
theorem reLp_coeFn (f : L2C_R3) :
    (reLp f : Domain3 → ℝ) =ᵐ[volume] fun x => (f x).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.reCLM f] with x hx
  rw [reLp]; rw [hx]; rfl

/-- The real-part map contracts the `L²` norm: `‖reLp f‖ ≤ ‖f‖`. -/
theorem norm_reLp_le (f : L2C_R3) : ‖reLp f‖ ≤ ‖f‖ := by
  have hcoe : (reLp f : Domain3 → ℝ) =ᵐ[volume] fun x => (f x).re := reLp_coeFn f
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hcoe]
  refine ENNReal.toReal_mono (by finiteness) ?_
  refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (f x)

/-- Multiplication of a real `L²` element by an essentially bounded real function, landing in
`L²`. Built directly (not as a CLM) — we only need its `coeFn` and an `L²`-Lipschitz bound. -/
noncomputable def mulRBdd (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh)).toLp

/-- The `Lp`-coercion of `mulRBdd h a` agrees a.e. with the pointwise product `h · a`. -/
theorem mulRBdd_coeFn (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    (mulRBdd h hh a : Domain3 → ℝ) =ᵐ[volume] fun x => h x * a x := by
  filter_upwards [MemLp.coeFn_toLp (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh))]
    with x hx
  rw [mulRBdd]; rw [hx]; rfl

/-- `mulRBdd` is additive (used to express the difference of two multiplier images). -/
theorem mulRBdd_sub (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    mulRBdd h hh a - mulRBdd h hh b = mulRBdd h hh (a - b) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (mulRBdd h hh a) (mulRBdd h hh b), mulRBdd_coeFn h hh a,
    mulRBdd_coeFn h hh b, mulRBdd_coeFn h hh (a - b), Lp.coeFn_sub a b] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5, Pi.sub_apply, mul_sub]

/-- `L²`-norm bound for the multiplier: `‖mulRBdd h c‖ ≤ ‖h‖_∞ · ‖c‖`. -/
theorem norm_mulRBdd_le (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (c : Lp ℝ 2 (volume : Measure Domain3)) :
    ‖mulRBdd h hh c‖ ≤ (eLpNorm h ⊤ (volume : Measure Domain3)).toReal * ‖c‖ := by
  have hnorm : ‖mulRBdd h hh c‖
      = (eLpNorm (h • (c : Domain3 → ℝ)) 2 (volume : Measure Domain3)).toReal :=
    Lp.norm_toLp _ _
  have hcnorm : ‖c‖ = (eLpNorm c 2 (volume : Measure Domain3)).toReal := Lp.norm_def c
  rw [hnorm, hcnorm, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono
    (ENNReal.mul_ne_top hh.eLpNorm_lt_top.ne (Lp.memLp c).eLpNorm_lt_top.ne) ?_
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable _) hh.aestronglyMeasurable

/-- The bounded multiplier sends an `L²`-convergent sequence to an `L²`-convergent sequence. -/
theorem tendsto_mulRBdd (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    {a : ℕ → Lp ℝ 2 (volume : Measure Domain3)} {a₀ : Lp ℝ 2 (volume : Measure Domain3)}
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀)) :
    Filter.Tendsto (fun n => mulRBdd h hh (a n)) Filter.atTop (nhds (mulRBdd h hh a₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at ha ⊢
  set C : ℝ := (eLpNorm h ⊤ (volume : Measure Domain3)).toReal with hC
  have hbound : ∀ n, ‖mulRBdd h hh (a n) - mulRBdd h hh a₀‖ ≤ C * ‖a n - a₀‖ := by
    intro n; rw [mulRBdd_sub]; exact norm_mulRBdd_le h hh (a n - a₀)
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  simpa using ha.const_mul C

/-- The integral `∫ a·b·h` over `ℝ³` for real `L²` elements `a, b` and bounded `h` equals the
real `L²` inner product `⟪a, mulRBdd h b⟫`. -/
theorem integral_mul_mul_eq_inner (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    ∫ x : Domain3, (a x) * (b x) * (h x) ∂(volume : Measure Domain3)
      = (inner ℝ a (mulRBdd h hh b) : ℝ) := by
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [mulRBdd_coeFn h hh b] with x hx
  rw [RCLike.inner_apply, hx, conj_trivial]; ring

/-- **Core limit lemma.** If `aₙ → a` and `bₙ → b` in `L²(ℝ³;ℝ)` and `h` is essentially bounded,
then `∫ aₙ·bₙ·h → ∫ a·b·h`. (Real `L²` inner product is jointly continuous.) -/
theorem tendsto_integral_mul_mul (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    {a b : ℕ → Lp ℝ 2 (volume : Measure Domain3)}
    {a₀ b₀ : Lp ℝ 2 (volume : Measure Domain3)}
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀))
    (hb : Filter.Tendsto b Filter.atTop (nhds b₀)) :
    Filter.Tendsto (fun n => ∫ x : Domain3, (a n x) * (b n x) * (h x) ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (a₀ x) * (b₀ x) * (h x) ∂(volume : Measure Domain3))) := by
  have heq : (fun n => ∫ x : Domain3, (a n x) * (b n x) * (h x) ∂(volume : Measure Domain3))
      = fun n => (inner ℝ (a n) (mulRBdd h hh (b n)) : ℝ) := by
    funext n; exact integral_mul_mul_eq_inner h hh (a n) (b n)
  rw [heq, integral_mul_mul_eq_inner h hh a₀ b₀]
  exact ha.inner (tendsto_mulRBdd h hh hb)

end LerayHopf
