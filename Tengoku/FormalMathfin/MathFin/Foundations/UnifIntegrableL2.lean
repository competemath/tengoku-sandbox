/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Bounded in `L²` ⟹ uniformly integrable in `L¹` (a finite-measure Vitali producer)

Mathlib provides the Vitali *consumer* `MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure`
(uniform integrability + convergence in measure ⟹ `L¹` convergence) but **no producer** of uniform
integrability from an `Lᵖ` bound with `p > 1`. This file supplies the `p = 2` case (the truncation
producer needs no finiteness of `μ` — only the downstream Vitali consumer does):

* `MathFin.unifIntegrable_one_of_sq_integral_le` — a family `f : ι → α → ℝ` with `f i ∈ L²` and a
  **uniform** second-moment bound `∫ (f i)² ≤ M` is `UnifIntegrable f 1 μ`.

The proof is a Chebyshev truncation fed to `MeasureTheory.unifIntegrable_of`: on `{‖f i‖ ≥ C}` one
has `C·‖f i‖ ≤ ‖f i‖²`, so the truncated `L¹` tail `∫_{‖f i‖≥C} ‖f i‖ ≤ C⁻¹·∫‖f i‖² ≤ C⁻¹·M`, which
is `≤ ε` once `C ≥ M/ε` — uniformly in `i`.

The intended use is the `L²→L¹` limit of Girsanov Doléans densities `Z⁽ⁿ⁾_T`, whose uniform bound
`∫ (Z⁽ⁿ⁾)² ≤ exp(K²T)` comes from the `Z² = E^{−2c}·exp(∑ c²Δτ)` identity; this lemma is the piece
that lets convergence in measure upgrade to `L¹` (hence `∫ Z⁽ⁿ⁾ → ∫ Z`, delivering unit mean).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MathFin

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {ι : Type*} {f : ι → α → ℝ}

/-- **Fatou `L²`-membership of an a.e.-subsequence limit.** If every `f n ∈ L²` with a uniform second
moment `∫ (f n)² ≤ M`, and some subsequence has `f (msₖ) → g` a.e., then `g ∈ L²`: Fatou on the
squared enorms, `∫⁻ ‖g²‖ₑ ≤ liminf ∫⁻ ‖f(msₖ)²‖ₑ = liminf ∫ f(msₖ)² ≤ M < ∞`. No finiteness of `μ`
is needed (pure Fatou) — the limit-side companion to the finite-measure Vitali producers above, and
the single principle behind an a.e.-subsequential `L²` limit inheriting its family's uniform second
moment (both the Girsanov continuous and predictable Doléans densities consume it). -/
theorem memLp_two_of_subseq_ae_of_sq_bound {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hmeas : ∀ n, Measurable (f n))
    {M : ℝ} (hM : ∀ n, ∫ x, (f n x) ^ 2 ∂μ ≤ M)
    (hsub : ∃ ms : ℕ → ℕ, ∀ᵐ x ∂μ, Tendsto (fun k ↦ f (ms k) x) atTop (𝓝 (g x))) :
    MemLp g 2 μ := by
  obtain ⟨ms, hae⟩ := hsub
  have hgmeas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k ↦ (hmeas (ms k)).aestronglyMeasurable) hae
  rw [memLp_two_iff_integrable_sq hgmeas]
  refine ⟨hgmeas.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsqbnd : ∀ k, ∫⁻ x, ‖(f (ms k) x) ^ 2‖ₑ ∂μ ≤ ENNReal.ofReal M := fun k ↦ by
    have hint_sq := (memLp_two_iff_integrable_sq (hf (ms k)).1).mp (hf (ms k))
    calc ∫⁻ x, ‖(f (ms k) x) ^ 2‖ₑ ∂μ
        = ∫⁻ x, ENNReal.ofReal ((f (ms k) x) ^ 2) ∂μ :=
          lintegral_congr fun x ↦ by rw [Real.enorm_eq_ofReal (sq_nonneg _)]
      _ = ENNReal.ofReal (∫ x, (f (ms k) x) ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint_sq (ae_of_all _ fun x ↦ sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hM (ms k))
  have hlim : (fun x ↦ ‖(g x) ^ 2‖ₑ)
      =ᵐ[μ] fun x ↦ Filter.liminf (fun k ↦ ‖(f (ms k) x) ^ 2‖ₑ) atTop := by
    filter_upwards [hae] with x hx
    exact ((hx.pow 2).enorm.liminf_eq).symm
  rw [lintegral_congr_ae hlim]
  exact ((lintegral_liminf_le (fun k ↦ ((hmeas (ms k)).pow_const 2).enorm)).trans
    ((liminf_le_liminf (Filter.Eventually.of_forall hsqbnd)).trans (liminf_const _).le)).trans_lt
    ENNReal.ofReal_lt_top

/-- **`TendstoInMeasure` only sees a.e.-classes of the sequence.** Replacing each `f n` by an
a.e.-equal `f' n` preserves convergence in measure — a generic congruence Mathlib does not ship
in this left-argument form. -/
theorem tendstoInMeasure_congr_left {E : Type*} [MetricSpace E] {f f' : ℕ → α → E} {g : α → E}
    (h : ∀ n, f n =ᵐ[μ] f' n) (hfg : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ f' atTop g := by
  intro ε hε
  refine (hfg ε hε).congr fun n ↦ measure_congr ?_
  rw [Filter.eventuallyEq_set]
  filter_upwards [h n] with x hx
  simp only [hx]

end MathFin
