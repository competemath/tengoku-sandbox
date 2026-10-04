/-
# LerayHopf.Bochner.WeakLimitToolkit — generic Hilbert-space weak-limit toolkit

**Campaign node:** R3 galerkin_limit_passage_R3 removal, issue #4 PR-5.

This file is a **domain-neutral, PDE-free, torus-free** Hilbert-space analysis engine.
It depends only on Mathlib and introduces **no** `LerayHopf.*` domain import — preserving
full reusability for both the T³ and ℝ³ Galerkin applications.

## Provenance

These five lemmas were originally extracted verbatim from `LerayHopf.Torus.TraceEnergy`
(lines ~274–539), where they were `private`.  Issue #131 rewired `LerayHopf.Torus.TraceEnergy`
to import this file and call these originals directly; the private copies there are gone.

## Main declarations

- `normSq_le_liminf_of_inner_tendsto` — squared-norm weak lsc via inner products
- `cauchySeq_inner_extend` — Cauchy extension along norm-approximation
- `exists_weak_limit_in_submodule` — Riesz representative inside a closed submodule
- `exists_mem_of_ae_full` — a.e.-full sets are dense in `[0, T]`
- `cauchySeq_of_equiLipschitz_of_dense` — equi-Lipschitz + dense convergence ⇒ Cauchy everywhere

## Axioms

No new axioms; no `sorry`.
-/

import Tengoku

namespace LerayHopf

open MeasureTheory Filter Topology

/-! ### Generic Hilbert-space weak-limit toolkit -/

section HilbertToolkit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cauchy extension along norm-approximation:** if `‖xₖ‖ ≤ M` and `z` can be approximated
in norm by vectors `z'` for which `k ↦ ⟪xₖ, z'⟫` is Cauchy, then `k ↦ ⟪xₖ, z⟫` is Cauchy. -/
theorem cauchySeq_inner_extend (x : ℕ → E) (M : ℝ) (hM : ∀ k, ‖x k‖ ≤ M)
    (z : E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ z' : E, ‖z - z'‖ < ε ∧
      CauchySeq (fun k => inner (𝕜 := ℝ) (x k) z')) :
    CauchySeq (fun k => inner (𝕜 := ℝ) (x k) z) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (x 0)) (hM 0)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨z', hz', hC⟩ := happrox (ε / (3 * (M + 1))) (by positivity)
  rw [Metric.cauchySeq_iff] at hC
  obtain ⟨N, hN⟩ := hC (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdist := hN m hm n hn
  rw [Real.dist_eq] at hdist ⊢
  have hcross : ∀ k, |inner (𝕜 := ℝ) (x k) z - inner (𝕜 := ℝ) (x k) z'| ≤ M * ‖z - z'‖ := by
    intro k
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hMz : M * ‖z - z'‖ ≤ M * (ε / (3 * (M + 1))) :=
    mul_le_mul_of_nonneg_left hz'.le hM0
  have hMz2 : M * (ε / (3 * (M + 1))) ≤ ε / 3 := by
    have h2 : M * (ε / (3 * (M + 1))) = (M / (M + 1)) * (ε / 3) := by
      field_simp
    have h3 : M / (M + 1) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < M + 1)]
      linarith
    calc M * (ε / (3 * (M + 1))) = (M / (M + 1)) * (ε / 3) := h2
      _ ≤ 1 * (ε / 3) := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ε / 3 := one_mul _
  calc |inner (𝕜 := ℝ) (x m) z - inner (𝕜 := ℝ) (x n) z|
      ≤ |inner (𝕜 := ℝ) (x m) z - inner (𝕜 := ℝ) (x m) z'|
        + |inner (𝕜 := ℝ) (x m) z' - inner (𝕜 := ℝ) (x n) z| := abs_sub_le _ _ _
    _ ≤ |inner (𝕜 := ℝ) (x m) z - inner (𝕜 := ℝ) (x m) z'|
        + (|inner (𝕜 := ℝ) (x m) z' - inner (𝕜 := ℝ) (x n) z'|
          + |inner (𝕜 := ℝ) (x n) z' - inner (𝕜 := ℝ) (x n) z|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε := by
        have h1 := hcross m
        have h2 := hcross n
        rw [abs_sub_comm (inner (𝕜 := ℝ) (x n) z') (inner (𝕜 := ℝ) (x n) z)] at *
        linarith [hcross n]

/-- **Weak limit inside a closed submodule.**  If `xₖ ∈ K`, `‖xₖ‖ ≤ M`, and every inner-product
sequence `k ↦ ⟪xₖ, z⟫` is Cauchy, then there is `y ∈ K` with `‖y‖ ≤ M` and `⟪xₖ, z⟫ → ⟪y, z⟫`
for every `z` (Riesz representation of the limit functional; membership by the
orthogonal-projection argument). -/
theorem exists_weak_limit_in_submodule [CompleteSpace E] (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (x : ℕ → E) (hxK : ∀ k, x k ∈ K) (M : ℝ)
    (hM : ∀ k, ‖x k‖ ≤ M)
    (hC : ∀ z : E, CauchySeq (fun k => inner (𝕜 := ℝ) (x k) z)) :
    ∃ y : E, y ∈ K ∧ ‖y‖ ≤ M ∧
      ∀ z : E, Tendsto (fun k => inner (𝕜 := ℝ) (x k) z) atTop (𝓝 (inner (𝕜 := ℝ) y z)) := by
  have hlim : ∀ z : E, ∃ l : ℝ, Tendsto (fun k => inner (𝕜 := ℝ) (x k) z) atTop (𝓝 l) :=
    fun z => cauchySeq_tendsto_of_complete (hC z)
  choose φ hφ using hlim
  have hadd : ∀ z z' : E, φ (z + z') = φ z + φ z' := by
    intro z z'
    refine tendsto_nhds_unique (hφ (z + z')) ?_
    refine ((hφ z).add (hφ z')).congr fun k => ?_
    rw [← inner_add_right]
  have hsmul : ∀ (c : ℝ) (z : E), φ (c • z) = c * φ z := by
    intro c z
    refine tendsto_nhds_unique (hφ (c • z)) ?_
    refine ((hφ z).const_mul c).congr fun k => ?_
    rw [real_inner_smul_right]
  have hbound : ∀ z : E, |φ z| ≤ M * ‖z‖ := by
    intro z
    refine le_of_tendsto (hφ z).abs (Filter.Eventually.of_forall fun k => ?_)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  set Lf : E →ₗ[ℝ] ℝ :=
    { toFun := φ
      map_add' := hadd
      map_smul' := fun c z => by simpa using hsmul c z } with hLf
  set L : E →L[ℝ] ℝ := Lf.mkContinuous M (fun z => by
    rw [Real.norm_eq_abs]; exact hbound z) with hL
  set y : E := (InnerProductSpace.toDual ℝ E).symm L with hydef
  have hyz : ∀ z : E, inner (𝕜 := ℝ) y z = φ z := by
    intro z
    have happ : (InnerProductSpace.toDual ℝ E) y = L :=
      (InnerProductSpace.toDual ℝ E).apply_symm_apply L
    calc inner (𝕜 := ℝ) y z = (InnerProductSpace.toDual ℝ E) y z := rfl
      _ = L z := by rw [happ]
      _ = φ z := rfl
  -- membership: `y = starProjection K y ∈ K`
  have hyK : y ∈ K := by
    have hop : K.starProjection y ∈ K := K.starProjection_apply_mem y
    have hoth : y - K.starProjection y ∈ Kᗮ := K.sub_starProjection_mem_orthogonal y
    have hz : ∀ k, inner (𝕜 := ℝ) (x k) (y - K.starProjection y) = 0 := fun k =>
      (Submodule.mem_orthogonal K _).mp hoth (x k) (hxK k)
    have hφ0 : φ (y - K.starProjection y) = 0 := by
      refine tendsto_nhds_unique (hφ (y - K.starProjection y)) ?_
      simp [hz]
    have h1 : inner (𝕜 := ℝ) y (y - K.starProjection y) = 0 := by rw [hyz]; exact hφ0
    have h2 : inner (𝕜 := ℝ) (K.starProjection y) (y - K.starProjection y) = 0 :=
      (Submodule.mem_orthogonal K _).mp hoth _ hop
    have hnorm0 : ‖y - K.starProjection y‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, h1, h2, sub_zero]
    have heq : y = K.starProjection y := by
      have hsub0 : y - K.starProjection y = 0 :=
        norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm0)
      exact sub_eq_zero.mp hsub0
    rw [heq]; exact hop
  -- norm bound: `‖y‖² = φ y ≤ M ‖y‖`
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (x 0)) (hM 0)
  have hybd : ‖y‖ ≤ M := by
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | hpos
    · rw [← h0]; exact hM0
    · have h1 : ‖y‖ ^ 2 = φ y := by rw [← hyz y, real_inner_self_eq_norm_sq]
      have h2 : ‖y‖ ^ 2 ≤ M * ‖y‖ := h1 ▸ ((le_abs_self _).trans (hbound y))
      nlinarith
  exact ⟨y, hyK, hybd, fun z => (hyz z) ▸ hφ z⟩

end HilbertToolkit

/-! ### Density of an a.e.-full subset of `[0, T]` -/

/-- A set of full measure in `[0, T]` meets every `ε`-neighborhood of every point of `[0, T]`. -/
theorem exists_mem_of_ae_full {T : ℝ} (hT : 0 < T) (S : Set ℝ)
    (hS : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ S)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S ∩ Set.Icc (0 : ℝ) T, |s - t| < ε := by
  by_contra hcon
  push Not at hcon
  set a : ℝ := max 0 (t - ε / 2) with ha
  set b : ℝ := min T (t + ε / 2) with hb
  have hab : a < b := by
    rw [ha, hb, max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hT, by linarith [ht.1]⟩, ⟨by linarith [ht.2], by linarith⟩⟩
  -- `Ioo a b ⊆ [0,T]` and every point of it is `ε`-close to `t`, hence outside `S` by `hcon`.
  have hIcc : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) T := fun x hx =>
    ⟨le_trans (le_max_left 0 (t - ε / 2)) hx.1.le, le_trans hx.2.le (min_le_left T (t + ε / 2))⟩
  have hclose : ∀ x ∈ Set.Ioo a b, |x - t| < ε := by
    intro x hx
    have h1 : t - ε / 2 < x := lt_of_le_of_lt (le_max_right 0 (t - ε / 2)) hx.1
    have h2 : x < t + ε / 2 := lt_of_lt_of_le hx.2 (min_le_right T (t + ε / 2))
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hnotS : ∀ x ∈ Set.Ioo a b, x ∉ S := by
    intro x hx hxS
    exact absurd (hcon x ⟨hxS, hIcc hx⟩) (not_le.mpr (hclose x hx))
  -- measure contradiction
  have hnull : volume.restrict (Set.Icc (0 : ℝ) T) {x | x ∉ S} = 0 := by
    have := hS
    rwa [MeasureTheory.ae_iff] at this
  have hle : volume.restrict (Set.Icc (0 : ℝ) T) (Set.Ioo a b) = 0 :=
    measure_mono_null (fun x hx => hnotS x hx) hnull
  have hval : volume.restrict (Set.Icc (0 : ℝ) T) (Set.Ioo a b)
      = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hIcc, Real.volume_Ioo]
  rw [hval] at hle
  exact absurd hle (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'

/-! ### Equi-Lipschitz + dense convergence ⇒ Cauchy everywhere -/

/-- A family of eventually-equi-Lipschitz real functions on `[0, T]` that is Cauchy on a
dense-in-`[0,T]` subset is Cauchy at every point of `[0, T]`. -/
theorem cauchySeq_of_equiLipschitz_of_dense {T : ℝ} (f : ℕ → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (K : ℕ)
    (hLip : ∀ k, K ≤ k → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t' ∈ Set.Icc (0 : ℝ) T,
      |f k t' - f k s| ≤ L * |t' - s|)
    (S : Set ℝ)
    (hdense : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ s ∈ S ∩ Set.Icc (0 : ℝ) T, |s - u| < ε)
    (hconv : ∀ s ∈ S ∩ Set.Icc (0 : ℝ) T, CauchySeq (fun k => f k s))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    CauchySeq (fun k => f k t) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨s, hsS, hst⟩ := hdense t ht (ε / (3 * (L + 1))) (by positivity)
  have hCs := hconv s hsS
  rw [Metric.cauchySeq_iff] at hCs
  obtain ⟨N₁, hN₁⟩ := hCs (ε / 3) (by positivity)
  refine ⟨max N₁ K, fun m hm n hn => ?_⟩
  have h1 := hN₁ m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have h2 := hLip m (le_trans (le_max_right _ _) hm) s hsS.2 t ht
  have h3 := hLip n (le_trans (le_max_right _ _) hn) s hsS.2 t ht
  rw [Real.dist_eq] at h1 ⊢
  have habs : |t - s| < ε / (3 * (L + 1)) := by rw [abs_sub_comm]; exact hst
  have hL1 : L * |t - s| < ε / 3 := by
    have hstep : L * |t - s| ≤ L * (ε / (3 * (L + 1))) :=
      mul_le_mul_of_nonneg_left habs.le hL
    have hstep2 : L * (ε / (3 * (L + 1))) < ε / 3 := by
      have h2 : L * (ε / (3 * (L + 1))) = (L / (L + 1)) * (ε / 3) := by
        field_simp
      have h3 : L / (L + 1) < 1 := by
        rw [div_lt_one (by linarith : (0 : ℝ) < L + 1)]
        linarith
      calc L * (ε / (3 * (L + 1))) = (L / (L + 1)) * (ε / 3) := h2
        _ < 1 * (ε / 3) := mul_lt_mul_of_pos_right h3 (by positivity)
        _ = ε / 3 := one_mul _
    linarith
  calc |f m t - f n t|
      ≤ |f m t - f m s| + |f m s - f n t| := abs_sub_le _ _ _
    _ ≤ |f m t - f m s| + (|f m s - f n s| + |f n s - f n t|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε := by
        rw [abs_sub_comm (f n s) (f n t)] at *
        linarith

end LerayHopf
