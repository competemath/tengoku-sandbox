/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.EllipticPoints
import Tengoku

/-!
# Modular Invariance of Vanishing Order

The order of vanishing `orderOfVanishingAt'` is invariant under the full modular group SL₂(ℤ).
This follows from T-periodicity `f(z+1) = f(z)` and the S-identity `f(-1/z) = z^k f(z)`.

We also provide:
* `modularFormCompOfComplex` — coercion of modular form to ℂ → ℂ
* `fdBox` and `modularForm_finitely_many_zeros_in_fdBox` — finiteness of zeros
* Cusp nonvanishing (`exists_height_cusp_nonvanishing`)
-/

open Complex Set Filter Topology CongruenceSubgroup
open scoped Real UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- The composition of a modular form with `ofComplex`, for contour integration. -/
abbrev modularFormCompOfComplex : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex

private lemma mero_sub_const_fwd (g : ℂ → ℂ) (x c : ℂ) (h_sub_an : AnalyticAt ℂ (· - c) (x + c))
    (hg : MeromorphicAt g x) :
    MeromorphicAt (fun w => g (w - c)) (x + c) := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n, ?_⟩
  have : (fun w => (w - (x + c)) ^ n • g (w - c)) = (fun z => (z - x) ^ n • g z) ∘ (· - c) := by
    ext w; simp only [Function.comp]; congr 2; ring
  rw [this]
  exact hn.comp_of_eq h_sub_an (add_sub_cancel_right x c)

private lemma mero_sub_const_bwd (g : ℂ → ℂ) (x c : ℂ) (h_add_an : AnalyticAt ℂ (· + c) x)
    (hgφ : MeromorphicAt (fun w => g (w - c)) (x + c)) :
    MeromorphicAt g x := by
  obtain ⟨n, hn⟩ := hgφ
  refine ⟨n, ?_⟩
  have : (fun w => (w - x) ^ n • g w) = (fun z => (z - (x + c)) ^ n • g (z - c)) ∘ (· + c) := by
    ext w; simp only [Function.comp, add_sub_cancel_right]; congr 2; ring
  rw [this]
  exact hn.comp_of_eq h_add_an rfl

private lemma filter_map_sub_const (x c : ℂ) {p : ℂ → Prop} (hp : ∀ᶠ z in 𝓝[≠] x, p z) :
    ∀ᶠ w in 𝓝[≠] (x + c), p (w - c) := by
  have : map (Homeomorph.addRight (-c)) (𝓝[≠] (x + c)) = 𝓝[≠] x := by
    rw [Homeomorph.map_punctured_nhds_eq]
    simp only [Homeomorph.coe_addRight, add_neg_cancel_right]
  rw [← this, eventually_map] at hp
  exact hp.mono fun z hz => by simpa [sub_eq_add_neg] using hz

private lemma meromorphicOrderAt_comp_sub_const (g : ℂ → ℂ) (x c : ℂ) :
    meromorphicOrderAt (fun w => g (w - c)) (x + c) = meromorphicOrderAt g x := by
  have h_sub_an : AnalyticAt ℂ (· - c) (x + c) := analyticAt_id.sub analyticAt_const
  have h_add_an : AnalyticAt ℂ (· + c) x := analyticAt_id.add analyticAt_const
  by_cases hg_mero : MeromorphicAt g x
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg_mero,
        meromorphicOrderAt_of_not_meromorphicAt (mt (mero_sub_const_bwd g x c h_add_an) hg_mero)]
  by_cases htop : meromorphicOrderAt g x = ⊤
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    exact filter_map_sub_const x c htop
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (meromorphicOrderAt_eq_int_iff hg_mero).mp hn.symm
  rw [hn.symm, meromorphicOrderAt_eq_int_iff (mero_sub_const_fwd g x c h_sub_an hg_mero)]
  refine ⟨fun w => h (w - c), hh_an.comp_of_eq h_sub_an (add_sub_cancel_right x c),
    by simpa using hh_ne, ?_⟩
  exact (filter_map_sub_const x c hh_eq).mono fun z hz => by
    simp only [smul_eq_mul] at hz ⊢
    rw [hz]; congr 2; ring

/-- T-invariance of vanishing order: `ord(f, z+1) = ord(f, z)`. -/
lemma ord_add_one_eq (p : ℍ) :
    orderOfVanishingAt' f ((1 : ℝ) +ᵥ p) = orderOfVanishingAt' f p := by
  unfold orderOfVanishingAt'
  set G : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 with hG_def
  have hvAdd_coe : (((1 : ℝ) +ᵥ p : ℍ) : ℂ) = (p : ℂ) + 1 := by
    simp [UpperHalfPlane.coe_vadd, add_comm]
  conv_lhs => rw [hvAdd_coe]
  have hG_eq_near : G =ᶠ[𝓝[≠] ((p : ℂ) + 1)] (fun w => G (w - 1)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds
      (show 0 < ((p : ℂ) + 1).im by simpa using p.im_pos)] with z hz _
    simp only [hG_def]
    rw [dite_eq_left hz, dite_eq_left (by simp [sub_im, hz] : 0 < (z - 1).im)]
    set z₀ : ℍ := ⟨z - 1, by simp [sub_im, hz]⟩
    have h_period := SlashInvariantForm.vAdd_width_periodic 1 k 1 f.toSlashInvariantForm z₀
    have h_vadd_coe : ((1 : ℝ) +ᵥ z₀ : ℍ) = ⟨z, hz⟩ := by
      ext
      change (↑(1 : ℝ) : ℂ) + (z - 1) = z
      push_cast; ring
    simp only [Nat.cast_one, mul_one, Int.cast_one, h_vadd_coe,
      ModularForm.toSlashInvariantForm_coe] at h_period
    exact h_period
  rw [meromorphicOrderAt_congr hG_eq_near, meromorphicOrderAt_comp_sub_const]

/-- An open box containing the truncated fundamental domain. -/
def fdBox (M : ℝ) : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ (1:ℝ)/2 < z.im ∧ z.im < M}

lemma fdBox_im_pos {M : ℝ} {z : ℂ} (hz : z ∈ fdBox M) : 0 < z.im := by
  linarith [hz.2.2.1]

/-- A nonzero modular form has finitely many zeros in `fdBox M`. -/
theorem modularForm_finitely_many_zeros_in_fdBox (hf : f ≠ 0) {M : ℝ} (hM : (1:ℝ)/2 < M) :
    Set.Finite {z ∈ fdBox M | modularFormCompOfComplex f z = 0} := by
  by_contra h_inf
  have hBdd : Bornology.IsBounded (fdBox M) :=
    isBounded_iff_forall_norm_le.mpr ⟨1 + M, fun z hz =>
      (Complex.norm_le_abs_re_add_abs_im z).trans (by
        have : |z.re| < 1 := abs_lt.mpr ⟨by linarith [hz.1], hz.2.1⟩
        have : |z.im| ≤ M := abs_le.mpr ⟨by linarith [hz.2.2.1], hz.2.2.2.le⟩
        linarith)⟩
  obtain ⟨z₀, hz₀K, hz₀_acc⟩ :=
    (show Set.Infinite _ from h_inf).exists_accPt_of_subset_isCompact hBdd.isCompact_closure
      ((sep_subset _ _).trans subset_closure)
  have hz₀_pos : 0 < z₀.im := by
    have : (1:ℝ)/2 ≤ z₀.im := closure_minimal (fun z hz => hz.2.2.1.le)
      (isClosed_le continuous_const Complex.continuous_im) hz₀K
    linarith
  have h_freq : ∃ᶠ y in 𝓝[≠] z₀, modularFormCompOfComplex f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hz₀_acc).mono fun y hy => hy.2
  have h_analOn : AnalyticOnNhd ℂ (modularFormCompOfComplex f) {z : ℂ | 0 < z.im} :=
    fun z hz => (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have h_preconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0)
      (fun z (hz : 0 < z.im) => hz) (fun z (hz : 0 < z.im) => le_of_lt hz)).isPreconnected
  apply hf
  ext z
  simpa only [FunLike.coe_zero, Pi.zero_apply, modularFormCompOfComplex,
      Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      h_preconn hz₀_pos h_freq) z.im_pos

/-- The cusp function of a nonzero modular form is not identically zero near 0. -/
theorem cuspFunction_not_eventually_zero (hf : f ≠ 0) :
    ¬∀ᶠ q in 𝓝 (0 : ℂ), UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q = 0 := by
  intro h_freq
  have hMC : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  have h_diff : DifferentiableOn ℂ (UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f))
      (Metric.ball 0 1) := fun q hq =>
    (ModularFormClass.differentiableAt_cuspFunction f
      (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL
      (by rwa [Metric.mem_ball, dist_zero_right] at hq)).differentiableWithinAt
  have h_eqOn : EqOn (UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f)) 0 (Metric.ball 0 1) :=
    (h_diff.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1)) h_freq
  apply hf
  ext τ
  simp only [FunLike.coe_zero, Pi.zero_apply]
  rw [← SlashInvariantFormClass.eq_cuspFunction f τ one_mem_strictPeriods_SL
    (by norm_num : (1:ℝ) ≠ 0)]
  exact h_eqOn (by
    rw [Metric.mem_ball, dist_zero_right]
    exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ)

/-- For a nonzero modular form, the cusp function is eventually nonzero near 0. -/
theorem cuspFunction_eventually_ne_zero (hf : f ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ),
      UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q ≠ 0 :=
  have hMC : ModularFormClass (ModularForm (Gamma 1) k) 𝒮ℒ k :=
    Gamma_one_coe_eq_SL ▸ inferInstance
  (ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num : (0 : ℝ) < 1)
    one_mem_strictPeriods_SL).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (cuspFunction_not_eventually_zero f hf)

/-- Existence of a nonvanishing radius for the cusp function. -/
theorem exists_radius_cusp_nonvanishing (hf : f ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : ℂ, q ∈ Metric.closedBall (0 : ℂ) r →
      q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q ≠ 0 := by
  obtain ⟨s, hs_prop, hs_open, hs_zero⟩ := eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (cuspFunction_eventually_ne_zero f hf))
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hs_open 0 hs_zero
  exact ⟨r / 2, by linarith, fun q hq hq_ne =>
    hs_prop q (hr_ball (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (by linarith)))
      (mem_compl_singleton_iff.mpr hq_ne)⟩

/-- Convert a q-radius to a FD boundary height. -/
noncomputable def heightOfRadius (r : ℝ) : ℝ := -Real.log r / (2 * Real.pi)

/-- For a nonzero modular form, there exists `H > √3/2` with cusp nonvanishing. -/
theorem exists_height_cusp_nonvanishing (hf : f ≠ 0) :
    ∃ H : ℝ, Real.sqrt 3 / 2 < H ∧
      ∀ q : ℂ, q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H)) →
        q ≠ 0 → UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q ≠ 0 := by
  obtain ⟨r, hr_pos, hr_nonvan⟩ := exists_radius_cusp_nonvanishing f hf
  let H₀ := max (heightOfRadius r) (Real.sqrt 3 / 2 + 1)
  refine ⟨H₀, (by linarith : Real.sqrt 3 / 2 < Real.sqrt 3 / 2 + 1).trans_le
    (le_max_right _ _), fun q hq hq_ne => ?_⟩
  apply hr_nonvan q _ hq_ne
  apply Metric.closedBall_subset_closedBall _ hq
  have hH₀_ge : heightOfRadius r ≤ H₀ := le_max_left _ _
  calc Real.exp (-2 * Real.pi * H₀)
      ≤ Real.exp (-2 * Real.pi * heightOfRadius r) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    _ = r := by
        rw [show -2 * Real.pi * heightOfRadius r = Real.log r by
          unfold heightOfRadius; field_simp]
        exact Real.exp_log hr_pos

/-- Height monotonicity for cusp nonvanishing. -/
lemma cusp_nonvanishing_height_mono {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂)
    (h : ∀ q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₁)), q ≠ 0 →
      UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q ≠ 0) :
    ∀ q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₂)), q ≠ 0 →
      UpperHalfPlane.cuspFunction (1 : ℝ) (⇑f) q ≠ 0 :=
  fun q hq hq_ne => h q (Metric.closedBall_subset_closedBall
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) hq) hq_ne

end
