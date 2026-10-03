import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq
import Tengoku.Analysis.InnerProductSpace.Calculus

/-!
# Generic dissipative finite-dimensional ODE: forward-global existence (issue #112)

**Campaign:** `docs/scratch/galerkin-domain-plan.md` §3.1 (PR-A). This file promotes the
feasibility spike `LerayHopf/Scratch/GalerkinDomainSpike.lean` to a production module:
the abstract dissipative-`C¹`-field forward-tiling/gluing argument, proved ONCE over any
finite-dimensional real inner-product space `V` and any field `g : V → V`, rather than
twice (once per lane) as it currently sits duplicated in `LerayHopf/R3/GalerkinODESolve.lean`
and `LerayHopf/Torus/GalerkinODESolve.lean`. PR-B (issue #112 lane rewiring) will re-derive
each lane's `forwardGlobalSolution_exists` as a corollary of `forwardGlobalSolution_exists`
below, instantiated via `coe_hasDerivAt` for the ambient-submodule transport step.

Mathlib-only imports (pdelib-grade layer — flagged in `docs/pdelib-staging.md`); this file
imports no `LerayHopf` module and is consumed by nothing in `LerayHopf` yet (PR-A has no
consumers by design; wiring happens in PR-B).

The five imports mirror `LerayHopf/R3/GalerkinODESolve.lean`'s import list: the mathlib
lemmas consumed by the proof bodies below (`ContDiffAt.exists_forall_mem_closedBall_
exists_eq_forall_mem_Ioo_hasDerivAt`, `ODE_solution_unique_of_mem_Icc_{left,right}`,
finite-dimensional compactness of closed balls) live in exactly these files.

## Scaffold status

Every proof body below is filled (PR-A, prover pass); the bodies are direct ports of
`LerayHopf/Scratch/GalerkinDomainSpike.lean`'s `AbstractODE` section (spike compiled
clean, see plan §2/§9), with internal lemma references renamed to match this module's
frozen names. Statements are FROZEN by the architect (plan §3.1) and were not altered.
-/

namespace LerayHopf.Galerkin

open Metric Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Energy derivative along a solution of `c' = g c`: `d/dt ½‖c t‖² = ⟪c t, g (c t)⟫`. -/
theorem energy_hasDerivAt_of_solution (g : V → V) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (g (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (inner (𝕜 := ℝ) (c t) (g (c t))) t := by
  have hinner : HasDerivAt (fun s => inner (𝕜 := ℝ) (c s) (c s))
      (inner (𝕜 := ℝ) (c t) (g (c t)) + inner (𝕜 := ℝ) (g (c t)) (c t)) t :=
    hc.inner ℝ hc
  have hfun : (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * inner (𝕜 := ℝ) (c s) (c s) := by
    funext s; rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  have hval : (1 / 2 : ℝ) *
      (inner (𝕜 := ℝ) (c t) (g (c t)) + inner (𝕜 := ℝ) (g (c t)) (c t))
      = inner (𝕜 := ℝ) (c t) (g (c t)) := by
    rw [real_inner_comm (g (c t)) (c t)]; ring
  rw [← hval]
  exact hinner.const_mul (1 / 2 : ℝ)

omit [FiniteDimensional ℝ V] in
/-- A-priori bound: any forward solution of a dissipative field stays in the initial ball. -/
theorem norm_le_of_forwardSolution_of_dissipative (g : V → V)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ))
    (c : ℝ → V) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt c (g (c t)) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖c t‖ ≤ ‖c 0‖ := by
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2 with hE
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt E (inner (𝕜 := ℝ) (c s) (g (c s))) s := fun s hs =>
    energy_hasDerivAt_of_solution g c s (hsol s hs)
  have hAnti : AntitoneOn E (Icc (0 : ℝ) T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s (interior_subset hs)).deriv]
      exact hdiss (c s)
  intro t ht
  have hle : E t ≤ E 0 := hAnti ⟨le_refl 0, hT⟩ ht ht.1
  have hsq : ‖c t‖ ^ 2 ≤ ‖c 0‖ ^ 2 := by simp only [hE] at hle; linarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- Uniform local-existence time on a ball: a single `δ` works for every start point in
`closedBall 0 R` and every start time `t₀`. -/
theorem uniform_local_time (g : V → V) (hg : ContDiff ℝ 1 g) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ Metric.closedBall (0 : V) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → V, α t₀ = x₀ ∧
        ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), HasDerivAt α (g (α t)) t := by
  have hcd : ∀ x : V, ContDiffAt ℝ 1 g x := fun x => hg.contDiffAt
  have hloc : ∀ y : V, ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ x ∈ closedBall y r, ∃ α : ℝ → V, α 0 = x ∧
        ∀ t ∈ Ioo (0 - ε) (0 + ε), HasDerivAt α (g (α t)) t := fun y =>
    (hcd y).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose r hr ε hε Hsol using hloc
  have hcover : closedBall (0 : V) R ⊆ ⋃ y, ball y (r y) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩
  obtain ⟨I, hI⟩ := (isCompact_closedBall (0 : V) R).elim_finite_subcover
    (fun y => ball y (r y)) (fun y => isOpen_ball) hcover
  rcases I.eq_empty_or_nonempty with hIemp | hIne
  · refine ⟨1, one_pos, fun x₀ hx₀ t₀ => ?_⟩
    rw [hIemp] at hI
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
      subset_empty_iff] at hI
    exact absurd (hI ▸ hx₀) (Set.notMem_empty x₀)
  · refine ⟨I.inf' hIne ε, ?_, fun x₀ hx₀ t₀ => ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun y _ => hε y
    · set δ := I.inf' hIne ε with hδ
      have hx₀' : x₀ ∈ ⋃ y ∈ I, ball y (r y) := hI hx₀
      rw [mem_iUnion₂] at hx₀'
      obtain ⟨y, hyI, hxy⟩ := hx₀'
      have hxmem : x₀ ∈ closedBall y (r y) := ball_subset_closedBall hxy
      obtain ⟨α, hα0, hαsol⟩ := Hsol y x₀ hxmem
      refine ⟨fun t => α (t - t₀), by simp only [sub_self]; exact hα0, fun t ht => ?_⟩
      have hδε : δ ≤ ε y := Finset.inf'_le _ hyI
      have htmem : t - t₀ ∈ Ioo (0 - ε y) (0 + ε y) := by
        rw [mem_Ioo] at ht ⊢
        refine ⟨by rw [zero_sub]; linarith [ht.1], by rw [zero_add]; linarith [ht.2]⟩
      have hd := hαsol (t - t₀) htmem
      have hsub : HasDerivAt (fun t : ℝ => t - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
      have hcomp := hd.scomp t hsub
      simp only [one_smul, Function.comp_def] at hcomp
      exact hcomp

omit [FiniteDimensional ℝ V] in
/-- Tiling induction: a forward solution exists on `[0, k·δ/2]` for every `k`, given a
uniform local-existence time `δ` on the a-priori ball around `x₀`. -/
private theorem solve_exists_on_step (g : V → V)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ))
    (x₀ : V) {δ : ℝ} (hδ : 0 < δ)
    (huniform : ∀ y ∈ closedBall (0 : V) ‖x₀‖, ∀ t₀ : ℝ,
      ∃ α : ℝ → V, α t₀ = y ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt α (g (α t)) t) :
    ∀ k : ℕ, ∃ c : ℝ → V, c 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)), HasDerivAt c (g (c t)) t := by
  set R := ‖x₀‖ with hR
  have hs2 : (0 : ℝ) < δ / 2 := by positivity
  intro k
  induction k with
  | zero =>
    have hx₀mem : x₀ ∈ closedBall (0 : V) R := by
      rw [mem_closedBall, dist_zero_right, hR]
    obtain ⟨α, hα0, hαsol⟩ := huniform x₀ hx₀mem 0
    refine ⟨α, hα0, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul] at ht
    have hts : t = 0 := le_antisymm ht.2 ht.1
    subst hts
    exact hαsol 0 ⟨by linarith, by linarith⟩
  | succ k ih =>
    obtain ⟨c, hc0, hcsol⟩ := ih
    have hkδ0 : (0 : ℝ) ≤ k * (δ / 2) := by positivity
    have hbound := norm_le_of_forwardSolution_of_dissipative g hdiss c hkδ0 hcsol
      (k * (δ / 2)) ⟨hkδ0, le_rfl⟩
    have hckmem : c (k * (δ / 2)) ∈ closedBall (0 : V) R := by
      rw [mem_closedBall, dist_zero_right, hR, ← hc0]
      exact hbound
    obtain ⟨α, hα0, hαsol⟩ := huniform (c (k * (δ / 2))) hckmem (k * (δ / 2))
    refine ⟨fun t => if t ≤ k * (δ / 2) then c t else α t, ?_, fun t ht => ?_⟩
    · simp only [show (0 : ℝ) ≤ k * (δ / 2) from hkδ0, ite_eq_left]; exact hc0
    · rcases lt_trichotomy t (k * (δ / 2)) with hlt | heq | hgt
      · have hmem : t ∈ Icc (0 : ℝ) (k * (δ / 2)) := ⟨ht.1, le_of_lt hlt⟩
        have hev : (fun t => if t ≤ k * (δ / 2) then c t else α t) =ᶠ[nhds t] c := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          simp only [ite_eq_left (le_of_lt (mem_Iio.mp hs))]
        rw [hev.hasDerivAt_iff]
        simp only [ite_eq_left (le_of_lt hlt)]
        exact hcsol t hmem
      · set m : ℝ := k * (δ / 2) with hm
        rw [heq]
        have hval : α m = c m := hα0
        have hpw_t : (if m ≤ m then c m else α m) = c m := by rw [ite_eq_left le_rfl]
        have hleft : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Iic m) m := by
          refine (hcsol m ⟨by rw [← heq]; exact ht.1, le_rfl⟩).hasDerivWithinAt.congr_of_mem
            (fun s hs => ?_) (mem_Iic.mpr le_rfl)
          simp only [ite_eq_left (mem_Iic.mp hs)]
        have htmem : m ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
        have hαt : HasDerivAt α (g (α m)) m := hαsol m htmem
        have hright : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Ici m) m := by
          have hαdw : HasDerivWithinAt α (g (c m)) (Ici m) m := by
            rw [← hval]; exact hαt.hasDerivWithinAt
          refine hαdw.congr_of_mem (fun s hs => ?_) (mem_Ici.mpr le_rfl)
          rcases eq_or_lt_of_le (mem_Ici.mp hs) with hse | hslt
          · simp only [← hse, ite_eq_left le_rfl]; exact hval.symm
          · simp only [ite_eq_right (not_le.mpr hslt)]
        have hunion := hleft.union hright
        rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
        show HasDerivAt (fun s => if s ≤ m then c s else α s)
          (g (if m ≤ m then c m else α m)) m
        rw [hpw_t]
        exact hunion
      · have hub : t ≤ (k + 1 : ℝ) * (δ / 2) := by
          have h2 := ht.2; push_cast at h2 ⊢; linarith
        have htmem : t ∈ Ioo (k * (δ / 2) - δ) (k * (δ / 2) + δ) := by
          refine ⟨by linarith, ?_⟩
          have : (k + 1 : ℝ) * (δ / 2) = k * (δ / 2) + δ / 2 := by ring
          have hδ2 : δ / 2 < δ := by linarith
          linarith [hub, this]
        have hev : (fun s => if s ≤ k * (δ / 2) then c s else α s) =ᶠ[nhds t] α := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          simp only [ite_eq_right (not_le.mpr (mem_Ioi.mp hs))]
        rw [hev.hasDerivAt_iff]
        show HasDerivAt α (g (if t ≤ k * (δ / 2) then c t else α t)) t
        rw [ite_eq_right (not_le.mpr hgt)]
        exact hαsol t htmem

/-- Splice uniqueness: two local solutions agreeing at one point agree on the whole
overlap interval. -/
theorem solution_agree (g : V → V) (hg : ContDiff ℝ 1 g)
    (α β : ℝ → V) {a b t₀ : ℝ} (_hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Set.Icc a b, HasDerivAt α (g (α t)) t)
    (hβ : ∀ t ∈ Set.Icc a b, HasDerivAt β (g (β t)) t) :
    ∀ t ∈ Set.Icc a b, α t = β t := by
  have hαc : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousAt.continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun t ht => (hβ t ht).continuousAt.continuousWithinAt
  obtain ⟨Mα, hMα⟩ := (((isCompact_Icc).image_of_continuousOn hαc).image continuous_norm).bddAbove
  obtain ⟨Mβ, hMβ⟩ := (((isCompact_Icc).image_of_continuousOn hβc).image continuous_norm).bddAbove
  set M : ℝ := max (max Mα Mβ) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hαM : ∀ t ∈ Icc a b, α t ∈ closedBall (0 : V) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMα ⟨α t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_left Mα Mβ) (le_max_left _ _)
  have hβM : ∀ t ∈ Icc a b, β t ∈ closedBall (0 : V) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMβ ⟨β t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_right Mα Mβ) (le_max_left _ _)
  obtain ⟨K, hlip⟩ := (hg.contDiffOn (s := closedBall (0 : V) M)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hbwd : EqOn α β (Icc a t₀) := by
    have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    refine ODE_solution_unique_of_mem_Icc_left (a := a) (b := t₀) (K := K)
      (s := fun _ => closedBall (0 : V) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1.le, ht'.2⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1.le, ht'.2⟩)) hαβ
  have hfwd : EqOn α β (Icc t₀ b) := by
    have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    refine ODE_solution_unique_of_mem_Icc_right (a := t₀) (b := b) (K := K)
      (s := fun _ => closedBall (0 : V) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1, ht'.2.le⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1, ht'.2.le⟩)) hαβ
  intro t ht
  rcases le_total t t₀ with hle | hle
  · exact hbwd ⟨ht.1, hle⟩
  · exact hfwd ⟨hle, ht.2⟩

/-- **Forward-global existence** for a dissipative `C¹` field on a finite-dimensional real
inner-product space, by tiling `[0,∞)` with the uniform local-existence time on the
a-priori ball and gluing by uniqueness. This is the abstract core that both lanes'
`forwardGlobalSolution_exists` will specialize to (PR-B). -/
theorem forwardGlobalSolution_exists (g : V → V) (hg : ContDiff ℝ 1 g)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ)) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (g (c t)) t := by
  classical
  obtain ⟨δ, hδ, huniform⟩ := uniform_local_time g hg ‖x₀‖
  have hstep := solve_exists_on_step g hdiss x₀ hδ huniform
  set s2 : ℝ := δ / 2 with hs2def
  have hs2 : (0 : ℝ) < s2 := by rw [hs2def]; positivity
  choose ck hck0 hcksol using hstep
  set N : ℝ → ℕ := fun t => ⌊t / s2⌋₊ + 1 with hN
  set c : ℝ → V := fun t => ck (N t) t with hc
  have hltN : ∀ t : ℝ, t < N t * s2 := by
    intro t
    rcases lt_or_ge t 0 with ht0 | ht0
    · have hN1 : (1 : ℝ) ≤ (N t : ℝ) := by
        rw [hN]; push_cast; have := Nat.zero_le (⌊t / s2⌋₊); linarith
      have hpos : (0 : ℝ) < N t * s2 := mul_pos (by linarith) hs2
      linarith
    · have hlt : t / s2 < (⌊t / s2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (t / s2)
      have heq2 : t = (t / s2) * s2 := by field_simp
      have hmul := mul_lt_mul_of_pos_right hlt hs2
      rw [← heq2] at hmul
      rw [hN]; push_cast
      exact hmul
  have hmemN : ∀ t, 0 ≤ t → t ∈ Icc (0 : ℝ) (N t * s2) := fun t ht => ⟨ht, le_of_lt (hltN t)⟩
  have hagree : ∀ j k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (j * s2) (k * s2)), ck j t = ck k t := by
    intro j k t ht
    have hjk : (0 : ℝ) ≤ min (j * s2) (k * s2) := le_min (by positivity) (by positivity)
    refine solution_agree g hg (ck j) (ck k) hjk ⟨le_refl 0, hjk⟩
      (by rw [hck0 j, hck0 k]) ?_ ?_ t ht
    · intro u hu
      exact hcksol j u ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩
    · intro u hu
      exact hcksol k u ⟨hu.1, le_trans hu.2 (min_le_right _ _)⟩
  refine ⟨c, ?_, ?_⟩
  · show ck (N 0) 0 = x₀
    rw [hck0 (N 0)]
  · intro t ht
    have hsol := hcksol (N t) t (hmemN t ht)
    have hN1 : ∀ u : ℝ, u < s2 → N u = 1 := by
      intro u hu
      show ⌊u / s2⌋₊ + 1 = 1
      have hfloor : ⌊u / s2⌋₊ = 0 := by
        apply Nat.floor_eq_zero.mpr
        rw [div_lt_one hs2]; exact hu
      rw [hfloor]
    have hev : c =ᶠ[nhds t] ck (N t) := by
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · rw [← ht0]
        have hVnhds : Iio s2 ∈ nhds (0 : ℝ) := Iio_mem_nhds hs2
        filter_upwards [hVnhds] with u hu
        show ck (N u) u = ck (N 0) u
        rw [hN1 u hu, hN1 0 hs2]
      · have hVnhds : Iio (N t * s2) ∩ Ioi 0 ∈ nhds t :=
          Filter.inter_mem (Iio_mem_nhds (hltN t)) (Ioi_mem_nhds ht0)
        filter_upwards [hVnhds] with u hu
        show ck (N u) u = ck (N t) u
        have humem : u ∈ Icc (0 : ℝ) (min (N u * s2) (N t * s2)) :=
          ⟨le_of_lt (mem_Ioi.mp hu.2), le_min (le_of_lt (hltN u)) (le_of_lt (mem_Iio.mp hu.1))⟩
        rw [hagree (N u) (N t) u humem]
    have hgoal : HasDerivAt (ck (N t)) (g (c t)) t := by
      have hct : c t = ck (N t) t := rfl
      rw [show g (c t) = g (ck (N t) t) from by rw [hct]]
      exact hsol
    exact (hev.hasDerivAt_iff).mpr hgoal

/-- Generic ambient transport: an intrinsic `HasDerivAt` in a submodule lifts to a
`HasDerivAt` of the coerced ambient curve. This is the generic form of both lanes'
private `solve_hasDerivAt_ambient` transport steps. -/
theorem coe_hasDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (W : Submodule ℝ H) (c : ℝ → W) (v : W) (t : ℝ) (h : HasDerivAt c v t) :
    HasDerivAt (fun s => (c s : H)) (v : H) t := by
  have hl : HasFDerivAt (Submodule.subtypeL W) (Submodule.subtypeL W) (c t) :=
    (Submodule.subtypeL W).hasFDerivAt
  have hcomp := hl.comp_hasDerivAt t h
  simpa [Function.comp_def, Submodule.subtypeL_apply] using hcomp

end LerayHopf.Galerkin
