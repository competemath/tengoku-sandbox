import Tengoku.LerayHopf.LerayHopf.R3.SolutionInterfaces
import Tengoku
import Tengoku.Std
import Tengoku.Tactic.Aesop
import Tengoku.Meta.Qq

/-!
# Galerkin ODE on ℝ³: axiom-free energy/dissipation/regularity payoff (milestone `ode-galerkin-r3`)

**Milestone:** `ode-galerkin-r3`.

This file substantiates the **analytic content** of the `galerkin_ode_solution_R3` axiom
(`LerayHopf/R3/SolutionInterfaces.lean`) by producing — for each `n` — a
`GalerkinSolutionData_R3 𝔊 F ν u₀ n` from a single **isolated, honest hypothesis**
(`GalerkinODEInput`) plus the algebraic properties of the abstract NS forms `F`.

## Import justification (NO import cycle)

```
Domain.lean → DivergenceFree.lean → … → SolutionInterfaces.lean
                                              └── GalerkinODE.lean   [THIS FILE]
```

This file **imports** `SolutionInterfaces.lean` solely to *name* the
**definitions/structures/proved lemmas** it produces:
`GalerkinSolutionData_R3`, `R3GalerkinScheme`, `R3NSForms`, `R3NSForms.b_self_zero`,
`stokesTestPairing_R3`, `viscousFormSq_R3` (and `Time`, `L2Sigma_R3`, `L2VF_R3`,
`memH1VF_R3`).  It does **NOT** import nor reference the axiom block destructively, and
`SolutionInterfaces.lean` does **NOT** import this file — the dependency is one-directional
(SolutionInterfaces → GalerkinODE), exactly as P5's `GalerkinScheme.lean`.  **No cycle.**

## HONEST scope (no overclaim — the P2 lesson)

This milestone does **NOT** make `galerkin_ode_solution_R3` axiom-free.  It proves the
energy / dissipation / H¹-regularity **algebra** axiom-free, and **isolates** the two
genuine mathlib gaps — (i) global existence (no continuation-from-a-priori-bound theorem in
mathlib for vector spaces) and (ii) the weak-form ⇄ `C¹`-vector-field Riesz representation
of the abstract trilinear form `F.b` — into the hypothesis structure `GalerkinODEInput`.
The connection to the axiom is **semantic**: we prove
`(GalerkinODEInput 𝔊 F ν u₀ n) → GalerkinSolutionData_R3 𝔊 F ν u₀ n`.

### Proved here (axiom-free, must-prove — lean-prover targets)

- `stokesTestPairing_R3_diag` (N1)        — diagonal viscous pairing = dissipation.
- `galerkinCurve_reg_mem` (M0)            — H¹ regularity of any curve in the Schwartz subspace.
- `galerkin_energy_identity` (E1)         — `½ d/dt ‖u‖² = −ν · viscousFormSq_R3 1 u`.
- `galerkin_energy_bound` (E2)            — the uniform energy bound (`energy_bound` field).
- `galerkin_reg_bound` (E3)               — the uniform dissipation bound (`reg_bound` field).
- `galerkinSolutionData_R3_of_input` (D)  — **deliverable**: assemble the full data.

### Isolated hypothesis (NOT proved — supplied by the caller, by design)

- `GalerkinODEInput`                      — global existence + weak-form representation
  (the genuine frontier).  It supplies ONLY the raw solution curve and the two facts that
  *define* it as a solution; it deliberately omits the energy/dissipation/regularity payoff.

## Assumptions / axioms

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.**  The genuine frontier is carried by
the hypothesis structure `GalerkinODEInput` (a bundle of curve data, not an environment
axiom) — the honest analogue of P3's `LocalRellichInput` and P5's `SchwartzGalerkinBasis`.
`SolutionInterfaces.lean` is **NOT edited**.
-/

namespace LerayHopf

open MeasureTheory
open scoped Topology

/-! ### M0 — H¹ regularity of a Galerkin-subspace curve -/

/-- H¹ regularity of any vector staying in the Schwartz Galerkin subspace. -/
theorem galerkinCurve_reg_mem (𝔊 : R3GalerkinScheme) (n : ℕ) (v : L2VF_R3)
    (hv : v = 𝔊.P n v) : memH1VF_R3 v := by
  -- `𝔊.range_schwartz n v` gives a real Schwartz `ψ` with the j-th real component of
  -- `𝔊.P n v` equal to `(ψ j).toLp`; since `v = 𝔊.P n v`, the same holds for `v`.  The
  -- complex component `L2VF_projComponentC_R3 j v` is then `RCLike.ofRealCLM ∘ (ψ j)` at the
  -- Lp level, i.e. the toLp of the complex Schwartz map `(ψ j).postcompCLM RCLike.ofRealCLM`;
  -- `SchwartzMap.memSobolev` gives `MemSobolev 1 2` of its tempered-distribution coercion,
  -- and the two coercions agree by `toTemperedDistribution_toLp_eq`.
  obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz n v
  intro j
  -- the complex Schwartz function whose toLp is the complex component of `v`
  set g : SchwartzMap Domain3 ℂ := (ψ j).postcompCLM (RCLike.ofRealCLM (K := ℂ)) with hg
  -- the complex component equals `g.toLp`
  have hcomp : L2VF_projComponentC_R3 j v = g.toLp 2 (volume : Measure Domain3) := by
    have hreal : L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3) := by
      rw [hv]; exact hψ j
    apply Lp.ext
    have h1 : (L2VF_projComponentC_R3 j v : Domain3 → ℂ)
        =ᵐ[volume] fun a => (RCLike.ofRealCLM (K := ℂ)) ((L2VF_projComponent_R3 j v) a) := by
      rw [L2VF_projComponentC_R3]
      exact ContinuousLinearMap.coeFn_compLpL _ _
    rw [hreal] at h1
    have hpsi : ((ψ j).toLp 2 (volume : Measure Domain3) : Domain3 → ℝ) =ᵐ[volume] ⇑(ψ j) :=
      SchwartzMap.coeFn_toLp (ψ j) 2 (volume : Measure Domain3)
    have h2 : (g.toLp 2 (volume : Measure Domain3) : Domain3 → ℂ)
        =ᵐ[volume] fun a => (RCLike.ofRealCLM (K := ℂ)) ((ψ j) a) := by
      refine (SchwartzMap.coeFn_toLp g 2 (volume : Measure Domain3)).trans ?_
      filter_upwards with a
      rw [hg, SchwartzMap.postcompCLM_apply]
    refine h1.trans (Filter.EventuallyEq.trans ?_ h2.symm)
    filter_upwards [hpsi] with a ha
    rw [ha]
  -- the goal (after `intro j`) is `MemSobolev 1 2 (component : 𝓢')`; rewrite the component to
  -- `g.toLp` and use that the two tempered-distribution coercions agree.
  rw [hcomp, MeasureTheory.Lp.toTemperedDistribution_toLp_eq]
  exact SchwartzMap.memSobolev (s := (1 : ℝ)) (p := 2) g

/-! ### S0 — the isolated analytic frontier hypothesis -/

/-- Isolated analytic frontier for the ℝ³ Galerkin ODE.

For each `n`, the finite-dim projected Navier–Stokes ODE on the subspace `range(𝔊.P n)`
admits a GLOBAL solution curve.  This bundles the two genuine mathlib gaps — (i) global
existence (no continuation-from-a-priori-bound theorem in mathlib) and (ii) the
weak-form ⇄ vector-field Riesz representation of the projected NS ODE for the abstract
trilinear form `F.b` — WITHOUT proving them; they are hypotheses supplied by the caller.

**Honesty (no-smuggle):** the input supplies ONLY the raw solution curve together with the
two facts that DEFINE it as a solution (its global differentiability `u_hasDeriv` and the
weak Galerkin ODE `u_ode`), plus the structural membership/initial-trace seeds
(`u_initial`, `u_inVn`).  It supplies NEITHER the energy bound, NOR the dissipation bound,
NOR H¹ regularity — all of those are DERIVED axiom-free below from the ODE and `F`'s
antisymmetry (`R3NSForms.b_self_zero`).  This matches the genuine content of
Picard–Lindelöf+continuation (existence of the curve) and excludes exactly the analytic
payoff this milestone proves.  The five present fields are byte-for-byte copies of the first
five `GalerkinSolutionData_R3` fields; the deliberately ABSENT fields are
`reg_mem`, `energy_bound`, `reg_bound`. -/
structure GalerkinODEInput (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) where
  /-- The global Galerkin solution curve. -/
  u : Time → L2Sigma_R3
  /-- Initial condition: `u(0) = 𝔊.P n u₀` (coerced into `L2Sigma_R3` via `preserves_sigma`). -/
  u_initial : u 0 = ⟨𝔊.P n (u₀ : L2VF_R3), 𝔊.preserves_sigma n (u₀ : L2VF_R3) u₀.2⟩
  /-- The curve stays in the n-th approximation subspace (so it is a genuine Galerkin curve). -/
  u_inVn : ∀ t, (u t : L2VF_R3) = 𝔊.P n (u t : L2VF_R3)
  /-- Forward differentiability of the ambient curve `t ↦ (u t : L2VF_R3)` at `t ≥ 0`.

  SOUNDNESS (forward-only): physical Galerkin solutions are confined only on forward time by
  the energy bound; this quadratic ODE field can blow up in finite backward time, so the
  all-`t` form was a latent over-strength claim.  Restricted to `0 ≤ t` to match the genuine
  Picard–Lindelöf+continuation guarantee. -/
  u_hasDeriv : ∀ t, 0 ≤ t → HasDerivAt (fun s => (u s : L2VF_R3))
    (deriv (fun s => (u s : L2VF_R3)) t) t
  /-- The weak projected Galerkin ODE (the defining equation) at forward times `t ≥ 0`: for
  all test vectors `w` with `𝔊.P n w = w`,
  `⟪u'(t), w⟫ + ν · stokesTestPairing_R3(u(t), w) + b(u(t), u(t), w) = 0`.

  SOUNDNESS (forward-only): same rationale as `u_hasDeriv`; restricted to `0 ≤ t`. -/
  u_ode : ∀ t, 0 ≤ t → ∀ w : L2Sigma_R3,
    (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : L2VF_R3)) t) (w : L2VF_R3) +
    ν * stokesTestPairing_R3 (u t : L2VF_R3) (w : L2VF_R3) + F.b (u t) (u t) w = 0
  /-- **Weighted-Fourier continuity (finite-dim-derived).** The weighted-Fourier component curve
  `s ↦ √W • 𝓕(projⱼ (u s))` is continuous on `Ici 0`.  Discharged at the concrete producer from
  the finite-dimensionality of the Galerkin subspace (all norms equivalent there). -/
  viscous_curve_continuous : ∀ j : Fin 3,
    ContinuousOn (fun s => weightedFourierComponent (u s : L2VF_R3)
      (galerkinCurve_reg_mem 𝔊 n (u s : L2VF_R3) (u_inVn s)) j) (Set.Ici 0)

/-! ### Helper — `viscousFormSq_R3` scales linearly in `ν` -/

/-- The viscous dissipation form scales linearly in `ν`:
`viscousFormSq_R3 ν u = ν • viscousFormSq_R3 1 u`.  Immediate from the leading `ν *` in
the definition.  Used to relate the `ν`-scaled `reg_bound` integrand (E3) to the
`ν = 1` energy identity (E1). -/
theorem viscousFormSq_R3_eq_smul (ν : ℝ) (u : L2VF_R3) :
    viscousFormSq_R3 ν u = ν • viscousFormSq_R3 1 u := by
  unfold viscousFormSq_R3
  simp [smul_eq_mul, mul_assoc]

/-! ### N0 — symmetry -/

open scoped FourierTransform in
/-- Stokes is symmetric on `V_n` span elements: the integrand `Re[(𝓕 uⱼ)·conj(𝓕 wⱼ)]` equals
`Re[(𝓕 wⱼ)·conj(𝓕 uⱼ)]` pointwise, so the whole pairing is symmetric (no integrability needed).

Promoted from a `private` copy in `R3/GalerkinODESolve.lean` (issue #112 PR-B): both
`GalerkinODESolve.lean` and `GalerkinODEExistence.lean` already import this file, so hosting
the one public copy here lets `r3FieldForms` (`GalerkinODEExistence.lean`) cite it directly
without an import cycle. Proof body unchanged from the original. -/
theorem stokesTestPairing_R3_symm (u w : L2VF_R3) :
    stokesTestPairing_R3 u w = stokesTestPairing_R3 w u := by
  unfold stokesTestPairing_R3
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  -- It suffices to equate the `.re` factors.
  have hre : ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
        (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)).re
      = ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ *
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)).re := by
    rw [← Complex.conj_re ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ *
        (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ))]
    congr 1
    rw [map_mul, Complex.conj_conj]
    ring
  exact congrArg (fun r => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * r) hre

/-! ### N1 — diagonal viscous pairing -/

/-- On the diagonal the viscous pairing is the dissipation:
`stokesTestPairing_R3 u u = viscousFormSq_R3 1 u`. -/
theorem stokesTestPairing_R3_diag (u : L2VF_R3) :
    stokesTestPairing_R3 u u = viscousFormSq_R3 1 u := by
  unfold stokesTestPairing_R3 viscousFormSq_R3
  rw [one_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only
  congr 1
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-! ### E1 — the energy identity (analytic core) -/

/-- Energy identity at forward times `t ≥ 0`: `½ d/dt ‖u(t)‖² = −ν · viscousFormSq_R3 1 (u t)`
along the ODE.  Equivalently `HasDerivAt (fun s => ½‖u s‖²) (−ν·viscousFormSq_R3 1 (u t)) t`.

Forward-only: it consumes `u_hasDeriv`/`u_ode`, both now restricted to `0 ≤ t`. -/
theorem galerkin_energy_identity (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) (I : GalerkinODEInput 𝔊 F ν u₀ n) (t : Time)
    (ht : 0 ≤ t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(I.u s : L2VF_R3)‖ ^ 2)
      (- ν * viscousFormSq_R3 1 (I.u t : L2VF_R3)) t := by
  -- abbreviations
  set u' := deriv (fun s => (I.u s : L2VF_R3)) t with hu'
  -- the ODE, tested against `w = I.u t` (a legal test by `I.u_inVn t`)
  have hode := I.u_ode t ht (I.u t) (I.u_inVn t)
  rw [R3NSForms.b_self_zero F (I.u t), add_zero, stokesTestPairing_R3_diag] at hode
  -- hode : ⟪u', u t⟫ + ν * viscousFormSq_R3 1 (u t) = 0
  -- the derivative of `s ↦ ⟪u s, u s⟫` is `⟪u t, u'⟫ + ⟪u', u t⟫`
  have hinner :
      HasDerivAt (fun s => inner (𝕜 := ℝ) (I.u s : L2VF_R3) (I.u s : L2VF_R3))
        (inner (𝕜 := ℝ) (I.u t : L2VF_R3) u' + inner (𝕜 := ℝ) u' (I.u t : L2VF_R3)) t :=
    (I.u_hasDeriv t ht).inner ℝ (I.u_hasDeriv t ht)
  -- rewrite `½‖u s‖²` as `½ * ⟪u s, u s⟫`
  have hfun : (fun s => (1 / 2 : ℝ) * ‖(I.u s : L2VF_R3)‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * inner (𝕜 := ℝ) (I.u s : L2VF_R3) (I.u s : L2VF_R3) := by
    funext s
    rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  -- the derivative value: `½ * (⟪u,u'⟫ + ⟪u',u⟫) = -ν * viscousFormSq_R3 1 (u t)`
  have hval : (1 / 2 : ℝ) *
      (inner (𝕜 := ℝ) (I.u t : L2VF_R3) u' + inner (𝕜 := ℝ) u' (I.u t : L2VF_R3))
      = - ν * viscousFormSq_R3 1 (I.u t : L2VF_R3) := by
    have hcomm : inner (𝕜 := ℝ) (I.u t : L2VF_R3) u' = inner (𝕜 := ℝ) u' (I.u t : L2VF_R3) :=
      real_inner_comm _ _
    have heq : inner (𝕜 := ℝ) u' (I.u t : L2VF_R3)
        = - (ν * viscousFormSq_R3 1 (I.u t : L2VF_R3)) := by
      linarith [hode]
    rw [hcomm, heq]; ring
  rw [← hval]
  exact hinner.const_mul (1 / 2 : ℝ)

/-! ### E2 — the uniform energy bound (→ `energy_bound` field) -/

/-- Uniform energy bound: `½‖u(t)‖² ≤ ½‖𝔊.P n u₀‖²` for `t ≥ 0`. -/
theorem galerkin_energy_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ) (I : GalerkinODEInput 𝔊 F ν u₀ n)
    (t : Time) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) * ‖(I.u t : L2VF_R3)‖ ^ 2 ≤
    (1 / 2 : ℝ) * ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 := by
  -- the energy `E s := ½‖u s‖²` is antitone on forward time `Ici 0`
  -- (derivative `= -ν·viscousFormSq ≤ 0`); forward-only since E1 holds only for `s ≥ 0`.
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖(I.u s : L2VF_R3)‖ ^ 2 with hE
  have hanti : AntitoneOn E (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun s => - ν * viscousFormSq_R3 1 (I.u s : L2VF_R3)) ?_ ?_ ?_
    · -- continuity of `E` on `Ici 0` from forward differentiability
      intro x hx
      have hx0 : 0 ≤ x := hx
      exact (galerkin_energy_identity 𝔊 F ν u₀ n I x hx0).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 ≤ x := le_of_lt hx
      exact (galerkin_energy_identity 𝔊 F ν u₀ n I x hx0).hasDerivWithinAt
    · intro x _
      simp only [neg_mul]
      have : 0 ≤ ν * viscousFormSq_R3 1 (I.u x : L2VF_R3) :=
        mul_nonneg hν.le (viscousFormSq_R3_nonneg zero_le_one _)
      linarith
  -- `E t ≤ E 0`
  have h0 : E t ≤ E 0 := hanti (Set.self_mem_Ici) ht ht
  -- `E 0 = ½‖𝔊.P n u₀‖²` via `u_initial`
  have hinit : E 0 = (1 / 2 : ℝ) * ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 := by
    rw [hE]; simp only; rw [I.u_initial]
  rw [hinit] at h0
  exact h0

/-! ### E3 — the uniform dissipation bound (→ `reg_bound` field) -/

/-- Uniform (n-independent, `T`-independent) dissipation bound:
`∫₀ᵀ viscousFormSq_R3 ν (u t) dt ≤ ½‖u₀‖²`.  Since `viscousFormSq_R3` already carries the
`ν` factor (`= ν · ‖∇u‖²`), this RHS is `ν`-independent. -/
theorem galerkin_reg_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (_hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ) (I : GalerkinODEInput 𝔊 F ν u₀ n)
    (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, viscousFormSq_R3 ν (I.u t : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  -- the energy `E s := ½‖u s‖²` and its negation `g := -E`
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖(I.u s : L2VF_R3)‖ ^ 2 with hE
  -- `E 0 = ½‖𝔊.P n u₀‖² ≤ ½‖u₀‖²`
  have hE0 : E 0 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
    have hinit : E 0 = (1 / 2 : ℝ) * ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 := by
      rw [hE]; simp only; rw [I.u_initial]
    rw [hinit]
    have hle : ‖𝔊.P n (u₀ : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := 𝔊.norm_le n (u₀ : L2VF_R3)
    have : ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    linarith
  -- `E T ≥ 0`
  have hET : 0 ≤ E T := by
    rw [hE]; positivity
  -- case split on integrability of the dissipation; if non-integrable, the integral is 0
  by_cases hint : IntervalIntegrable
      (fun t => viscousFormSq_R3 ν (I.u t : L2VF_R3)) volume (0 : ℝ) T
  · -- FTC (one-sided, requiring only the integrand — not `E'` — to be integrable)
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) T,
        HasDerivWithinAt (fun s => - E s)
          (ν * viscousFormSq_R3 1 (I.u x : L2VF_R3)) (Set.Ioi x) x := by
      intro x hx
      have hx0 : 0 ≤ x := le_of_lt hx.1
      have hd : HasDerivAt E (- ν * viscousFormSq_R3 1 (I.u x : L2VF_R3)) x :=
        galerkin_energy_identity 𝔊 F ν u₀ n I x hx0
      have hneg : HasDerivAt (fun s => - E s)
          (ν * viscousFormSq_R3 1 (I.u x : L2VF_R3)) x := by
        have := hd.neg
        rwa [neg_mul, neg_neg] at this
      exact hneg.hasDerivWithinAt
    have hcont : ContinuousOn (fun s => - E s) (Set.Icc (0 : ℝ) T) := by
      apply ContinuousOn.neg
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      exact (galerkin_energy_identity 𝔊 F ν u₀ n I x hx0).continuousAt.continuousWithinAt
    have hφint : MeasureTheory.IntegrableOn
        (fun t => viscousFormSq_R3 ν (I.u t : L2VF_R3)) (Set.Icc (0 : ℝ) T) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1 hint
    have hle := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT.le hcont hderiv hφint
      (fun x _ => by rw [viscousFormSq_R3_eq_smul]; rfl)
    -- `∫ φ ≤ (-E T) - (-E 0) = E 0 - E T ≤ E 0 ≤ ½‖u₀‖²`
    have : (∫ y in (0:ℝ)..T, viscousFormSq_R3 ν (I.u y : L2VF_R3)) ≤ E 0 - E T := by
      have heq : (fun s => - E s) T - (fun s => - E s) 0 = E 0 - E T := by simp; ring
      rw [heq] at hle; exact hle
    linarith
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-! ### D — the deliverable -/

/-- **Deliverable.** From the isolated global-existence/representation input, assemble the
full `GalerkinSolutionData_R3`: the curve, its initial value, subspace confinement,
differentiability, the weak ODE, H¹ regularity, and the uniform energy + dissipation
bounds — the last three DERIVED axiom-free from the ODE via `R3NSForms.b_self_zero`.  This is
the axiom-free analytic content of `galerkin_ode_solution_R3`, modulo the bundled input.

The first five fields are passed straight from the input (they are what an existence theorem
supplies); `reg_mem`/`energy_bound`/`reg_bound` are the proved payoff (M0/E2/E3).  Field
types match `GalerkinSolutionData_R3` byte-for-byte (the structure is NOT altered).

This is a `noncomputable def` (not `theorem`): `GalerkinSolutionData_R3` is a data-carrying
structure in `Type`, not a `Prop`. -/
noncomputable def galerkinSolutionData_R3_of_input
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (I : GalerkinODEInput 𝔊 F ν u₀ n) :
    GalerkinSolutionData_R3 𝔊 F ν u₀ n := by
  exact
    { u := I.u
      u_initial := I.u_initial
      u_inVn := I.u_inVn
      u_hasDeriv := I.u_hasDeriv
      u_ode := I.u_ode
      reg_mem := fun t => galerkinCurve_reg_mem 𝔊 n (I.u t : L2VF_R3) (I.u_inVn t)
      viscous_curve_continuous := I.viscous_curve_continuous
      energy_bound := fun t ht => galerkin_energy_bound 𝔊 F ν hν u₀ n I t ht
      reg_bound := fun T hT => galerkin_reg_bound 𝔊 F ν hν u₀ n I T hT }

end LerayHopf
