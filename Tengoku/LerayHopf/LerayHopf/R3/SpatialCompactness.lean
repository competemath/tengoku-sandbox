import Tengoku.LerayHopf.LerayHopf.R3.Regularity
import Tengoku.Topology.Sequences
import Tengoku.MeasureTheory.Function.L2Space
import Tengoku.MeasureTheory.Integral.Bochner.Set

namespace LerayHopf
open MeasureTheory Filter Topology Metric

/-!
# LOCAL spatial compactness on ℝ³ — axiom-free reduction (P3)

**Milestone:** `p3-spatial-compactness`

This file substantiates — axiom-free and (once `lean-prover` fills the bodies)
sorry-free — the analytic content of the `spatial_compactness_R3` axiom in
`SolutionInterfaces.lean:378–389`.  It *reproduces* that axiom's exact conclusion
shape from ONE clean isolated hypothesis, `LocalRellichInput`, which captures the
genuine analytic frontier.

## Architecture (standalone)

This file is **standalone**: it does **not** import `R3.SolutionInterfaces.lean`, and is
**not** imported by it.  The connection to the axiom is *semantic* (the deliverable's
conclusion is byte-identical to the axiom body, plus a `(B : LocalRellichInput)` binder),
exactly as R3-d (`TrilinearEstimate.lean`) and P5 (`GalerkinScheme.lean`) did.  It does
NOT remove the axiom; it is a sibling proved lemma.

The single isolated frontier is `LocalRellichInput.ballCompact`: the LOCAL compact
embedding `H¹(B_R) ↪↪ L²(B_R)` (Leray 1934; Lemarié-Rieusset §6), which mathlib lacks (no
Rellich–Kondrachov, no compact-embedding API, no Fréchet–Kolmogorov).  **This milestone
proves the reduction AROUND that embedding — the diagonal extraction over growing balls,
the limit assembly, and the divergence-free closure — NOT the embedding itself.**

DAG position:
```
R3/Domain.lean
    └── R3/DivergenceFree.lean
            └── R3/Regularity.lean   (memH1VF_R3, viscousFormSq_R3)
                    └── R3/SpatialCompactness.lean   [THIS FILE]
                            (standalone; NOT importing R3/SolutionInterfaces.lean)
```
Sibling of `R3/SolutionInterfaces.lean`, not a dependency of it.  Added to root `LerayHopf.lean`.

## Declarations (dependency order)

- `LocalRellichInput`                              : isolated analytic frontier (one field, `ballCompact`)
- `L2ballR3`                                       : D0a — L²(B_R) over the restricted measure
- `restrictToBall`                                 : D0b — restriction map `L2VF_R3 → L2ballR3 R`
- `setIntegral_normSq_eq_dist_sq_restrictToBall`   : D0c — bridge: ball ∫‖·‖² = L²(B_R) dist²
- `exists_subseq_tendsto_on_ball`                  : D1 — per-ball subsequence extraction
- `exists_subseq_tendsto_on_all_balls`             : D2 — diagonal over expanding balls
- `ballLimits_are_consistent`                      : D3a — per-ball limits are mutually consistent
- `ballLimit_global_mem_L2Sigma`                   : D3b — assembled global limit is div-free
- `localCompactness_R3_of_ballCompact`             : D4 — DELIVERABLE (≡ `spatial_compactness_R3`)

## Assumptions

Zero new `axiom`/`opaque`/`constant`.  The genuine frontier is carried by the **hypothesis**
`LocalRellichInput` (an explicit argument), exactly as R3-d's `hdiv` and P5's
`SchwartzGalerkinBasis.dense_span`.  A hypothesis is not an axiom.
-/

/-! ### Tier 0 — restriction plumbing -/

/-- **D0a.** L²(B_R): the Lp space over the volume measure restricted to the closed ball
of radius `R`.  This is the carrier that supplies a usable metric for
`IsCompact.tendsto_subseq`. -/
noncomputable abbrev L2ballR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R))

/-- **D0b.** Restriction of an L²(ℝ³) velocity field to the ball `B_R`, as an element of
`L2ballR3 R`.

Goes through the underlying a.e.-function: `MemLp.restrict (Lp.memLp w)` gives
`MemLp (w : Domain3 → _) 2 (volume.restrict (closedBall 0 R))`, and `MemLp.toLp` packages it.
(Restriction is not measure-preserving, so `Lp.compMeasurePreserving` is not applicable —
G1.) -/
noncomputable def restrictToBall (R : ℝ) (w : L2VF_R3) : L2ballR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R))

/-- Isolated analytic frontier: LOCAL compact embedding `H¹(B_R) ↪↪ L²(B_R)`.

For every radius `R` and every uniform bound `M`, the image under restriction-to-`B_R`
of the L²/H¹-bounded div-free family is contained in a COMPACT subset of `L²(B_R)`.

This is the unconditional local Rellich theorem (Leray 1934; Lemarié-Rieusset §6). It is
NOT provable in current mathlib (no Rellich / compact embedding / Fréchet–Kolmogorov).

Honesty (no-smuggle): the hypothesis speaks ONLY ball-by-ball and ONLY supplies
precompactness of a SET in a SINGLE L²(B_R); it provides NEITHER a subsequence, NOR a
limit, NOR cross-ball coherence, NOR div-freeness. All of those are derived axiom-free in
the reduction below. -/
structure LocalRellichInput where
  ballCompact : ∀ (M : ℝ) (R : ℝ),
    ∃ K : Set (L2ballR3 R), IsCompact K ∧
      ∀ (w : L2VF_R3), w ∈ L2Sigma_R3 → memH1VF_R3 w →
        ‖w‖ ≤ M → viscousFormSq_R3 1 w ≤ M ^ 2 →
        restrictToBall R w ∈ K

/-- L²-norm-squared as an integral of the pointwise squared norm, for an element of an
`L²` space over a real inner-product target. -/
theorem normSq_eq_integral_normSq {μ : Measure Domain3}
    (h : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ) :
    ‖h‖ ^ 2 = ∫ x, ‖(h x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂μ := by
  have hre : ‖h‖ ^ 2 = (inner ℝ h h : ℝ) := by
    have := norm_sq_eq_re_inner (𝕜 := ℝ) h
    simp
  rw [hre, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact real_inner_self_eq_norm_sq _

/-- **D0c.** The ball set-integral of the squared difference equals the squared
L²(B_R)-distance of the two restrictions. This is the bridge between the conclusion's
set-integral shape and the metric in which `IsCompact.tendsto_subseq` produces convergence. -/
theorem setIntegral_normSq_eq_dist_sq_restrictToBall (R : ℝ) (u v : L2VF_R3) :
    ∫ x in Metric.closedBall (0 : Domain3) R,
      ‖(u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
      ∂(volume : Measure Domain3)
    = dist (restrictToBall R u) (restrictToBall R v) ^ 2 := by
  set μ : Measure Domain3 := volume.restrict (Metric.closedBall (0 : Domain3) R) with hμ
  rw [dist_eq_norm, normSq_eq_integral_normSq (restrictToBall R u - restrictToBall R v)]
  -- the integral over `volume.restrict ball` is the set integral over the ball
  show ∫ x in Metric.closedBall (0 : Domain3) R,
      ‖(u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂volume
    = ∫ x,
      ‖((restrictToBall R u - restrictToBall R v) x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂μ
  rw [hμ]
  refine integral_congr_ae ?_
  have hsub : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[μ] (fun x => (restrictToBall R u) x - (restrictToBall R v) x) :=
    Lp.coeFn_sub _ _
  have hu : ⇑(restrictToBall R u) =ᵐ[μ] (u : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
    MemLp.coeFn_toLp _
  have hv : ⇑(restrictToBall R v) =ᵐ[μ] (v : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
    MemLp.coeFn_toLp _
  filter_upwards [hsub, hu, hv] with x hxsub hxu hxv
  rw [hxsub, hxu, hxv]

/-! ### Tier 1 — per-ball subsequence extraction -/

/-! ### Tier 2 — diagonal over expanding balls (structural core) -/

/-- Factorization of a nested family of extractions: if `Φ (k+1) = Φ k ∘ ρ k` with each
`ρ k` strictly monotone, then for `k ≤ n` the extraction `Φ n` is `Φ k` post-composed with a
strictly monotone map. -/
theorem nested_extraction_factor (Φ ρ : ℕ → ℕ → ℕ)
    (hρ : ∀ k, StrictMono (ρ k)) (hstep : ∀ k, Φ (k + 1) = Φ k ∘ ρ k) :
    ∀ k n, k ≤ n → ∃ R : ℕ → ℕ, StrictMono R ∧ Φ n = Φ k ∘ R := by
  intro k n hkn
  induction n with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hkn
    exact ⟨id, strictMono_id, rfl⟩
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · obtain ⟨R, hR, hReq⟩ := ih (Nat.lt_succ_iff.mp hlt)
      refine ⟨R ∘ ρ m, hR.comp (hρ m), ?_⟩
      rw [hstep m, hReq]
      rfl
    · obtain rfl : k = m + 1 := Nat.le_antisymm hkn hge
      exact ⟨id, strictMono_id, rfl⟩

/-! ### Tier 3 — limit assembly + div-free closure -/

/-- Further restriction of an `L²(B_k)` element to a smaller ball `B_R` (`R ≤ k`), through the
underlying a.e. function.  This is well-defined because `volume.restrict (B_R) ≤
volume.restrict (B_k)`. -/
private noncomputable def furtherRestrict (R k : ℝ) (h : (R : ℝ) ≤ k)
    (w : L2ballR3 k) : L2ballR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    (by
      have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
        Metric.closedBall_subset_closedBall h
      have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)
          ≤ volume.restrict (Metric.closedBall (0 : Domain3) k) :=
        Measure.restrict_mono hsub le_rfl
      exact (Lp.memLp w).mono_measure hle)

/-- Restriction to a ball does not increase the L²-norm. -/
theorem norm_restrictToBall_le (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ≤ ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcong : ⇑(restrictToBall R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ hle)

/-- `restrictToBall R` sends `0` to `0`. -/
theorem restrictToBall_zero (R : ℝ) : restrictToBall R (0 : L2VF_R3) = 0 := by
  apply Lp.ext
  have h1 : ⇑(restrictToBall R (0 : L2VF_R3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    (Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)).restrict
  have hz0 : ⇑(0 : L2ballR3 R)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2)
      (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
  filter_upwards [h1, h0, hz0] with x hx hx0 hxz
  simp only [hx, hx0, hxz, Pi.zero_apply]

/-- `restrictToBall R (u - v) = restrictToBall R u - restrictToBall R v`. -/
theorem restrictToBall_sub (R : ℝ) (u v : L2VF_R3) :
    restrictToBall R (u - v) = restrictToBall R u - restrictToBall R v := by
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp ((Lp.memLp (u - v)).restrict (Metric.closedBall (0 : Domain3) R)),
    MemLp.coeFn_toLp ((Lp.memLp u).restrict (Metric.closedBall (0 : Domain3) R)),
    MemLp.coeFn_toLp ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)),
    Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v),
    ae_mono Measure.restrict_le_self (Lp.coeFn_sub u v)] with x h1 h2 h3 h4 h5
  -- Bridge definitional equality: restrictToBall R w = MemLp.toLp ↑↑w ... by def
  have eq1 : (↑↑(restrictToBall R (u - v)) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑(u - v) : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h1
  have eq2 : (↑↑(restrictToBall R u) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑u : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h2
  have eq3 : (↑↑(restrictToBall R v) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑v : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h3
  rw [eq1, h5]
  simp only [h4, Pi.sub_apply, eq2, eq3]

/-- `restrictToBall R` is `1`-Lipschitz on `L2VF_R3`. Used to obtain continuity, hence
time-measurability transport. -/
theorem restrictToBall_dist_le (R : ℝ) (u v : L2VF_R3) :
    dist (restrictToBall R u) (restrictToBall R v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  -- The underlying function of `restrictToBall R u - restrictToBall R v` agrees a.e. (on `B_R`)
  -- with `u - v`'s underlying function.
  have hcongR : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub := Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v)
    have hu : ⇑(restrictToBall R u)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (u : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R v)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (v : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongG : ⇑(u - v)
      =ᵐ[(volume : Measure Domain3)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) :=
    Lp.coeFn_sub u v
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongG]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongG]
  exact (Lp.memLp (u - v)).2.ne

/-- Continuity of `restrictToBall R : L2VF_R3 → L2ballR3 R` (it is `1`-Lipschitz). -/
theorem continuous_restrictToBall (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      ≤ dist w' w := restrictToBall_dist_le R w' w
    _ < ε := hw'

/-- The squared L²(B_R)-norm of `restrictToBall R w` equals the ball set-integral of `‖w·‖²`. -/
theorem normSq_restrictToBall_eq_setIntegral (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ^ 2
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖(w x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂(volume : Measure Domain3) := by
  -- Use the bridge with `v = 0`: `restrictToBall R 0 = 0`, so the ball integral of `‖w - 0‖²`
  -- equals `dist (restrictToBall R w) 0 ^ 2 = ‖restrictToBall R w‖²`.
  have hbridge := setIntegral_normSq_eq_dist_sq_restrictToBall R w 0
  rw [restrictToBall_zero, dist_zero_right] at hbridge
  -- Rewrite the integrand: `w x - (0 : L2VF_R3) x = w x` a.e.
  rw [← hbridge]
  refine setIntegral_congr_ae measurableSet_closedBall ?_
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)
  filter_upwards [h0] with x hx _
  rw [hx]; simp

/-- **Ball exhaustion for the Lebesgue integral.** The set-lintegral of a function over the
closed ball `B_k` increases to the full-space lintegral as `k → ∞`, because the balls
exhaust `ℝ³`. -/
private theorem tendsto_setLIntegral_closedBall (f : Domain3 → ENNReal) (hf : Measurable f) :
    Tendsto (fun k : ℕ => ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), f x ∂volume)
      atTop (𝓝 (∫⁻ x, f x ∂volume)) := by
  have hcov : ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) = Set.univ :=
    Metric.iUnion_closedBall_nat 0
  have hmeas : ∀ k : ℕ, MeasurableSet (Metric.closedBall (0 : Domain3) (k : ℝ)) :=
    fun k => measurableSet_closedBall
  -- rewrite each set-lintegral as a full lintegral of an indicator
  have hrw : ∀ k : ℕ, (∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), f x ∂volume)
      = ∫⁻ x, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x ∂volume := fun k =>
    (lintegral_indicator (hmeas k) f).symm
  simp only [hrw]
  -- and the full lintegral as the indicator of `univ`
  have hfull : (∫⁻ x, f x ∂volume)
      = ∫⁻ x, (fun x => ⨆ k : ℕ, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x) x
        ∂volume := by
    refine lintegral_congr fun x => ?_
    have hx : x ∈ ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) := by
      rw [hcov]; trivial
    obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hx
    refine le_antisymm ?_ ?_
    · refine le_iSup_of_le k₀ ?_
      rw [Set.indicator_of_mem hk₀]
    · refine iSup_le fun k => ?_
      exact Set.indicator_le_self _ f x
  rw [hfull]
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun k => ((hf.indicator (hmeas k)).aemeasurable)) ?_ ?_
  · refine Filter.Eventually.of_forall fun x a b hab => ?_
    have hsub : Metric.closedBall (0 : Domain3) (a : ℝ)
        ⊆ Metric.closedBall (0 : Domain3) (b : ℝ) :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    show (Metric.closedBall (0 : Domain3) (a : ℝ)).indicator f x
      ≤ (Metric.closedBall (0 : Domain3) (b : ℝ)).indicator f x
    by_cases ha : x ∈ Metric.closedBall (0 : Domain3) (a : ℝ)
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hsub ha)]
    · rw [Set.indicator_of_notMem ha]; exact bot_le
  · refine Filter.Eventually.of_forall fun x => ?_
    have hx : x ∈ ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) := by
      rw [hcov]; trivial
    obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hx
    -- eventually the indicator equals `f x`, so the sequence converges to the sup `f x`
    have hval : ⨆ k : ℕ, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x = f x := by
      refine le_antisymm (iSup_le fun k => Set.indicator_le_self _ f x) ?_
      exact le_iSup_of_le k₀ (by rw [Set.indicator_of_mem hk₀])
    rw [hval]
    refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
    have hmem : x ∈ Metric.closedBall (0 : Domain3) (k : ℝ) :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hk) hk₀
    rw [Set.indicator_of_mem hmem]

/-- **Textbook step (D3a helper).** The radial classification map `x ↦ ⌈dist x 0⌉₊`, used to
partition `Domain3` into the annuli `{c = j}` from which a single global representative is
assembled out of the per-ball limits `g k`. -/
private noncomputable def ballClassify (x : Domain3) : ℕ := ⌈dist x (0 : Domain3)⌉₊

/-! ### G5 helper lemmas — global div-free closure from local L² convergence

The `divTestFunctional φ w = ∑ j, ⟪(∂_j φ).toLp, projComponent_j w⟫_{L²(ℝ³)}` is a GLOBAL
L² inner product, but ball-restriction convergence is only LOCAL.  We close the gap with an
ε/3 ball-truncation, packaging `divTestFunctional φ` as a single global L²-vector inner
product `⟪gradVF φ, w⟫_{L2VF_R3}` against the gradient vector field `gradVF φ`. -/

/-- The **gradient vector field** of a Schwartz test `φ`, as an element of `L2VF_R3`:
`gradVF φ x = ∑ j, (∂_j φ)(x) • e_j = ∇φ(x)`.  Built by lifting each scalar component
`(∂_j φ).toLp` along `toSpanSingleton ℝ (e_j)`. -/
private noncomputable def gradVF (φ : SchwartzMap Domain3 ℝ) : L2VF_R3 :=
  ∑ j : Fin 3,
    (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).compLp
      ((LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp
        2 (volume : Measure Domain3))

/-- The j-th scalar component `(∂_j φ).toLp` used throughout. -/
private noncomputable def dphiLp (φ : SchwartzMap Domain3 ℝ) (j : Fin 3) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
      (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3)

/-- L²(B_Rᶜ): the carrier for the tail part of the truncation. -/
private noncomputable abbrev L2tailR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)

/-- Restriction of an L²(ℝ³) field to the tail `B_Rᶜ`, as an element of `L2tailR3 R`. -/
noncomputable def tailVF (R : ℝ) (w : L2VF_R3) : L2tailR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)

/-- The tail restriction does not increase the L²-norm. -/
theorem norm_tailVF_le (R : ℝ) (w : L2VF_R3) : ‖tailVF R w‖ ≤ ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcong : ⇑(tailVF R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ hle)

/-- **Ball/tail split** of the global L²-vector inner product:
`⟪v, w⟫ = ⟪restrictToBall R v, restrictToBall R w⟫ + ⟪tailVF R v, tailVF R w⟫`. -/
theorem inner_eq_ball_add_tail (R : ℝ) (v w : L2VF_R3) :
    (inner ℝ v w : ℝ)
      = (inner ℝ (restrictToBall R v) (restrictToBall R w) : ℝ)
        + (inner ℝ (tailVF R v) (tailVF R w) : ℝ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  -- the integrand for the ball/tail inner products agrees a.e. with `⟪v x, w x⟫`.
  have hball : (∫ x, (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)))
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R))] with x hxv hxw
    show (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ) = _
    rw [show ((restrictToBall R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((restrictToBall R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  have htail : (∫ x, (inner ℝ ((tailVF R v) x) ((tailVF R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ))
      = ∫ x in (Metric.closedBall (0 : Domain3) R)ᶜ,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)ᶜ),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)] with x hxv hxw
    show (inner ℝ ((tailVF R v) x) ((tailVF R w) x) : ℝ) = _
    rw [show ((tailVF R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((tailVF R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  rw [hball, htail]
  exact (integral_add_compl measurableSet_closedBall
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) v w)).symm

/-- **Tail-vanishing** of a fixed L² field: `‖tailVF R v‖ → 0` as `R → ∞`.

Proved via dominated/monotone convergence: `eLpNorm v 2 (B_Rᶜ-restricted)`'s square is the
set-lintegral over `B_Rᶜ` of `‖v ·‖ₑ²`, which decreases to the lintegral over `⋂_R B_Rᶜ = ∅`,
hence to `0`.  We obtain it from the ball-exhaustion `tendsto_setLIntegral_closedBall`: the
ball part increases to the full (finite) integral, so the complement part tends to `0`. -/
theorem tendsto_norm_tailVF_zero (v : L2VF_R3) :
    Tendsto (fun k : ℕ => ‖tailVF (k : ℝ) v‖) atTop (𝓝 0) := by
  classical
  set p2 : ℝ := (2 : ENNReal).toReal with hp2
  have hp2_eq : p2 = 2 := by simp [hp2]
  have hp2_pos : 0 < p2 := by rw [hp2_eq]; norm_num
  -- A measurable representative `v'` of `v` (a.e. equal under `volume`).
  obtain ⟨v', hv'_meas, hv'_ae⟩ := (Lp.memLp v).1
  set H : Domain3 → ENNReal := fun x => ‖v' x‖ₑ ^ p2 with hH
  have hH_meas : Measurable H := (hv'_meas.enorm).pow_const _
  -- `v =ᵐ v'` ⇒ `‖v·‖ₑ^p2 =ᵐ H`.
  have hHv : (fun x => ‖(v : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2) =ᵐ[volume] H := by
    filter_upwards [hv'_ae] with x hx; simp only [hH, hx]
  -- Full lintegral is finite (since `v ∈ L²`).
  have hI_lt : (∫⁻ x, H x ∂volume) < ⊤ := by
    have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)).1 (Lp.memLp v).2
    rw [← hp2] at hfin
    rwa [lintegral_congr_ae hHv.symm]
  set I : ENNReal := ∫⁻ x, H x ∂volume with hI
  -- Ball lintegrals of `H` increase to `I`; hence tail lintegrals tend to `0`.
  have hball := tendsto_setLIntegral_closedBall H hH_meas
  -- `Tk := ∫⁻_{B_kᶜ} H = I - (∫⁻_{B_k} H)`.
  have hTk_eq : ∀ k : ℕ,
      (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume)
        = I - ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume := by
    intro k
    have hbk_fin : (∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hI_lt.ne ?_
      exact setLIntegral_le_lintegral _ _
    rw [setLIntegral_compl measurableSet_closedBall hbk_fin]
  have hTk_tendsto : Tendsto
      (fun k : ℕ => ∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume)
      atTop (𝓝 0) := by
    have hsub : Tendsto
        (fun k : ℕ => I - ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume)
        atTop (𝓝 (I - I)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds hball (Or.inl hI_lt.ne)
    rw [tsub_self] at hsub
    exact (tendsto_congr hTk_eq).2 hsub
  -- `eLpNorm (tail of v) 2 volume = (Tk)^(1/p2)` (after a.e.-replacing `v` by `v'`).
  have heLp_eq : ∀ k : ℕ,
      eLpNorm v 2 (volume.restrict (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ)
        = (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← hp2]
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae hHv)
  -- Convert the ENNReal tail to its `toReal` and conclude the real limit.
  have hnorm_eq : ∀ k : ℕ, ‖tailVF (k : ℝ) v‖
      = ((∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2)).toReal := by
    intro k
    rw [tailVF, MeasureTheory.Lp.norm_toLp, heLp_eq k]
  rw [tendsto_congr hnorm_eq]
  -- `(Tk)^(1/p2) → 0^(1/p2) = 0` in ENNReal, then `.toReal → 0`.
  have hrpow : Tendsto
      (fun k : ℕ => (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2))
      atTop (𝓝 (0 : ENNReal)) := by
    have hcont : Continuous (fun t : ENNReal => t ^ (1 / p2)) :=
      ENNReal.continuous_rpow_const
    have hz : (0 : ENNReal) ^ (1 / p2) = 0 :=
      ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / p2)
    have := (hcont.tendsto 0).comp hTk_tendsto
    rw [hz] at this
    simpa [Function.comp_def] using this
  have := (ENNReal.tendsto_toReal (a := (0 : ENNReal)) (by simp)).comp hrpow
  simpa [Function.comp_def] using this

/-! ### Tier 4 — final packaging (the deliverable) -/

end LerayHopf
