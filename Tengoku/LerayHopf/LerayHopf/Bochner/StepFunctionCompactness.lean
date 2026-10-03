/-
# LerayHopf.Bochner.StepFunctionCompactness — Issue #46 PR-1 (File A)

**Goal:** Generic step-curve compactness machinery in the Bochner space
`Lp X 2 (volume.restrict (Set.Icc 0 T))`, for `X` a (complete, where needed)
`NormedAddCommGroup`.  This is the abstract half of the "good-sampling" Simon
compactness route that discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File A):

1. piecewise-constant curves on the uniform mesh `T/m` (`stepCurve`),
2. membership `MemLp (stepCurve …) 2 μ_T` and difference plumbing,
3. compactness in `Lp X 2 μ_T` of the set of all mesh-`m` step curves with
   values in a fixed compact `K ⊆ X`,
4. total-boundedness transfer under uniform ε-approximation,
5. sequential extraction: a totally bounded `toLp`-range yields a subsequence
   with `eLpNorm (f (ρ j) - G) 2 μ_T → 0`.

The file is **domain-neutral and mathlib-only** (no `LerayHopf.R3.*` /
`LerayHopf.Torus*` imports), so it is directly reusable for the torus-#23
spacetime compactness.

**A5 decision (per plan §3, task A5):** we keep this file mathlib-only and
therefore state `totallyBounded_of_uniform_approx'` as a FRESH copy of the
public `totallyBounded_of_uniform_approx` (`LerayHopf/R3/FrechetKolmogorov.lean:1806`),
rather than importing `LerayHopf.R3.FrechetKolmogorov` (which would drag the
whole R3 Fourier stack into a generic Bochner file and break torus reuse).
The ~15-line proof is duplicated by design; see the plan's fresh-build note (§2).

## Declarations (dependency order)

- `stepCurve`                       : A1 — piecewise-constant curve on mesh `T/m` (def, fully implemented)
- `stepCurve_memLp`                 : A2 — `MemLp (stepCurve T m y) 2 μ_T`
- `stepCurve_sub_memLp`             : A3 — difference of a `MemLp` curve and a step curve is `MemLp`
- `dist_toLp_stepCurve`             : A3 — `Lp`-distance to a step curve = `toReal` of the difference `eLpNorm`
- `isCompact_stepCurve_toLp`        : A4 — the mesh-`m` step curves valued in a compact `K` form a compact subset of `Lp X 2 μ_T`
- `totallyBounded_of_uniform_approx'` : A5 — total-boundedness transfer (fresh mathlib-only copy)
- `exists_subseq_tendsto_eLpNorm_of_totallyBounded` : A6 — sequential eLpNorm extraction from a totally bounded `toLp`-range

Dependency edges: A1 → A2 → A3, A4; A5, A6 independent of A1–A4.

## Assumptions

No axioms are introduced by this file (`axiom` count: 0), and the file is
`sorry`-free (0 `sorry`): all PR-1 scaffold placeholders (A2–A6) have been
discharged by `lean-prover`.
-/

import Tengoku.MeasureTheory.Function.LpSpace.Basic
-- Deviation from the scaffold's import list (recorded per task instruction): A6's proof
-- upgrades the totally bounded closure to a COMPACT set, which needs the completeness
-- instance `Lp.instCompleteSpace` — that instance lives in `LpSpace.Complete`, not in
-- `LpSpace.Basic`.  Mathlib-only, so the file stays domain-neutral (header contract intact).
import Tengoku.MeasureTheory.Function.LpSpace.Complete
import Tengoku.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Topology.Sequences

namespace LerayHopf

open MeasureTheory Filter Topology

variable {X : Type*} [NormedAddCommGroup X]

/-! ### A1 — the piecewise-constant step curve on the uniform mesh `T/m` -/

/-- **A1.** The piecewise-constant **step curve** on `[0, T]` with mesh `δ = T/m` and
values `y : Fin m → X`: on the `i`-th cell `[i·T/m, (i+1)·T/m)` it takes the value `y i`
(the last cell absorbs `t = T` and everything beyond via the `min · (m-1)` clamp; for
`t < 0` the floor clamps to the cell `0`).  For the degenerate mesh `m = 0` the curve is
constantly `0` (there is no data to sample; all consumers assume `0 < m`).

Concretely, the cell index is `min ⌊t·m/T⌋₊ (m − 1)`. -/
noncomputable def stepCurve (T : ℝ) (m : ℕ) (y : Fin m → X) : ℝ → X := fun t =>
  if hm : 0 < m then
    y ⟨min ⌊t * (m : ℝ) / T⌋₊ (m - 1),
       lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩
  else 0

/-! ### Local helpers for A2/A4 (measurability and evaluation of the step curve) -/

/-- Local helper: `Nat.floor : ℝ → ℕ` is measurable.  Fresh inline proof (fiber-wise:
the fiber over `0` is `Iio 1`, the fiber over `n ≠ 0` is `Ico n (n+1)`), keeping this
file free of the `Mathlib.MeasureTheory.Function.Floor` import. -/
private theorem measurable_natFloor_real : Measurable (fun x : ℝ => ⌊x⌋₊) := by
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (fun x : ℝ => ⌊x⌋₊) ⁻¹' {0} = Set.Iio 1 := by
      ext x
      simp
    rw [h]
    exact measurableSet_Iio
  · have h : (fun x : ℝ => ⌊x⌋₊) ⁻¹' {n} = Set.Ico (n : ℝ) ((n : ℝ) + 1) := by
      ext x
      simp [Nat.floor_eq_iff' hn.ne']
    rw [h]
    exact measurableSet_Ico

/-- Local helper: evaluation of the step curve for a positive mesh count. -/
private theorem stepCurve_apply {T : ℝ} {m : ℕ} (hm : 0 < m) (y : Fin m → X) (t : ℝ) :
    stepCurve T m y t
      = y ⟨min ⌊t * (m : ℝ) / T⌋₊ (m - 1),
           lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩ :=
  dite_eq_left hm

/-- Local helper: the step curve is strongly measurable — it is the composition of the
(discrete-target, hence strongly measurable) sampling map `ℕ → X` with the measurable
cell-index map `t ↦ ⌊t·m/T⌋₊`. -/
private theorem stepCurve_stronglyMeasurable (T : ℝ) {m : ℕ} (hm : 0 < m) (y : Fin m → X) :
    StronglyMeasurable (stepCurve T m y) := by
  have hg : StronglyMeasurable fun k : ℕ =>
      y ⟨min k (m - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩ :=
    StronglyMeasurable.of_discrete
  have hidx : Measurable fun t : ℝ => ⌊t * (m : ℝ) / T⌋₊ :=
    measurable_natFloor_real.comp ((measurable_id.mul_const (m : ℝ)).div_const T)
  have hfun : stepCurve T m y = (fun k : ℕ =>
      y ⟨min k (m - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩)
      ∘ fun t : ℝ => ⌊t * (m : ℝ) / T⌋₊ :=
    funext fun t => stepCurve_apply hm y t
  rw [hfun]
  exact hg.comp_measurable hidx

/-! ### A2/A3 — Lp membership and difference plumbing -/

/-- **A2.** A step curve is in `L²(0,T; X)`: it takes finitely many values on the finite
measure space `volume.restrict (Icc 0 T)`, hence is (strongly measurable and) `MemLp` at
exponent `2`. -/
theorem stepCurve_memLp (T : ℝ) (_hT : 0 < T) (m : ℕ) (hm : 0 < m) (y : Fin m → X) :
    MemLp (stepCurve T m y) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  refine MemLp.of_bound (stepCurve_stronglyMeasurable T hm y).aestronglyMeasurable
    (∑ i : Fin m, ‖y i‖) (ae_of_all _ fun t => ?_)
  rw [stepCurve_apply hm y t]
  exact Finset.single_le_sum (fun i _ => norm_nonneg (y i)) (Finset.mem_univ _)

/-- **A3 (membership half).** The difference of an `L²(0,T; X)` curve and a step curve is
again in `L²(0,T; X)` (both terms are `MemLp`, and `MemLp` is closed under subtraction). -/
theorem stepCurve_sub_memLp (T : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m) (y : Fin m → X)
    {f : ℝ → X} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    MemLp (fun t => f t - stepCurve T m y t) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) :=
  hf.sub (stepCurve_memLp T hT m hm y)

/-- **A3 (eLpNorm half).** The `Lp`-distance between the `toLp` classes of an `L²` curve and
a step curve is the `toReal` of the `eLpNorm` of the pointwise difference.  This is the
bridge from metric estimates in `Lp X 2 μ_T` (A4/A5/A6) back to the concrete
`eLpNorm`-of-difference form used by the axiom's conclusion. -/
theorem dist_toLp_stepCurve (T : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m) (y : Fin m → X)
    {f : ℝ → X} (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    dist (hf.toLp f) ((stepCurve_memLp T hT m hm y).toLp (stepCurve T m y))
      = (eLpNorm (fun t => f t - stepCurve T m y t) 2
          (volume.restrict (Set.Icc (0 : ℝ) T))).toReal := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf (stepCurve_memLp T hT m hm y), Lp.norm_toLp]
  congr 1

/-! ### A4 — compactness of the mesh-`m` step-curve set -/

/-- **A4.** For a compact `K ⊆ X`, the set of `toLp` classes of all mesh-`m` step curves
with values in `K` is COMPACT in `Lp X 2 μ_T`.

Route (plan §3 A4): the assembly map `y ↦ (stepCurve_memLp …).toLp` is Lipschitz from
`Fin m → X` with the sup metric (`‖stepCurve y − stepCurve y'‖_{L²} ≤ √T · max_i ‖y i − y' i‖`),
and `{y | ∀ i, y i ∈ K}` is compact (`IsCompact.pi` on `Set.pi Set.univ (fun _ => K)`), so the
image is compact by `IsCompact.image`. -/
theorem isCompact_stepCurve_toLp (T : ℝ) (hT : 0 < T) (m : ℕ) (hm : 0 < m)
    {K : Set X} (hK : IsCompact K) :
    IsCompact ((fun y : Fin m → X =>
        (stepCurve_memLp T hT m hm y).toLp (stepCurve T m y)) ''
      {y : Fin m → X | ∀ i, y i ∈ K}) := by
  set μT := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  -- Lipschitz bound for the assembly map `y ↦ toLp (stepCurve T m y)`.
  have hbound : ∀ y y' : Fin m → X,
      dist ((stepCurve_memLp T hT m hm y).toLp (stepCurve T m y))
          ((stepCurve_memLp T hT m hm y').toLp (stepCurve T m y'))
        ≤ (μT Set.univ ^ (2 : ENNReal).toReal⁻¹).toReal * dist y y' := by
    intro y y'
    -- pointwise sup-metric bound on the difference of the two step curves
    have hae : ∀ᵐ t ∂μT, ‖(stepCurve T m y - stepCurve T m y') t‖ ≤ dist y y' :=
      ae_of_all _ fun t => by
        rw [Pi.sub_apply, stepCurve_apply hm y t, stepCurve_apply hm y' t, ← dist_eq_norm]
        exact dist_le_pi_dist y y' _
    have hle : eLpNorm (stepCurve T m y - stepCurve T m y') 2 μT
        ≤ μT Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal (dist y y') :=
      eLpNorm_le_of_ae_bound hae
    have hμfin : μT Set.univ ≠ ⊤ := by
      rw [hμT, Measure.restrict_apply_univ]
      exact measure_Icc_lt_top.ne
    have hfin : μT Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal (dist y y') ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμfin)
        ENNReal.ofReal_ne_top
    have hdist : dist ((stepCurve_memLp T hT m hm y).toLp (stepCurve T m y))
        ((stepCurve_memLp T hT m hm y').toLp (stepCurve T m y'))
        = (eLpNorm (stepCurve T m y - stepCurve T m y') 2 μT).toReal := by
      rw [dist_eq_norm,
        ← MemLp.toLp_sub (stepCurve_memLp T hT m hm y) (stepCurve_memLp T hT m hm y'),
        Lp.norm_toLp]
    rw [hdist]
    calc (eLpNorm (stepCurve T m y - stepCurve T m y') 2 μT).toReal
        ≤ (μT Set.univ ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal (dist y y')).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = (μT Set.univ ^ (2 : ENNReal).toReal⁻¹).toReal * dist y y' := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg]
  -- the assembly map is Lipschitz, hence continuous
  have hlip : LipschitzWith (μT Set.univ ^ (2 : ENNReal).toReal⁻¹).toNNReal
      (fun y : Fin m → X => (stepCurve_memLp T hT m hm y).toLp (stepCurve T m y)) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    have hcoe : (((μT Set.univ ^ (2 : ENNReal).toReal⁻¹).toNNReal : NNReal) : ℝ)
        = (μT Set.univ ^ (2 : ENNReal).toReal⁻¹).toReal := rfl
    rw [hcoe]
    exact hbound y y'
  -- compactness of the parameter set + continuity of the assembly map
  have hset : {y : Fin m → X | ∀ i, y i ∈ K} = Set.pi Set.univ (fun _ : Fin m => K) := by
    ext y
    simp
  rw [hset]
  exact (isCompact_univ_pi fun _ : Fin m => hK).image hlip.continuous

/-! ### A5 — total-boundedness transfer under uniform approximation -/

/-- **A5.** Total-boundedness transfer: in a pseudometric space, a set `S` that is, for
EVERY `ε > 0`, uniformly ε-approximable by a totally bounded set is itself totally bounded
(an ε-net of the approximant, fattened by ε, is a 2ε-net of `S`).

FRESH mathlib-only copy of the public `totallyBounded_of_uniform_approx`
(`LerayHopf/R3/FrechetKolmogorov.lean:1806`), duplicated by design so this file stays free
of R3 imports (plan §2 fresh-build note; A5 decision recorded in the file header). -/
theorem totallyBounded_of_uniform_approx' {α : Type*} [PseudoMetricSpace α] (S : Set α)
    (happrox : ∀ ε > 0, ∃ A : Set α, TotallyBounded A ∧
      ∀ s ∈ S, ∃ a ∈ A, dist s a < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Approximate `S` within `ε/2` by a totally bounded `A`.
  obtain ⟨A, hA, hAapprox⟩ := happrox (ε / 2) (by linarith)
  -- A finite `ε/2`-net `t` of `A`.
  obtain ⟨t, ht_fin, ht_cover⟩ := (Metric.totallyBounded_iff.mp hA) (ε / 2) (by linarith)
  -- `t` is an `ε`-net of `S` by the triangle inequality.
  refine ⟨t, ht_fin, fun s hs => ?_⟩
  obtain ⟨a, haA, hsa⟩ := hAapprox s hs
  have ha_mem : a ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := ht_cover haA
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ha_mem ⊢
  obtain ⟨y, hyt, hay⟩ := ha_mem
  refine ⟨y, hyt, ?_⟩
  calc dist s y ≤ dist s a + dist a y := dist_triangle s a y
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ### A6 — sequential eLpNorm extraction -/

/-- **A6.** Sequential extraction from a totally bounded `toLp`-range: if the curves
`f n : ℝ → X` are `L²(0,T; X)` and their `toLp` classes form a totally bounded subset of the
COMPLETE space `Lp X 2 μ_T`, then some subsequence converges in `Lp`, i.e. there are a
strictly monotone `ρ` and a limit `G : Lp X 2 μ_T` with
`eLpNorm (f (ρ j) − G) 2 μ_T → 0`.

Route (plan §3 A6): `TotallyBounded.closure` + completeness make the closure of the range
compact; `IsCompact.tendsto_subseq` extracts `ρ` and `G`; `Lp.norm_def` plus the
`coeFn`-congruences `(hf n).coeFn_toLp` / `Lp.coeFn_sub` and an `ENNReal.toReal` conversion
turn norm convergence into the stated `eLpNorm` convergence (all eLpNorms are finite). -/
theorem exists_subseq_tendsto_eLpNorm_of_totallyBounded [CompleteSpace X]
    (T : ℝ) (f : ℕ → ℝ → X)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (htb : TotallyBounded (Set.range fun n => (hf n).toLp (f n))) :
    ∃ (ρ : ℕ → ℕ) (G : Lp X 2 (volume.restrict (Set.Icc (0 : ℝ) T))),
      StrictMono ρ ∧
      Filter.Tendsto
        (fun j => eLpNorm (fun t => f (ρ j) t - G t) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0) := by
  set μT := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  -- the closure of the `toLp` range is compact (complete ambient space)
  have hcpt : IsCompact (closure (Set.range fun n => (hf n).toLp (f n))) :=
    isCompact_iff_totallyBounded_isComplete.mpr
      ⟨htb.closure, isClosed_closure.isComplete⟩
  obtain ⟨G, -, ρ, hρ, htend⟩ := hcpt.tendsto_subseq
    (x := fun n => (hf n).toLp (f n)) fun n => subset_closure (Set.mem_range_self n)
  refine ⟨ρ, G, hρ, ?_⟩
  -- Lp-norm convergence of the subsequence
  have hnorm0 : Filter.Tendsto (fun j => ‖(hf (ρ j)).toLp (f (ρ j)) - G‖)
      Filter.atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.mp htend
  -- identify the Lp norm of the difference with the eLpNorm of the pointwise difference
  have hnormeq : ∀ j, ‖(hf (ρ j)).toLp (f (ρ j)) - G‖
      = (eLpNorm (fun t => f (ρ j) t - G t) 2 μT).toReal := by
    intro j
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((hf (ρ j)).toLp (f (ρ j))) G, (hf (ρ j)).coeFn_toLp]
      with t h1 h2
    rw [h1, Pi.sub_apply, h2]
  have htoReal : Filter.Tendsto
      (fun j => (eLpNorm (fun t => f (ρ j) t - G t) 2 μT).toReal)
      Filter.atTop (nhds 0) := hnorm0.congr fun j => hnormeq j
  -- all difference eLpNorms are finite, so `toReal → 0` upgrades to `eLpNorm → 0`
  have hfin : ∀ j, eLpNorm (fun t => f (ρ j) t - G t) 2 μT ≠ ⊤ := by
    intro j
    have h := ((hf (ρ j)).sub (Lp.memLp G)).eLpNorm_ne_top
    have heq : eLpNorm (f (ρ j) - fun t => G t) 2 μT
        = eLpNorm (fun t => f (ρ j) t - G t) 2 μT :=
      eLpNorm_congr_ae (Filter.Eventually.of_forall fun t => rfl)
    rw [← heq]
    exact h
  have hofReal := ENNReal.tendsto_ofReal htoReal
  rw [ENNReal.ofReal_zero] at hofReal
  exact hofReal.congr fun j => ENNReal.ofReal_toReal (hfin j)

end LerayHopf
