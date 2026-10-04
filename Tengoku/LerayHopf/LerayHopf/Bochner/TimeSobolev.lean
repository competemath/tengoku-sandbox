/-
# LerayHopf.Bochner.TimeSobolev — abstract Bochner–Sobolev-in-time, Stages D1 + D2

Abstract Bochner–Sobolev-in-time / Gelfand-triple vocabulary and theorems (Stage D1: the
weak time derivative and the `W1pTime` bundle; Stage D2: the measurable-representative
primitives). This file is sorry-free — see "Scaffold ledger" below for what is proved.

This file is domain-neutral. It depends only on `LerayHopf.Bochner.GelfandTriple`
(itself depending only on `EvolutionTriple` + mathlib) and on mathlib's Bochner / `Lp` /
convergence-in-measure machinery. It does NOT import either `SolutionInterfaces.lean`, so it
introduces no import cycle and may be reused by both the T³ and ℝ³ capstones later.

## Stage D1 — vector-valued time-Sobolev objects

- `IsWeakTimeDeriv` — distributional (weak) time derivative of a Banach-valued curve, with
  the SAME test-function convention as `WeakFormNS` (`C¹`, compact support in `Ioo 0 T`).
- `isWeakTimeDeriv_unique` — a.e. uniqueness (must-prove; deferred body).
- `hasDerivAt_isWeakTimeDeriv` — a classical strong derivative is a weak time derivative
  (the entry point connecting Galerkin curves' `HasDerivAt` field to the weak API).
- `GelfandTriple.Vprime` — the continuous dual `V' := V →L[ℝ] ℝ` (`StrongDual ℝ V`).
- `GelfandTriple.hToVprime` — the canonical embedding `H → V'`, `h ↦ (v ↦ ⟪ι v, h⟫_H)`,
  i.e. the transpose of `ι` composed with the Riesz identification `H ≅ H'`.
- `W1pTime` — the abstract `W^{1,p}(0,T;V) ∩ {u' ∈ L^q(0,T;V')}` membership bundle. The
  time derivative is stored as a genuine `V'`-valued curve `u' ∈ L^q(0,T;V')` (Lions–Magenes
  / Gelfand-triple convention), NOT as an `H`-valued curve — requiring `u' ∈ H` would be
  strictly stronger and could exclude the actual Navier–Stokes weak time derivative.
- `W1pTime.ofHValuedDeriv` — the SEPARATE STRONGER specialization: an `H`-valued weak time
  derivative yields a `W1pTime` element (via the embedding `H ↪ V'`).

**Relocated and corrected (issues #147, #158):** `w1pTime_continuous_in_H` (the Lions–Magenes
good-representative embedding, a months-class residual) now lives in
`LerayHopf.Bochner.TimeSobolevExperimental`, so the release surface `import LerayHopf` stays
sorry-free. Its statement was also corrected there: the prior generic-`p,q` signature was
FALSE (issue #158, explicit `p = q = 1` counterexample) and is now restricted to `p = q = 2`,
the only case with an actual proof plan. Everything else in this file is unaffected — see
`LerayHopf/Experimental.lean` for the opt-in aggregator.

## Stage D2 — measurable representative primitive (KEY — unblocks P2's E1)

- `aeStronglyMeasurable_of_spaceTimeL2` — from L²-in-time convergence of an
  a.e.-strongly-measurable sequence to an **a.e.-strongly-measurable** limit `g`, there is an
  a.e.-convergent subsequence (and `g`'s representative is returned). **Statement-gate fix
  (Lane-D):** the measurability of `g` is an explicit hypothesis `hg`, not a conclusion — without
  it the statement is FALSE (Vitali-set counterexample in the theorem docstring), since L²-limit
  measurability cannot be extracted from L²-convergence alone. **Proved sorry-free.**
- `kineticEnergy_lsc_transfer` — abstract norm-lsc transfer of a uniform pointwise bound to the
  L²-limit at a.e. time, given the same `hg`. **Proved sorry-free.**

## Assumptions

No new `axiom`/`opaque`/`constant`. Genuinely-missing inputs appear as explicit
hypotheses, never axioms.

## Scaffold ledger

Definitions (scaffold): `IsWeakTimeDeriv`, `GelfandTriple.Vprime`,
`GelfandTriple.hToVprime`, `W1pTime`.
**Proved (sorry-free):** `hasDerivAt_isWeakTimeDeriv` (strong⇒weak time derivative
via Bochner IBP), `aeStronglyMeasurable_of_spaceTimeL2` and `kineticEnergy_lsc_transfer` (both
after a statement-gate fix adding the isolated `hg : AEStronglyMeasurable g μ` hypothesis — the
prior hypothesis-free forms were FALSE; Vitali counterexamples kept in their docstrings),
`GelfandTriple.hToVprimeCLM` / `GelfandTriple.hToVprimeCLM_apply` (the embedding `H ↪ V'`
bundled as a genuine `H →L[ℝ] V'`, equal to `hToVprime` pointwise), and
`isWeakTimeDeriv_comp_clm` (transport of a weak time derivative through a CLM, given
interval-integrability of the Bochner integrands).
**Proved (sorry-free, issue #13-B):** `isWeakTimeDeriv_unique` — after adding the
  faithful `[CompleteSpace X]` guard (domain fix: without it `integral_of_not_completeSpace`
  collapses both `h₁`/`h₂` to `0 = -0`, admitting arbitrary `v₁,v₂`; identical to D2 precedent)
  and importing `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff` (vector-valued du Bois-Reymond).
`W1pTime.ofHValuedDeriv` is **sorry-free**: under the domain guards `1 ≤ p` /
`1 ≤ q` (the Lions–Magenes space is only defined for exponents ≥ 1, so these are faithful
preconditions, not proof-strengthening), the two interval-integrability obligations are
discharged via `MemLp.integrable` on the finite measure combined with the private helper
`intervalIntegrable_smul_of_integrableOn_Icc` (bounded continuous test factor + support in
`Ioo 0 T`). The `1 ≤ p` / `1 ≤ q` signature guards (added commit c362d9b) are the minimal
honest domain restriction; the previous over-strength-flagged form (without those guards) was
corrected before the proof was attempted.
Months-class residual (scaffold-only + `TODO`): `w1pTime_continuous_in_H`, relocated to
`LerayHopf.Bochner.TimeSobolevExperimental` (issue #147) and there restricted to `p = q = 2`
after the prior generic-`p,q` statement was found FALSE (issue #158).
-/

import Tengoku.LerayHopf.LerayHopf.Bochner.GelfandTriple
import Tengoku.Seed.Analysis.Distribution.AEEqOfIntegralContDiff
import Tengoku.Seed.Analysis.InnerProductSpace.Dual
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Stage D1 — weak (distributional) time derivative -/

section WeakTimeDeriv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Weak (distributional) time derivative** of a Banach-valued curve on `(0, T)`.

`v` is a weak time derivative of `u` on `(0, T)` iff for every scalar test function
`ψ : ℝ → ℝ` that is `C¹` with compact support contained in the open interval `Ioo 0 T`,

  `∫ t in 0..T, deriv ψ t • u t = - ∫ t in 0..T, ψ t • v t`   (Bochner integrals).

The compact-support-in-`Ioo 0 T` convention matches `WeakFormNS` exactly, so the two
distributional formulations compose without boundary terms. No boundary term is smuggled:
`ψ` vanishes (with all derivatives) at `0` and `T`, so the integration-by-parts identity
defining `v = u'` has no endpoint contribution. This is the genuine distributional
derivative, not a strong one. -/
def IsWeakTimeDeriv (T : ℝ) (u v : ℝ → X) : Prop :=
  ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
    (∫ t in (0 : ℝ)..T, deriv ψ t • u t) = - ∫ t in (0 : ℝ)..T, ψ t • v t

/-- **Whole-line weak (distributional) time derivative** of a Banach-valued curve on all of `ℝ`.

`v` is a whole-line weak time derivative of `u` iff for every scalar test function
`ψ : ℝ → ℝ` that is `C¹` with compact support (no interval constraint),

  `∫ t, deriv ψ t • u t = - ∫ t, ψ t • v t`   (global Bochner integrals).

The global integrals converge because `ψ` has compact support. This is the honest
distributional derivative on `ℝ` — strictly stronger than `IsWeakTimeDeriv T u v`, which
only tests `ψ` supported inside `(0, T)`. It is the correct hypothesis for whole-line
operations such as convolution (see `s1-walls-design.md` §1a): shifting a globally
compactly-supported test function by `s` stays compactly-supported and global, so
`hwd (ψ(· + s))` is always applicable, dissolving the Fubini obstruction present at
the old interval signature. -/
def IsWeakTimeDerivℝ (u v : ℝ → X) : Prop :=
  ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
    (∫ t, deriv ψ t • u t) = - ∫ t, ψ t • v t

end WeakTimeDeriv

/-! ### Stage D1 — the continuous dual `V'` and the embedding `H ↪ V'` -/

namespace GelfandTriple

/-- The **continuous dual** `V' := V →L[ℝ] ℝ` (= `StrongDual ℝ V`) of the regularity
space, the codomain of the Lions–Magenes time derivative `u' ∈ L^q(0,T;V')`. -/
abbrev Vprime (GT : GelfandTriple) : Type _ :=
  letI := GT.instNACG_V; letI := GT.instIPS_V;
  GT.V →L[ℝ] ℝ

/-- The **canonical embedding** `H ↪ V'`, sending `h ∈ H` to the functional
`v ↦ ⟪ι v, h⟫_H` on `V`. By real-symmetry of the inner product this equals
`(InnerProductSpace.toDual ℝ H h) ∘L GT.ι`, i.e. the transpose of `ι` composed with the
Riesz identification `H ≅ H'`. It is injective because `ι` has dense range
(`ι_denseRange`), which is exactly the Gelfand-triple defining property — but injectivity is
not needed to state `W1pTime`, so we keep this as the bare embedding. -/
noncomputable def hToVprime (GT : GelfandTriple) :
    letI := GT.instNACG_H; GT.H → GT.Vprime :=
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  fun h => (InnerProductSpace.toDual ℝ GT.H h).comp GT.ι

end GelfandTriple

/-! ### Stage D1 — abstract `W^{1,p}(0,T;V) ∩ {u' ∈ L^q(0,T;V')}` bundle -/

/-- **Abstract vector-valued time-Sobolev membership bundle** for a Gelfand triple.

`W1pTime GT p q T uV` bundles the data of `u ∈ L^p(0, T; V)` together with a weak time
derivative `u' ∈ L^q(0, T; V')`. The time derivative is stored as a genuine `V'`-valued
curve `u' : ℝ → V'` (the faithful Lions–Magenes / Gelfand-triple object): requiring the
derivative to live in the pivot space `H` would be strictly STRONGER and could exclude the
actual Navier–Stokes weak time derivative, which is only expected in `V'`. The `u`-side is
measured in `V` in the genuine **Bochner** sense (`u ∈ L^p(·;V)` is `MemLp uV p`: the
V-valued curve is a.e.-strongly-measurable with finite `eLpNorm`, controlling the curve
itself rather than only its scalar norm `t ↦ ‖u t‖_V`); weak differentiation is taken on the
`V'`-valued curve obtained by viewing `u` in `V'` through `ι` followed by `H ↪ V'`.

Fields:
- `u'` : the `V'`-valued weak time-derivative curve (Lions–Magenes `u' ∈ L^q(0,T;V')`);
- `mem_p` : `uV ∈ L^p(0,T;V)` in the **Bochner** sense — `MemLp uV p`, which bundles
  a.e.-strong-measurability of the V-valued curve `uV` with finite `eLpNorm` (NOT merely
  finiteness of the scalar norm `t ↦ ‖uV t‖`, which would not control measurability of `uV`);
- `mem_q` : `u' ∈ L^q(0,T;V')` (the genuine `V'`-valued time-derivative membership);
- `weakDeriv` : `u'` is the weak time derivative, in `V'`, of the curve `t ↦ (ι (uV t)) ∈ V'`
  (the embedding of `u` into `V'`), so the bundle is a genuine Sobolev-in-time element.

**Scaffold (definition).** -/
structure W1pTime (GT : GelfandTriple) (p q : ℝ≥0∞) (T : ℝ)
    (uV : ℝ → GT.V) where
  /-- The `V'`-valued weak time-derivative curve (Lions–Magenes `u' ∈ L^q(0,T;V')`). -/
  u' : ℝ → GT.Vprime
  /-- `L^p(0,T;V)` membership in the genuine **Bochner** sense: the V-valued curve `uV` is
  `p`-integrable on `[0,T]`. `MemLp uV p μ` bundles `AEStronglyMeasurable uV μ` together with
  finite `eLpNorm uV p μ`, so it controls the V-valued curve itself — not merely its scalar
  norm `t ↦ ‖uV t‖` (which would not even assert measurability of `uV`). -/
  mem_p : letI := GT.instNACG_V; MemLp uV p (volume.restrict (Set.Icc 0 T))
  /-- `L^q(0,T;V')` membership of the genuine `V'`-valued weak derivative. -/
  mem_q : letI := GT.instNACG_V; letI := GT.instIPS_V;
    MemLp u' q (volume.restrict (Set.Icc 0 T))
  /-- `u'` is the weak time derivative, in `V'`, of the `V'`-image of `u`, namely
  `t ↦ hToVprime (ι (uV t))`. -/
  weakDeriv : letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    IsWeakTimeDeriv (X := GT.Vprime) T (fun t => GT.hToVprime (GT.ι (uV t))) u'

/-- The canonical embedding `H ↪ V'` as a genuine `ContinuousLinearMap` (the bundled form
of `GelfandTriple.hToVprime`). It is the precomposition `g ↦ g ∘ GT.ι` (the honest ℝ-linear
`ContinuousLinearMap.compL … |>.flip GT.ι`) applied after the Riesz map `innerSL ℝ : H →L[ℝ]
(H →L[ℝ] ℝ)`. Over `ℝ` the inner product is genuinely bilinear, so `innerSL ℝ` is an honest
`H →L[ℝ] _` (its conjugate-linearity is trivial), and `hToVprimeCLM h = (innerSL ℝ h).comp
GT.ι = (toDual ℝ H h).comp GT.ι = hToVprime h` pointwise (see `hToVprimeCLM_apply`). -/
noncomputable def GelfandTriple.hToVprimeCLM (GT : GelfandTriple) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H; GT.H →L[ℝ] GT.Vprime :=
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  ((ContinuousLinearMap.compL ℝ GT.V GT.H ℝ).flip GT.ι).comp
    (innerSL ℝ : GT.H →L[ℝ] (GT.H →L[ℝ] ℝ))

/-- The bundled continuous linear map `hToVprimeCLM` agrees pointwise with the (unbundled)
Riesz embedding `hToVprime`. -/
@[simp] theorem GelfandTriple.hToVprimeCLM_apply (GT : GelfandTriple) :
    letI := GT.instNACG_H;
    (h : GT.H) → GT.hToVprimeCLM h = GT.hToVprime h := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  intro h
  -- Both sides equal `(v ↦ ⟪ι v, h⟫) ∈ V'`; reduce the bundled composition and compare on `V`.
  ext v
  simp only [GelfandTriple.hToVprimeCLM, GelfandTriple.hToVprime,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, coe_innerSL_apply, InnerProductSpace.toDual_apply_apply]

/-- **Transport of a whole-line weak time derivative through a continuous linear map.**
If `v` is the whole-line weak time derivative of `u` (an `X`-valued curve, `IsWeakTimeDerivℝ
u v`) and `L : X →L[ℝ] Y` is continuous linear, then `L ∘ v` is the whole-line weak time
derivative of `L ∘ u`.

The global integrals converge because the test `ψ` has compact support; `L` commutes with
the Bochner integral (`ContinuousLinearMap.integral_comp_comm`, which needs integrability —
automatic here: integrand `deriv ψ • u` is supported in `tsupport ψ` which is compact, so
integrability follows from continuity of the integrand on a compact domain) and with `smul`
(`map_smul`). This is the global analogue of `isWeakTimeDeriv_comp_clm` (§2e of the
`s1-walls-design.md`); the interval integrability side-conditions collapse because
compactness of `tsupport ψ` gives integrability for free.

Tier: **Sonnet** (mechanical port of `isWeakTimeDeriv_comp_clm`). -/
theorem isWeakTimeDerivℝ_comp_clm {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {u v : ℝ → X} (L : X →L[ℝ] Y)
    (hwd : IsWeakTimeDerivℝ (X := X) u v)
    (hu_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
      Integrable (fun t => deriv ψ t • u t) volume)
    (hv_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
      Integrable (fun t => ψ t • v t) volume) :
    IsWeakTimeDerivℝ (X := Y) (fun t => L (u t)) (fun t => L (v t)) := by
  -- Port of `isWeakTimeDeriv_comp_clm` to the whole-line setting.
  -- For each test ψ: push L through both global integrals via `ContinuousLinearMap.integral_comp_comm`,
  -- use `map_smul` to commute L with scalar multiplication, then apply `hwd ψ`.
  intro ψ hψcs hψC1
  -- The defining identity in `X`: `∫ deriv ψ • u = - ∫ ψ • v`.
  have hX := hwd ψ hψcs hψC1
  -- Push `L` through the left integral: `∫ deriv ψ t • L (u t) = L (∫ deriv ψ t • u t)`.
  have hLu : (∫ t, deriv ψ t • L (u t)) = L (∫ t, deriv ψ t • u t) := by
    have hint := hu_int ψ hψcs hψC1
    have : (fun t => deriv ψ t • L (u t)) = (fun t => L (deriv ψ t • u t)) := by
      ext t; rw [L.map_smul]
    rw [this]
    exact L.integral_comp_comm hint
  -- Push `L` through the right integral: `∫ ψ t • L (v t) = L (∫ ψ t • v t)`.
  have hLv : (∫ t, ψ t • L (v t)) = L (∫ t, ψ t • v t) := by
    have hint := hv_int ψ hψcs hψC1
    have : (fun t => ψ t • L (v t)) = (fun t => L (ψ t • v t)) := by
      ext t; rw [L.map_smul]
    rw [this]
    exact L.integral_comp_comm hint
  rw [hLu, hLv, hX, L.map_neg]

/-! ### Lions–Magenes good-representative embedding — relocated and corrected (issues #147, #158)

`w1pTime_continuous_in_H` now lives in `LerayHopf.Bochner.TimeSobolevExperimental`, so the
release surface `import LerayHopf` stays sorry-free. It is also no longer stated at the prior
generic `{p q} (hpq : 1 ≤ p ∧ 1 ≤ q)` signature — issue #158 found that FALSE (explicit
`p = q = 1` counterexample) — but restricted to `p = q = 2`, the only case with an actual
proof plan. This file's other declarations (`W1pTime`, `GelfandTriple.hToVprimeCLM`,
`aeStronglyMeasurable_of_spaceTimeL2`, `kineticEnergy_lsc_transfer`, …) are unaffected and
remain sorry-free in the root closure; `R3/AubinLionsLimitPassage.lean` and
`R3/EnergyWeakLsc.lean` continue to import this file directly for `kineticEnergy_lsc_transfer`
(Stage D2 below), which does not depend on the relocated theorem. -/

/-! ### Stage D2 — measurable-representative primitive (KEY, unblocks P2's E1) -/

section MeasurableRep

variable {β : Type*} [NormedAddCommGroup β]

/-- **Measurable representative of a space-time L²-limit (D2 KEY PRIMITIVE).**

Setup (the abstract form of `AubinLionsPackage_R3`'s local space-time convergence): a
sequence `f : ℕ → ℝ → β` of curves, each a.e.-strongly-measurable in time w.r.t. a measure
`μ` on the time line, converges to a limit curve `g` in `L²(μ; β)` (i.e.
`eLpNorm (fun t => f n t - g t) 2 μ → 0`). Then:

1. `g` admits an **a.e.-strongly-measurable representative** w.r.t. `μ` (the joint
   `(t,x)`-measurability handle), and
2. there is a **subsequence** `φ` with `f (φ k) t → g t` for `μ`-a.e. `t`.

This is precisely the ingredient `R3.AubinLionsLimitPassage.kineticEnergy_lsc_bound` (E1)
names as its sole blocker: from the package's `∫₀ᵀ ∫_{B_k} ‖uₙ(t) − u(t)‖² dt → 0` (an
`eLpNorm`-to-0 statement with each `uₙ(·)` measurable in `t`), it yields both the time
measurability of the limit and an a.e.-in-`t` convergent subsequence, after which per-`t`
ball-exhaustion norm-lsc closes the kinetic bound. The conclusion is genuine
a.e.-strong-measurability + an a.e. (not merely in-measure) subsequence — no trivial
representative satisfies it because it is tied to the given `L²`-convergent sequence.

**Isolated missing pillar `hg : AEStronglyMeasurable g μ` (statement-gate fix, Lane-D
2026-06-20).** The earlier form WITHOUT this hypothesis was FALSE: μ = Lebesgue on `[0,1]`,
`f n = 0`, `g = 𝟙_V` for a non-measurable Vitali set `V` (inner measure `0`) gives
`eLpNorm (f n - g) 2 μ = eLpNorm g 2 μ = (∫⁻ ‖g‖²)^(1/2) = 0` (the `∫⁻` of a non-measurable
function is the *lower* Lebesgue integral, whose largest measurable minorant of `‖g‖²` is `0`
a.e.), so the convergence hypothesis held yet `g` was not a.e.-strongly-measurable. Measurability
of an L²-limit genuinely CANNOT be extracted from L²-convergence alone — every
`tendstoInMeasure_of_tendsto_eLpNorm*` mathlib lemma *requires* `AEStronglyMeasurable g` as an
INPUT. So `g`'s measurability is the genuine missing pillar; we isolate it as the explicit
hypothesis `hg` (no-smuggle: it asserts ONLY measurability of `g` — no subsequence, no limit
identification, no spatial content). The lemma's real content is then the a.e.-convergent
subsequence; the first conjunct is `hg` itself, kept in the conclusion so the lemma packages
"measurable representative + a.e. subsequence" for its E1-style consumer.

**Proved** (sorry-free). Route: `tendstoInMeasure_of_tendsto_eLpNorm` (needs `hg`)
⇒ `TendstoInMeasure.exists_seq_tendsto_ae`. -/
theorem aeStronglyMeasurable_of_spaceTimeL2
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0)) :
    AEStronglyMeasurable g μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ t ∂μ, Tendsto (fun k => f (φ k) t) atTop (𝓝 (g t)) := by
  refine ⟨hg, ?_⟩
  -- `eLpNorm (f n - g) 2 μ → 0`: the pointwise sub `fun t => f n t - g t` IS the `Pi` sub
  -- `f n - g` (definitionally), so `hconv` already has the form the mathlib lemma consumes.
  have hconv' : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := hconv
  -- L²-convergence ⇒ convergence in measure (uses `hg`), then extract an a.e. subsequence.
  have htim : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf hg hconv'
  exact htim.exists_seq_tendsto_ae

end MeasurableRep

/-- **Abstract kinetic-energy lower-semicontinuity transfer (abstract core of E1).**

GIVEN the measurable representative from `aeStronglyMeasurable_of_spaceTimeL2`: if a sequence
`f n : ℝ → β` converges to `g` in `L²(μ)`, with a UNIFORM pointwise norm bound
`‖f n t‖ ≤ M` for `μ`-a.e. `t` and every `n`, then the limit inherits the bound at a.e.
time: `‖g t‖ ≤ M` for `μ`-a.e. `t`.

This is the domain-neutral norm-lsc step: extract the a.e.-convergent subsequence
(`aeStronglyMeasurable_of_spaceTimeL2`), then pass the uniform bound through the a.e. limit
by `le_of_tendsto` + lower-semicontinuity of the norm. The a.e.-in-`t` conclusion (NOT
`∀ t`) is the honest form — the value of `g` on a `μ`-null set is not pinned by `L²`
convergence (matching `kineticEnergy_lsc_bound`'s a.e. conclusion, no-smuggle).

**Isolated missing pillar `hg : AEStronglyMeasurable g μ` (statement-gate fix, Lane-D
2026-06-20), exactly as in `aeStronglyMeasurable_of_spaceTimeL2`.** WITHOUT it the statement is
FALSE: μ = Lebesgue on `[0,1]`, `M = 1`, `f n = 0` (so `hbound` holds), `g = 2 · 𝟙_V` for a
non-measurable Vitali set `V` gives `eLpNorm (f n - g) 2 μ = eLpNorm g 2 μ = 0` (lower integral
of a non-measurable function) so `hconv` holds, yet `{t : ‖g t‖ > 1} = V` is not contained in any
null set (positive outer measure), so `∀ᵐ t, ‖g t‖ ≤ 1` FAILS. The norm bound on the limit
genuinely needs `g` measurable. No-smuggle: `hg` asserts only measurability of `g`.

**Proved** (sorry-free), given `hg`. -/
theorem kineticEnergy_lsc_transfer {β : Type*} [NormedAddCommGroup β]
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β} {M : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ M) :
    ∀ᵐ t ∂μ, ‖g t‖ ≤ M := by
  -- Extract the a.e.-convergent subsequence `f (φ k) t → g t`.
  obtain ⟨_, φ, _hφ, hae⟩ := aeStronglyMeasurable_of_spaceTimeL2 hf hg hconv
  -- The uniform bound holds for all `n` simultaneously at a.e. `t` (`ae_all_iff`).
  have hbound_all : ∀ᵐ t ∂μ, ∀ k, ‖f (φ k) t‖ ≤ M :=
    (ae_all_iff.2 fun k => hbound (φ k))
  -- At a.e. `t`: `‖f (φ k) t‖ → ‖g t‖` and `‖f (φ k) t‖ ≤ M`, so `‖g t‖ ≤ M`.
  filter_upwards [hae, hbound_all] with t htlim htbd
  exact le_of_tendsto' htlim.norm htbd

end LerayHopf.Bochner
