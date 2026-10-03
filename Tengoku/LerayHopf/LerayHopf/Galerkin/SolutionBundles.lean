import Tengoku.LerayHopf.LerayHopf.Galerkin.Domain

open MeasureTheory Filter Topology

/-!
# Generic Galerkin solution bundles (issue #112, PR-C)

**Domain-neutral proof-carrying solution structures over a `Galerkin.Domain`.**

This file promotes the per-lane bundle structures (`GalerkinSolutionData[_R3]`,
`LerayHopfSolutionFull[_R3]`, `GalerkinCompactnessPackageFull[_R3]`) to a single generic
layer parameterized by a `Galerkin.Domain` and an `NSFormCore`.  Both lanes recover their
current structures as abbreviations of these (`LerayHopf/{Torus,R3}/SolutionInterfaces.lean`);
every field specializes definitionally to the current per-lane field, so constructor and
projection sites are unchanged.  R3's finite-dim `viscous_curve_continuous` enrichment is
carried by an `extends`-extension in the R3 lane, not here (it is R3-specific).

## Main definitions and theorems

- `Galerkin.SolutionData`        : the `n`-th Galerkin ODE solution data
- `Galerkin.LerayHopfSolution`   : proof-carrying Leray–Hopf solution
- `Galerkin.CompactnessPackage`  : proof-carrying Galerkin compactness package
- `Galerkin.exists_lerayHopf_from_package` : lifts a package to `Nonempty (LerayHopfSolution …)`

## Assumptions

None beyond mathlib axioms; zero `axiom`/`opaque`/`unsafe`/`sorry` declarations.
`exists_lerayHopf_from_package` is the trivial field-copy assembly (the shared body of the
former per-lane `exists_lerayHopf_from_package_full[_R3]`); both lanes delegate to it, keeping
the capstones kernel-only.
-/

namespace LerayHopf.Galerkin

/-- Data produced by the `n`-th Galerkin ODE on the approximation subspace `Vₙ ⊆ ↥D.σ`.

Packages: the solution curve, initial condition, subspace-range property, forward-time
differentiability, the projected ODE, regularity membership, and uniform (n-independent)
energy and regularity bounds.  The forward-only (`0 ≤ t →`) restriction on `u_hasDeriv` and
`u_ode` matches the merged per-lane structures (the quadratic Galerkin field can blow up in
finite backward time). -/
structure SolutionData (D : Domain) (C : NSFormCore D) (ν : ℝ) (u₀ : ↥D.σ) (n : ℕ) where
  /-- The Galerkin solution curve. -/
  u : Time → ↥D.σ
  /-- Initial condition: `u(0) = Pₙ u₀`. -/
  u_initial : u 0 = ⟨D.P n ↑u₀, D.P_preserves_σ n ↑u₀ u₀.2⟩
  /-- Range in `Vₙ`: the solution stays in the Galerkin subspace. -/
  u_inVn : ∀ t, (u t : D.X) = D.P n ↑(u t)
  /-- The curve `t ↦ (u t : D.X)` is differentiable at every forward time `t ≥ 0`. -/
  u_hasDeriv : ∀ t, 0 ≤ t →
    HasDerivAt (fun s => (u s : D.X)) (deriv (fun s => (u s : D.X)) t) t
  /-- The projected Galerkin ODE at forward times: for all `w ∈ Vₙ`,
  `⟪u'(t), w⟫ + ν · stokes(u(t), w) + b(u(t), u(t), w) = 0`. -/
  u_ode : ∀ t, 0 ≤ t → ∀ w : ↥D.σ, (w : D.X) = D.P n ↑w →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : D.X)) t) (w : D.X)
      + ν * D.stokes ↑(u t) ↑w + C.b (u t) (u t) w = 0
  /-- Regularity membership: the solution stays in H¹. -/
  reg_mem : ∀ t, D.regMem ↑(u t)
  /-- Uniform energy bound: `½‖u(t)‖² ≤ ½‖Pₙu₀‖²`. -/
  energy_bound : ∀ t, 0 ≤ t →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖D.P n ↑u₀‖ ^ 2
  /-- Uniform (n-independent) regularity bound. -/
  reg_bound : ∀ T, 0 < T →
    ∫ t in (0 : ℝ)..T, D.regIntegrand ν ↑(u t) ≤ D.regBoundRHS ν T ‖(u₀ : D.X)‖

/-- The **full Leray–Hopf solution** structure carrying genuine proof fields:
weak NS identity, energy inequality, initial trace, energy class, and time-measurability. -/
structure LerayHopfSolution (D : Domain) (C : NSFormCore D) (ν T : ℝ) (u₀ : ↥D.σ) where
  /-- The solution curve. -/
  u : Time → ↥D.σ
  /-- Weak NS equation (proof-carrying). -/
  weak_eq : WeakFormNS ν T (D.evolution C) u
  /-- Energy inequality (proof-carrying): holds for `t ∈ [0, T]`. -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2
  /-- Initial trace: `u(t) → u₀` as `t → 0⁺` (proof-carrying). -/
  initial_trace : Filter.Tendsto (fun t => (u t : D.X))
    (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀)
  /-- Energy class (proof-carrying): a.e. regularity membership on `[0, T]` and integrable
  viscous dissipation (non-vacuity of the energy inequality). -/
  energy_class :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), D.regMem ↑(u t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(u s)) MeasureTheory.volume 0 T
  /-- Time-measurability (proof-carrying): the solution curve is `AEStronglyMeasurable`. -/
  u_aestronglyMeasurable :
    MeasureTheory.AEStronglyMeasurable (fun t => (u t : D.X))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

/-- The **full Galerkin compactness package** carrying genuine proof fields.  Its fields
mirror `LerayHopfSolution` with the compactness-limit curve `limit`. -/
structure CompactnessPackage (D : Domain) (C : NSFormCore D) (ν T : ℝ) (u₀ : ↥D.σ) where
  /-- The limit curve. -/
  limit : Time → ↥D.σ
  /-- Weak NS equation for the limit. -/
  weak_eq_limit : WeakFormNS ν T (D.evolution C) limit
  /-- Energy inequality for the limit: holds for `t ∈ [0, T]`. -/
  energy_ineq_limit : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(limit t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(limit s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2
  /-- Initial trace for the limit. -/
  initial_trace_limit : Filter.Tendsto (fun t => (limit t : D.X))
    (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀)
  /-- Energy class for the limit. -/
  energy_class_limit :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), D.regMem ↑(limit t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(limit s)) MeasureTheory.volume 0 T
  /-- Time-measurability for the limit. -/
  u_aestronglyMeasurable_limit :
    MeasureTheory.AEStronglyMeasurable (fun t => (limit t : D.X))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

/-- **Assembly:** A `CompactnessPackage` yields `Nonempty (LerayHopfSolution …)`. -/
theorem exists_lerayHopf_from_package (D : Domain) (C : NSFormCore D) (ν T : ℝ)
    (u₀ : ↥D.σ) (pkg : CompactnessPackage D C ν T u₀) :
    Nonempty (LerayHopfSolution D C ν T u₀) :=
  ⟨{ u := pkg.limit
     weak_eq := pkg.weak_eq_limit
     energy_ineq := pkg.energy_ineq_limit
     initial_trace := pkg.initial_trace_limit
     energy_class := pkg.energy_class_limit
     u_aestronglyMeasurable := pkg.u_aestronglyMeasurable_limit }⟩

end LerayHopf.Galerkin
