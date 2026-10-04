import Tengoku

/-!
# Abstract energy inequality

**Must-prove, sorry-free.** A purely abstract, PDE-free formulation of the energy
inequality and one nontrivial consequence: if the dissipation is nonnegative and the
viscosity is nonnegative, the energy is nonincreasing. This checks that the formalization
is more than a collection of records.

The accumulated-dissipation form (`A : ℝ → ℝ → ℝ`) is used per the original MVP plan's
design decision; the interval-integral form was considered as a later refinement but not
adopted. Design-decision reference (archived, historical): `docs/archive/leray_hopf_lean_mvp_plan.md`
(Milestone E).
-/

namespace LerayHopf

/-- Abstract data for an energy inequality: kinetic energy `E`, accumulated dissipation
`A s t` over `[s, t]`, and viscosity `ν`. -/
structure EnergyData where
  /-- Kinetic energy as a function of time. -/
  E : ℝ → ℝ
  /-- Accumulated dissipation `A s t` over the interval `[s, t]`. -/
  A : ℝ → ℝ → ℝ
  /-- Viscosity coefficient. -/
  ν : ℝ

/-- The abstract energy inequality: for `0 ≤ s ≤ t`,
`E(t) + ν · A(s,t) ≤ E(s)`. -/
def EnergyInequality (ed : EnergyData) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → ed.E t + ed.ν * ed.A s t ≤ ed.E s

/-- If the energy inequality holds with nonnegative viscosity and nonnegative
accumulated dissipation, then the energy is nonincreasing on `[0, ∞)`. -/
theorem energy_nonincreasing_from_nonnegative_dissipation
    (ed : EnergyData) (hE : EnergyInequality ed) (hν : 0 ≤ ed.ν)
    (hA : ∀ s t, 0 ≤ s → s ≤ t → 0 ≤ ed.A s t) :
    ∀ s t, 0 ≤ s → s ≤ t → ed.E t ≤ ed.E s := by
  intro s t hs hst
  have h := hE s t hs hst
  have hnonneg : 0 ≤ ed.ν * ed.A s t := mul_nonneg hν (hA s t hs hst)
  linarith

end LerayHopf
