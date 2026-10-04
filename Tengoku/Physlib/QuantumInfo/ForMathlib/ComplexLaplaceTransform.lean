/-
Copyright (c) 2025 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Tengoku

@[expose] public section

noncomputable section

/-- The integrand of the complex Laplace transform of a possibly infinite-valued energy function. -/
def ComplexLaplaceIntegrand {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (x : α) : ℂ :=
  if h : E x = ⊤ then 0 else Complex.exp (-z * (E x).untop h : ℂ)

/-- The complex Laplace transform of a possibly infinite-valued energy function. -/
def ComplexLaplaceTransform {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) (z : ℂ) : ℂ :=
  ∫ x, ComplexLaplaceIntegrand E z x

/-- The complex convergence domain of a Laplace transform. -/
def ComplexLaplaceConvergenceDomain {α : Type*} [MeasureTheory.MeasureSpace α]
    (E : α → WithTop ℝ) : Set ℂ :=
  {z | MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E z)}

/-- A two-sided exponential envelope controlling the Laplace integrand near `z`. -/
private def ComplexLaplaceEnvelope {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (δ : ℝ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E (z - (δ : ℂ)) x‖ +
    ‖ComplexLaplaceIntegrand E (z + (δ : ℂ)) x‖

private def ComplexLaplaceEndpointEnvelope {α : Type*} (E : α → WithTop ℝ) (z w : ℂ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E z x‖ + ‖ComplexLaplaceIntegrand E w x‖

end
