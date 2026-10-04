/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1969, Problem 6

Given real numbers x₁, x₂, y₁, y₂, z₁, z₂ satisfying x₁ > 0, x₂ > 0,
x₁y₁ > z₁², and x₂y₂ > z₂², prove that

  8 / ((x₁ + x₂)(y₁ + y₂) - (z₁ + z₂)²) ≤ 1 / (x₁y₁ - z₁²) + 1 / (x₂y₂ - z₂²).

Give necessary and sufficient conditions for equality.
-/

namespace Imo1969P6

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln696.html

/-- The core AM–GM chain of the solution: with `p² = x₁y₁ - z₁²` and `q² = x₂y₂ - z₂²`
we have `pq + z₁z₂ ≤ √(x₁y₁ · x₂y₂) = √(x₁y₂) · √(x₂y₁)` and
`2 √(x₁y₂) √(x₂y₁) ≤ x₁y₂ + x₂y₁` (AM–GM). -/
theorem amgm_chain {x₁ x₂ y₁ y₂ z₁ z₂ p q : ℝ}
    (hx₁ : 0 < x₁) (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (hp₂ : p ^ 2 = x₁ * y₁ - z₁ ^ 2) (hq₂ : q ^ 2 = x₂ * y₂ - z₂ ^ 2) :
    p * q + z₁ * z₂ ≤ Real.sqrt (x₁ * y₁ * (x₂ * y₂)) ∧
      Real.sqrt (x₁ * y₁ * (x₂ * y₂)) = Real.sqrt (x₁ * y₂) * Real.sqrt (x₂ * y₁) ∧
        2 * (Real.sqrt (x₁ * y₂) * Real.sqrt (x₂ * y₁)) ≤ x₁ * y₂ + x₂ * y₁ := by
  have hx₁y₁ : x₁ * y₁ = p ^ 2 + z₁ ^ 2 := by linarith only [hp₂]
  have hx₂y₂ : x₂ * y₂ = q ^ 2 + z₂ ^ 2 := by linarith only [hq₂]
  have hpos₁ : (0 : ℝ) ≤ x₁ * y₂ := (mul_pos hx₁ hy₂).le
  have hpos₂ : (0 : ℝ) ≤ x₂ * y₁ := (mul_pos hx₂ hy₁).le
  have hs1 : (p * q + z₁ * z₂) ^ 2 ≤ x₁ * y₁ * (x₂ * y₂) := by
    have e : x₁ * y₁ * (x₂ * y₂) = (p ^ 2 + z₁ ^ 2) * (q ^ 2 + z₂ ^ 2) := by
      rw [hx₁y₁, hx₂y₂]
    rw [e]
    linarith only [sq_nonneg (p * z₂ - q * z₁)]
  refine ⟨Real.le_sqrt_of_sq_le hs1, ?_, ?_⟩
  · rw [show x₁ * y₁ * (x₂ * y₂) = x₁ * y₂ * (x₂ * y₁) by ring,
      Real.sqrt_mul hpos₁]
  · have h := two_mul_le_add_sq (Real.sqrt (x₁ * y₂)) (Real.sqrt (x₂ * y₁))
    rw [Real.sq_sqrt hpos₁, Real.sq_sqrt hpos₂] at h
    linarith only [h]

/-- The condition for equality to hold. -/
abbrev eqCondition (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ) : Prop := x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂

end Imo1969P6
