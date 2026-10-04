/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1976, Problem 5

The polynomials a(x), b(x), c(x), d(x) satisfy
a(x⁵) + x·b(x⁵) + x²·c(x⁵) = (1 + x + x² + x³ + x⁴)·d(x).
Show that a(x) has the factor (x - 1).
-/

namespace Usa1976P5

open Polynomial

/-- A primitive fifth root of unity in `ℂ`. -/
noncomputable abbrev ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (5 : ℂ)⁻¹)

lemma isPrimitiveRoot_ω : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp_of_coprime 1 5 (by norm_num) (by decide)
  simpa using h

end Usa1976P5
