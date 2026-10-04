/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module -- shake: keep-all

public import Tengoku.Seed.FieldTheory.Finite.Valuation

deprecated_module (since := "2026-03-31")

public section

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.algebraMap_eq_one :=
  FiniteField.valuation_algebraMap_eq_one

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.algebraMap_le_one :=
  FiniteField.valuation_algebraMap_le_one

@[deprecated (since := "2026-03-31")] alias Valuation.FiniteField.instIsTrivialOn :=
  FiniteField.instIsTrivialOn
