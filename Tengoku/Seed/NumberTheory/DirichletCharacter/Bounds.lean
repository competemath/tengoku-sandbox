/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Field.Basic
public import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
public import Tengoku.Seed.Data.Nat.Totient
public import Tengoku.Seed.Data.Sym.Sym2
public import Tengoku.Seed.Tactic.ContinuousFunctionalCalculus
public import Tengoku.Seed.Tactic.NormNum.GCD
public import Tengoku.Seed.Tactic.Positivity

/-!
# Bounds for values of Dirichlet characters

We consider Dirichlet characters `χ` with values in a normed field `F`.

We show that `‖χ a‖ = 1` if `a` is a unit and `‖χ a‖ ≤ 1` in general.
-/

public section

variable {F : Type*} [NormedField F] {n : ℕ} (χ : DirichletCharacter F n)

namespace DirichletCharacter

/-- The value at a unit of a Dirichlet character with target a normed field has norm `1`. -/
@[simp] lemma unit_norm_eq_one (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one,
    norm_one]

/-- The values of a Dirichlet character with target a normed field have norm bounded by `1`. -/
lemma norm_le_one (a : ZMod n) : ‖χ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one


end DirichletCharacter
