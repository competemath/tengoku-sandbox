/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Init
public import Tengoku.Seed.Tactic.Aesop.Frontend

/-! # Finiteness tactic attribute -/

declare_aesop_rule_sets [finiteness]
