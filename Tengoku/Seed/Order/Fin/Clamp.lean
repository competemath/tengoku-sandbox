/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Std.Data.Fin.Lemmas
public import Tengoku.Seed.Order.Fin.Basic
public import Tengoku.Seed.Order.MinMax

/-!
# Lemmas about `Fin.clamp`

-/

namespace Fin

public lemma clamp_monotone {m : ℕ} : Monotone (fun n ↦ clamp n m) := by
  intro a b h
  rw [le_iff_val_le_val]
  exact min_le_min_right m h

public lemma clamp_eq_last (n m : ℕ) (hmn : m ≤ n) :
    clamp n m = last _ := by
  ext
  simpa

end Fin
