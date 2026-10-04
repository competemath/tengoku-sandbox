/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Logic.Encodable.Basic
public import Tengoku.Seed.Data.Rat.Init

/-! # The rationals are `Encodable`.

As a consequence we also get the instance `Countable ℚ`.

This is kept separate from `Data.Rat.Defs` in order to minimize imports.
-/

public section


namespace Rat

instance : Encodable ℚ :=
  Encodable.ofEquiv (Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_iff_ne_zero.mp c, d⟩,
      fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩

end Rat
