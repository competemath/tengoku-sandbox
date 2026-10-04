/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Logic.Encodable.Basic
public import Tengoku.Seed.Data.NNRat.Defs

/-! # The nonnegative rationals are `Encodable`.

As a consequence we also get the instance `Countable ℚ≥0`.
-/

namespace NNRat

public instance : Encodable ℚ≥0 :=
  Encodable.ofEquiv (Σ n : ℕ, { d : ℕ // 0 < d ∧ n.Coprime d })
    ⟨fun q => ⟨q.num, q.den, q.den_pos, q.coprime_num_den⟩,
      fun ⟨num, den, prop⟩ => ⟨⟨num, den, Nat.pos_iff_ne_zero.mp prop.1, prop.2⟩,
        Rat.num_nonneg.mp (Int.natCast_nonneg num)⟩,
      fun ⟨⟨num, _, _, _⟩, hq⟩ => by lift num to ℕ using Rat.num_nonneg.mpr hq; rfl,
      Eq.refl⟩

end NNRat
