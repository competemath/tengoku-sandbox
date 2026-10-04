/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public meta import Tengoku.Seed.Tactic.Ring.Basic
public meta import Tengoku.Seed.Data.PNat.Basic
public import Tengoku.Seed.Data.PNat.Basic
public import Tengoku.Seed.Tactic.Ring.Basic

/-!
# Additional instances for `ring` over `PNat`

This adds some instances which enable `ring` to work on `PNat` even though it is not a commutative
semiring, by lifting to `Nat`.
-/

public meta section

namespace Mathlib.Tactic.Ring

instance : CSLift ℕ+ Nat where
  lift := PNat.val
  inj := PNat.coe_injective

-- FIXME: this `no_index` seems to be in the wrong place, but
-- #synth CSLiftVal (3 : ℕ+) _ doesn't work otherwise
instance {n} : CSLiftVal (no_index (OfNat.ofNat (n + 1)) : ℕ+) (n + 1) := ⟨rfl⟩

instance {n h} : CSLiftVal (Nat.toPNat n h) n := ⟨rfl⟩


instance {n} : CSLiftVal (Nat.succPNat n) (n + 1) := ⟨rfl⟩

instance {n} : CSLiftVal (Nat.toPNat' n) (n.pred + 1) := ⟨rfl⟩

instance {n k} : CSLiftVal (PNat.divExact n k) (n.div k + 1) := ⟨rfl⟩

instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n + k) (n' + k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k k'} [h1 : CSLiftVal (n : ℕ+) n'] [h2 : CSLiftVal (k : ℕ+) k'] :
    CSLiftVal (n * k) (n' * k') := ⟨by simp [h1.1, h2.1, CSLift.lift]⟩

instance {n n' k} [h1 : CSLiftVal (n : ℕ+) n'] :
    CSLiftVal (n ^ k) (n' ^ k) := ⟨by simp [h1.1, CSLift.lift]⟩

end Ring

end Mathlib.Tactic
