/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.CharP.Defs
public import Tengoku.Seed.Algebra.Ring.Pi

/-!
# Characteristic of semirings of functions
-/

public section


universe u v

namespace CharP

instance pi (ι : Type u) [hi : Nonempty ι] (R : Type v) [Semiring R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  ⟨fun x =>
    let ⟨i⟩ := hi
    Iff.symm <|
      (CharP.cast_eq_zero_iff R p x).symm.trans
        ⟨fun h =>
          funext fun j =>
            show Pi.evalRingHom (fun _ => R) j (↑x : ι → R) = 0 by rw [map_natCast, h],
          fun h ↦ by rw [← map_natCast (Pi.evalRingHom (fun _ : ι => R) i) x, h, map_zero]⟩⟩

-- diamonds
instance pi' (ι : Type u) [Nonempty ι] (R : Type v) [CommRing R] (p : ℕ) [CharP R p] :
    CharP (ι → R) p :=
  CharP.pi ι R p

end CharP
