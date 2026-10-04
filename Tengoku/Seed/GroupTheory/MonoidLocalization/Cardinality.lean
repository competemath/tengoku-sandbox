/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.GroupTheory.MonoidLocalization.Basic
public import Tengoku.Seed.GroupTheory.OreLocalization.Cardinality

/-!

# Cardinality of localizations of commutative monoids

This file contains some results on cardinality of localizations.

-/

public section

universe u

open Cardinal

namespace Localization

variable {M : Type u} [CommMonoid M] (S : Submonoid M)

@[to_additive]
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S

end Localization
