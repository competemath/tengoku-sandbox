/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Filtered.Basic
public import Tengoku.Seed.CategoryTheory.WithTerminal.Basic

/-!
# Further lemmas on `WithTerminal`

These lemmas and instances need more imports.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace WithTerminal

open IsCofiltered in
instance [IsCofilteredOrEmpty C] : IsCofiltered (WithTerminal C) where
  cone_objs x y :=
    match x, y with
    | star, y => ⟨y, default, 𝟙 y, trivial⟩
    | x, star => ⟨x, 𝟙 x, default, trivial⟩
    | of x, of y => ⟨.of <| min x y, minToLeft _ _, minToRight _ _, trivial⟩
  cone_maps x y f g :=
    match x, y with
    | star, _ => ⟨star, 𝟙 _, (IsIso.eq_comp_inv f).mp rfl⟩
    | x, star => ⟨x, 𝟙 _, Subsingleton.elim _ _⟩
    | of _, of _ => ⟨.of <| eq f g, eqHom _ _, eq_condition _ _⟩

end WithTerminal

namespace WithInitial

instance [IsFilteredOrEmpty C] : IsFiltered (WithInitial C) :=
  have := IsCofiltered.of_equivalence (opEquiv C).symm
  isFiltered_of_isCofiltered_op _

end WithInitial

end CategoryTheory
