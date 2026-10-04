/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.CategoryTheory.Groupoid
public import Tengoku.Seed.CategoryTheory.Discrete.Basic
/-!

# Discrete categories are groupoids
-/

public section

namespace CategoryTheory

variable {C : Type*}

instance : Groupoid (Discrete C) := { inv := fun h ↦ ⟨h.1.symm⟩ }

instance [Category* C] [IsDiscrete C] : IsGroupoid C where

end CategoryTheory
