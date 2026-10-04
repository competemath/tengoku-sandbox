/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.Set.Finite.Basic
public import Tengoku.Seed.Data.Set.Finite.Lattice
public import Tengoku.Seed.Data.Set.Finite.Range
public import Tengoku.Seed.Data.Set.Lattice
public import Tengoku.Seed.Data.Finite.Vector

/-!
# Finiteness of sets of lists

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

namespace List
variable (α : Type*) [Finite α] (n : ℕ)

lemma finite_length_eq : {l : List α | l.length = n}.Finite := List.Vector.finite

lemma finite_length_lt : {l : List α | l.length < n}.Finite := by
  convert! (Finset.range n).finite_toSet.biUnion fun i _ ↦ finite_length_eq α i; ext; simp

lemma finite_length_le : {l : List α | l.length ≤ n}.Finite := by
  simpa [Nat.lt_succ_iff] using finite_length_lt α (n + 1)

end List
