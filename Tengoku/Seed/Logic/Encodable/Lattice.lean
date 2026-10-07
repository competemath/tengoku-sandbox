/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Tengoku.Seed.Logic.Encodable.Basic
public import Tengoku.Seed.Logic.Pairwise
public import Tengoku.Seed.Data.Set.Subsingleton

/-!
# Lattice operations on encodable types

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `MeasureTheory` folder.
-/

public section

open Set

namespace Encodable

variable {α : Type*} {β : Type*} [Encodable β]

/--
@isnad1 id=eq.0h3v.s6.990e03792b2d from=seed src=0 shape=6ab31f78 vocab=4bdb69ea
-/
theorem iSup_decode₂ [CompleteLattice α] (f : β → α) :
    ⨆ (i : ℕ) (b ∈ decode₂ β i), f b = (⨆ b, f b) := by
  rw [iSup_comm]
  simp only [mem_decode₂, iSup_iSup_eq_right]

/--
@isnad1 id=eq.0h3v.s5.4f5efb5e5a2f from=seed src=0 shape=6fbd449c vocab=fa7ad568
-/
theorem iUnion_decode₂ (f : β → Set α) : ⋃ (i : ℕ) (b ∈ decode₂ β i), f b = ⋃ b, f b :=
  iSup_decode₂ f

/--
@isnad1 id=var.0h7v.s6.2942beaeb7c3 from=seed src=0 shape=a5571afa vocab=201e0d2c
-/
@[elab_as_elim]
theorem iUnion_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp only [Option.mem_def, iUnion_of_empty, iUnion_empty, reduceCtorEq]
    apply H0
  | some b => by
    convert! H1 b
    simp

open scoped Function in -- required for scoped `on` notation
/--
@isnad1 id=pairwise.1h3v.s7.bb2b54fb4492 from=seed src=0 shape=fe7f9473 vocab=bc9faecc
-/
theorem iUnion_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) := by
  rintro i j ij
  refine disjoint_left.mpr fun x => ?_
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩

end Encodable
