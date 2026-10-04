/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

module

public import Tengoku

@[expose] public section

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 1

We will be considering colorings in 2 colors of n (distinct) points
A₁, A₂, ..., Aₙ. Call such a coloring "good" if there exist three points
Aᵢ, Aⱼ, A₂ⱼ₋ᵢ, 1 ≤ i < 2j - i ≤ n, which are colored the same color.

Find the least natural number n (n ≥ 3) such that all colorings
of n points are good.
-/

namespace Bulgaria1998P1

abbrev coloring_is_good {m : ℕ} (color : Set.Icc 1 m → Fin 2) : Prop :=
  ∃ i j : Set.Icc 1 m,
    i < j ∧
    ∃ h3 : 2 * j.val - i ∈ Set.Icc 1 m,
    color i = color j ∧ color i = color ⟨2 * j - i, h3⟩

abbrev all_colorings_are_good (m : ℕ) : Prop :=
  3 ≤ m ∧ ∀ color : Set.Icc 1 m → Fin 2, coloring_is_good color

lemma lemma1 {m n : ℕ} (hmn : m ≤ n) (hm : all_colorings_are_good m) :
    all_colorings_are_good n := by
  constructor
  · exact hm.1.trans hmn
  · intro c
    let c' : Set.Icc 1 m → Fin 2 :=
      fun x ↦ c ⟨x.val, by rw [Set.mem_Icc]; exact ⟨x.prop.1, x.prop.2.trans hmn⟩⟩
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij1, hij2, hc1, hc2⟩ := hm.2 c'
    obtain ⟨hi1, hi2⟩ := Set.mem_Icc.mp hi
    obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
    use ⟨i, Set.mem_Icc.mpr ⟨hi1, hi2.trans hmn⟩⟩
    use ⟨j, Set.mem_Icc.mpr ⟨hj1, hj2.trans hmn⟩⟩
    simp only [Subtype.mk_lt_mk, Set.mem_Icc, tsub_le_iff_right, exists_and_left]
    simp only [Subtype.mk_lt_mk] at hij1
    refine ⟨hij1, ?_⟩
    simp only [Set.mem_Icc, tsub_le_iff_right] at hij2
    simp only [c'] at hc1
    refine ⟨hc1, ?_⟩
    have hij2' : 1 ≤ 2 * j - i ∧ 2 * j ≤ n + i :=
       ⟨hij2.1, le_add_of_le_add_right hij2.2 hmn⟩
    use hij2'

def coloring_of_eight {n : ℕ} : Set.Icc 1 n → Fin 2
| ⟨1, _⟩ => 0
| ⟨2, _⟩ => 1
| ⟨3, _⟩ => 0
| ⟨4, _⟩ => 1
| ⟨5, _⟩ => 1
| ⟨6, _⟩ => 0
| ⟨7, _⟩ => 1
| ⟨8, _⟩ => 0
| _ => 0 -- unreachable

lemma lemma2 :
    ∃ f : Set.Icc 1 8 → Fin 2, ¬coloring_is_good f := by
  use coloring_of_eight
  decide

abbrev solution_value : ℕ := 9

private def check9 (f : Fin 9 → Fin 2) : Bool :=
  (List.finRange 9).any fun i =>
    (List.finRange 9).any fun j =>
      decide (i < j) &&
        if h : 2 * j.val - i.val < 9 then
          decide (f i = f j) && decide (f i = f ⟨2 * j.val - i.val, h⟩)
        else false

private def toFin9 (color : Set.Icc 1 9 → Fin 2) : Fin 9 → Fin 2 :=
  fun i => color ⟨i.val + 1, Set.mem_Icc.mpr (by lia)⟩

end Bulgaria1998P1
