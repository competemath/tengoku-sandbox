/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2007, Problem 3

In a mathematical competition some competitors are (mutual) friends.
Call a group of competitors a clique if each two of them are friends.
Given that the largest size of a clique is even, prove that the
competitors can be arranged into two rooms such that the largest size
of a clique contained in one room is the same as the largest size of
a clique contained in the other room.
-/

namespace Imo2007P3

/-- The largest size of a clique of the graph `G` all of whose vertices lie in `A`. -/
noncomputable def maxCliqueCard {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  sSup {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n}

section

variable {V : Type*} (G : SimpleGraph V)

lemma bddAbove_cliqueCard {A : Finset V} :
    BddAbove {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n} :=
  ⟨A.card, fun n hn ↦ by
    obtain ⟨s, hsA, -, rfl⟩ := hn
    exact Finset.card_le_card hsA⟩

lemma nonempty_cliqueCard {A : Finset V} :
    {n : ℕ | ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = n}.Nonempty :=
  ⟨0, ∅, Finset.empty_subset A, by rw [Finset.coe_empty]; exact Set.pairwise_empty G.Adj,
    Finset.card_empty⟩

lemma card_le_maxCliqueCard {A s : Finset V} (hsA : s ⊆ A) (hsc : G.IsClique s) :
    s.card ≤ maxCliqueCard G A :=
  le_csSup (bddAbove_cliqueCard G) ⟨s, hsA, hsc, rfl⟩

lemma maxCliqueCard_le {A : Finset V} {n : ℕ}
    (h : ∀ s : Finset V, s ⊆ A → G.IsClique s → s.card ≤ n) :
    maxCliqueCard G A ≤ n := by
  apply csSup_le (nonempty_cliqueCard G)
  rintro m ⟨s, hsA, hsc, rfl⟩
  exact h s hsA hsc

lemma maxCliqueCard_le_card {A : Finset V} : maxCliqueCard G A ≤ A.card :=
  maxCliqueCard_le G fun _ hsA _ ↦ Finset.card_le_card hsA

lemma maxCliqueCard_eq_card_of_isClique {A : Finset V} (hA : G.IsClique A) :
    maxCliqueCard G A = A.card :=
  le_antisymm (maxCliqueCard_le_card G) (card_le_maxCliqueCard G (Finset.Subset.refl A) hA)

lemma maxCliqueCard_mono {A B : Finset V} (hAB : A ⊆ B) :
    maxCliqueCard G A ≤ maxCliqueCard G B :=
  maxCliqueCard_le G fun _ hsA hsc ↦ card_le_maxCliqueCard G (hsA.trans hAB) hsc

lemma isClique_of_subset {s t : Finset V} (hst : s ⊆ t) (ht : G.IsClique t) :
    G.IsClique s :=
  ht.subset (Finset.coe_subset.mpr hst)

lemma isClique_union {s t : Finset V} (hs : G.IsClique s) (ht : G.IsClique t)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≠ y → G.Adj x y) : G.IsClique (s ∪ t) := by
  intro x hx y hy hxy
  rw [Set.mem_union] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hs hx hy hxy
  · exact hst x hx y hy hxy
  · exact (hst y hy x hx hxy.symm).symm
  · exact ht hx hy hxy

lemma maxCliqueCard_insert_le [DecidableEq V] {A : Finset V} (x : V) :
    maxCliqueCard G (insert x A) ≤ maxCliqueCard G A + 1 := by
  apply maxCliqueCard_le G
  intro s hsA hsc
  by_cases hx : x ∈ s
  · have h1 : s.erase x ⊆ A := Finset.subset_insert_iff.mp hsA
    have h2 := card_le_maxCliqueCard G h1 (isClique_of_subset G (Finset.erase_subset x s) hsc)
    have h3 : s.card = (s.erase x).card + 1 := (Finset.card_erase_add_one hx).symm
    lia
  · have h1 : s ⊆ A := by
      intro y hy
      rcases Finset.mem_insert.mp (hsA hy) with h | h
      · exact absurd (h ▸ hy) hx
      · exact h
    exact (card_le_maxCliqueCard G h1 hsc).trans (by lia)

lemma maxCliqueCard_erase_le [DecidableEq V] {A : Finset V} (x : V) :
    maxCliqueCard G A ≤ maxCliqueCard G (A.erase x) + 1 := by
  by_cases hx : x ∈ A
  · have h := maxCliqueCard_insert_le G x (A := A.erase x)
    rwa [Finset.insert_erase hx] at h
  · rw [Finset.erase_eq_of_notMem hx]
    lia

lemma exists_isClique_card_eq {A : Finset V} :
    ∃ s : Finset V, s ⊆ A ∧ G.IsClique s ∧ s.card = maxCliqueCard G A := by
  obtain ⟨s, hsA, hsc, hs⟩ := Nat.sSup_mem (nonempty_cliqueCard G) (bddAbove_cliqueCard G)
  exact ⟨s, hsA, hsc, hs⟩

end

end Imo2007P3
