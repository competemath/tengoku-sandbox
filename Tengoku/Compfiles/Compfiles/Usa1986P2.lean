/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1986, Problem 2

Five professors attended a lecture. Each fell asleep just twice. For each pair
there was a moment when both were asleep. Show that there was a moment when
three of them were asleep.
-/

namespace Usa1986P2

/-- Each professor `p : Fin 5` takes two naps, and nap `k : Fin 2` of professor
`p` is the closed interval `[s p k, e p k]`. Professor `p` is asleep at time
`t` if `t` belongs to one of these two nap intervals. -/
def Asleep (s e : Fin 5 → Fin 2 → ℝ) (p : Fin 5) (t : ℝ) : Prop :=
  ∃ k : Fin 2, s p k ≤ t ∧ t ≤ e p k

/-- The ten pairs of professors, as the 2-element subsets of `Fin 5`. -/
def pairs : Finset (Finset (Fin 5)) := Finset.powersetCard 2 Finset.univ

/-- The type of pairs of professors. -/
abbrev PairSet := { A : Finset (Fin 5) // A ∈ pairs }

variable {s e : Fin 5 → Fin 2 → ℝ}

open Classical in
/-- Candidate "first moments" for a set `A` of professors: nap-start times of
members of `A` at which every member of `A` is asleep. -/
noncomputable def cands (s e : Fin 5 → Fin 2 → ℝ) (A : Finset (Fin 5)) : Finset ℝ :=
  Finset.filter (fun u ↦ ∀ p ∈ A, Asleep s e p u)
    (A.biUnion fun p ↦ Finset.image (s p) Finset.univ)

/-- Membership in `cands`: a nap-start time of a member of `A` at which every
member of `A` is asleep. -/
lemma mem_cands {A : Finset (Fin 5)} {u : ℝ} :
    u ∈ cands s e A ↔
      (∃ p ∈ A, ∃ k : Fin 2, s p k = u) ∧ ∀ p ∈ A, Asleep s e p u := by
  unfold cands
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and]

/-- If all members of a nonempty set `A` of professors are asleep at time `t`,
then some nap-start time `u ≤ t` of a member of `A` is already a moment when
all members of `A` are asleep. -/
lemma exists_mem_cands_le {A : Finset (Fin 5)} (hA : A.Nonempty) {t : ℝ}
    (ht : ∀ p ∈ A, Asleep s e p t) : ∃ u ∈ cands s e A, u ≤ t := by
  have ht' : ∀ p : A, ∃ k : Fin 2, s p.1 k ≤ t ∧ t ≤ e p.1 k := fun p ↦ ht p.1 p.2
  choose k hk₁ hk₂ using ht'
  obtain ⟨p₀, -, hmax⟩ :=
    A.attach.exists_max_image (fun p ↦ s p.1 (k p)) (Finset.attach_nonempty_iff.mpr hA)
  refine ⟨s p₀.1 (k p₀), mem_cands.mpr ⟨⟨p₀.1, p₀.2, k p₀, rfl⟩, fun p hp ↦
    ⟨k ⟨p, hp⟩, hmax ⟨p, hp⟩ (Finset.mem_attach _ _), (hk₁ p₀).trans (hk₂ ⟨p, hp⟩)⟩⟩, hk₁ p₀⟩

/-- The first moment at which all members of `A` are simultaneously asleep. -/
noncomputable def f (s e : Fin 5 → Fin 2 → ℝ) (A : Finset (Fin 5))
    (h : (cands s e A).Nonempty) : ℝ := (cands s e A).min' h

/-- All members of `A` are asleep at the first common moment. -/
lemma f_asleep {A : Finset (Fin 5)} {h : (cands s e A).Nonempty} :
    ∀ p ∈ A, Asleep s e p (f s e A h) := by
  have hm : (cands s e A).min' h ∈ cands s e A := Finset.min'_mem _ h
  exact (mem_cands.mp hm).2

/-- The first common moment is a nap-start time of some member of `A`. -/
lemma f_mem {A : Finset (Fin 5)} {h : (cands s e A).Nonempty} :
    ∃ p ∈ A, ∃ k : Fin 2, f s e A h = s p k := by
  have hm : (cands s e A).min' h ∈ cands s e A := Finset.min'_mem _ h
  obtain ⟨p, hp, k, hkp⟩ := (mem_cands.mp hm).1
  exact ⟨p, hp, k, hkp.symm⟩

/-- The first common moment is at most any moment at which all members of `A`
are asleep. -/
lemma f_le {A : Finset (Fin 5)} (hA : A.Nonempty) {h : (cands s e A).Nonempty}
    {t : ℝ} (ht : ∀ p ∈ A, Asleep s e p t) : f s e A h ≤ t := by
  obtain ⟨u, hu, hut⟩ := exists_mem_cands_le hA ht
  exact (Finset.min'_le _ _ hu).trans hut

/-- Pairs of professors have candidate first moments. -/
lemma cands_nonempty
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    {A : Finset (Fin 5)} (hA : A.card = 2) : (cands s e A).Nonempty := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hA
  obtain ⟨t, hpt, hqt⟩ := hsleep p q hpq
  have ht : ∀ r ∈ ({p, q} : Finset (Fin 5)), Asleep s e r t := by
    intro r hr
    rw [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hpt
    · exact hqt
  obtain ⟨u, hu, -⟩ := exists_mem_cands_le ⟨p, Finset.mem_insert_self p {q}⟩ ht
  exact ⟨u, hu⟩

/-- The first moment when both members of a pair `A` are asleep. -/
noncomputable def F
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) : ℝ :=
  f s e A.1 (cands_nonempty hsleep (Finset.mem_powersetCard.mp A.2).2)

/-- Both members of a pair are asleep at the pair's first common moment. -/
lemma F_asleep
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) {p : Fin 5} (hp : p ∈ A.1) : Asleep s e p (F hsleep A) :=
  f_asleep p hp

/-- A pair's first common moment is a falling-asleep event: it is the start
time of a nap of one of the two members. -/
lemma F_mem
    (hsleep : ∀ p q : Fin 5, p ≠ q → ∃ t, Asleep s e p t ∧ Asleep s e q t)
    (A : PairSet) : ∃ p ∈ A.1, ∃ k : Fin 2, F hsleep A = s p k :=
  f_mem

end Usa1986P2
