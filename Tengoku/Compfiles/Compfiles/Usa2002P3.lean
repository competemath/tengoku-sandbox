/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 2002, Problem 3

Prove that any monic polynomial (a polynomial with leading coefficient 1)
of degree n with real coefficients is the average of two monic polynomials
of degree n with n real roots.
-/

namespace Usa2002P3

open Polynomial Filter Asymptotics

/-- If `ξ` is strictly increasing at consecutive arguments below `n`,
then it is injective on `Finset.range n`. -/
theorem injOn_range_of_step {n : ℕ} {ξ : ℕ → ℝ}
    (h : ∀ i, i + 1 < n → ξ i < ξ (i + 1)) :
    Set.InjOn ξ (Finset.range n) := by
  have key : ∀ k : ℕ, ∀ i : ℕ, i + (k + 1) < n → ξ i < ξ (i + (k + 1)) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact h i (by simpa using hi)
    | succ k ih =>
      intro i hi
      have h1 : i + (k + 1) < n := by lia
      exact (ih i h1).trans (h (i + (k + 1)) (by lia))
  intro i hi j hj hij
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hji : j = i + (j - i - 1 + 1) := by lia
    have hlt' := key (j - i - 1) i (by lia)
    rw [← hji] at hlt'
    exact absurd hij (ne_of_lt hlt')
  · exact heq
  · have hji : i = j + (i - j - 1 + 1) := by lia
    have hlt' := key (i - j - 1) j (by lia)
    rw [← hji] at hlt'
    exact absurd hij (ne_of_gt hlt')

/-- A nonzero real polynomial of degree `n` that has `n` distinct real roots
has exactly `n` roots (counted with multiplicity), and in particular it splits. -/
theorem card_roots_eq_n {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    {ξ : ℕ → ℝ} (hinj : Set.InjOn ξ (Finset.range n))
    (hroot : ∀ i ∈ Finset.range n, p.eval (ξ i) = 0) :
    p.roots.card = n ∧ p.Splits := by
  have hsub : ((Finset.range n).image ξ).val ≤ p.roots := by
    rw [Multiset.le_iff_subset (Finset.nodup _)]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (show a ∈ (Finset.range n).image ξ from ha)
    exact (p.mem_roots hp0).mpr (hroot i hi)
  have hcard : ((Finset.range n).image ξ).card = n := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have h1 : n ≤ p.roots.card := by
    have hle := Multiset.card_le_card hsub
    rw [← hcard]
    exact hle
  have h2 : p.roots.card ≤ n := hn ▸ p.card_roots'
  exact ⟨le_antisymm h2 h1, splits_iff_card_roots.mpr (by rw [le_antisymm h2 h1, hn])⟩

/-- A nonzero real polynomial of degree `n` that has a root in each of `n`
open intervals `(L i, R i)` arranged in increasing order (`R i ≤ L (i+1)`)
has exactly `n` real roots and splits. -/
theorem card_roots_eq_n_of_intervals {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    {L R : ℕ → ℝ} (hstep : ∀ i, i + 1 < n → R i ≤ L (i + 1))
    (hex : ∀ i, i < n → ∃ x ∈ Set.Ioo (L i) (R i), p.eval x = 0) :
    p.roots.card = n ∧ p.Splits := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℕ → ℝ, ∀ i (hi : i < n),
      ξ i ∈ Set.Ioo (L i) (R i) ∧ p.eval (ξ i) = 0 := by
    refine ⟨fun i => if h : i < n then Classical.choose (hex i h) else 0, fun i hi => ?_⟩
    simp only [dite_eq_left hi]
    exact Classical.choose_spec (hex i hi)
  have hmono : ∀ i, i + 1 < n → ξ i < ξ (i + 1) := by
    intro i hi
    have h1 := ((hξ i (by lia)).1).2
    have h2 := ((hξ (i + 1) hi).1).1
    exact lt_trans (lt_of_lt_of_le h1 (hstep i hi)) h2
  exact card_roots_eq_n hp0 hn (injOn_range_of_step hmono)
    (fun i hi => (hξ i (Finset.mem_range.mp hi)).2)

/-- Intermediate value theorem for polynomials: if `p` changes sign between
`a` and `b`, then `p` has a root in the open interval `(a, b)`. -/
theorem exists_root_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo' hab.le p.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc, hce⟩
  · obtain ⟨c, hc, hce⟩ := intermediate_value_Ioo hab.le p.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc, hce⟩

/-- Let `p` be a nonzero real polynomial of degree `n` whose values at the
integers `1, ..., n` alternate in sign, so that `p` has a root in each of the
`n - 1` intervals `(i, i+1)`. If moreover `p` changes sign on one of the two
"tails" `(-∞, 1)` or `(n, ∞)`, then `p` has exactly `n` real roots and splits. -/
theorem card_roots_and_splits {p : ℝ[X]} {n : ℕ} (hp0 : p ≠ 0) (hn : p.natDegree = n)
    (hmul : ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
      p.eval (i : ℝ) * p.eval ((i + 1 : ℕ) : ℝ) < 0)
    (htail : (∃ a₁ : ℝ, a₁ < 1 ∧ p.eval a₁ * p.eval 1 < 0) ∨
             (∃ a₂ : ℝ, (n : ℝ) < a₂ ∧ p.eval (n : ℝ) * p.eval a₂ < 0)) :
    p.roots.card = n ∧ p.Splits := by
  rcases htail with ⟨a₁, ha₁, hmul₁⟩ | ⟨a₂, ha₂, hmul₂⟩
  · -- The extra root lies in `(a₁, 1)`, to the left of all the integer points.
    refine card_roots_eq_n_of_intervals hp0 hn (L := fun i : ℕ => if i = 0 then a₁ else (i : ℝ))
      (R := fun i : ℕ => ((i + 1 : ℕ) : ℝ)) ?_ ?_
    · intro i _
      rw [ite_eq_right (by lia : i + 1 ≠ 0)]
    · intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [ite_eq_left rfl]
        obtain ⟨c, hc, hce⟩ := exists_root_of_eval_mul_neg ha₁ hmul₁
        refine ⟨c, ?_, hce⟩
        rw [show ((0 + 1 : ℕ) : ℝ) = 1 by simp]
        exact hc
      · rw [ite_eq_right hi0]
        exact exists_root_of_eval_mul_neg
          (show (i : ℝ) < ((i + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_add_one i)
          (hmul i (by lia) (by lia))
  · -- The extra root lies in `(n, a₂)`, to the right of all the integer points.
    refine card_roots_eq_n_of_intervals hp0 hn (L := fun i : ℕ => ((i + 1 : ℕ) : ℝ))
      (R := fun i : ℕ => if i < n - 1 then ((i + 2 : ℕ) : ℝ) else a₂) ?_ ?_
    · intro i hi
      rw [ite_eq_left (by lia : i < n - 1)]
    · intro i hi
      by_cases hi' : i < n - 1
      · rw [ite_eq_left hi']
        exact exists_root_of_eval_mul_neg
          (show ((i + 1 : ℕ) : ℝ) < ((i + 2 : ℕ) : ℝ) by exact_mod_cast Nat.lt_add_one (i + 1))
          (hmul (i + 1) (by lia) (by lia))
      · rw [ite_eq_right hi']
        have hieq : i + 1 = n := by lia
        obtain ⟨c, hc, hce⟩ := exists_root_of_eval_mul_neg ha₂ hmul₂
        refine ⟨c, ?_, hce⟩
        rw [hieq]
        exact hc

/-- A monic real polynomial of positive degree takes arbitrarily large
positive values. -/
theorem exists_eval_pos {p : ℝ[X]} (hm : p.Monic) (hd : 1 ≤ p.natDegree) (B : ℝ) :
    ∃ c : ℝ, B < c ∧ 0 < p.eval c := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by lia)
  have hnn : 0 ≤ p.leadingCoeff := by
    have hlc : p.leadingCoeff = 1 := hm
    rw [hlc]
    exact zero_le_one
  have hT : Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hnn
  obtain ⟨c, hc1, hcB⟩ := ((hT.eventually_ge_atTop (1 : ℝ)).and (eventually_gt_atTop B)).exists
  exact ⟨c, hcB, by linarith⟩

/-- A monic real polynomial `p` of degree `n`, multiplied by `(-1)^n`, takes
arbitrarily large positive values at large negative arguments. -/
theorem exists_eval_neg_one_pow_pos {p : ℝ[X]} (hm : p.Monic) (hd : 1 ≤ p.natDegree) (B : ℝ) :
    ∃ a : ℝ, a < B ∧ 0 < (-1 : ℝ) ^ p.natDegree * p.eval a := by
  have hn0 : p.natDegree ≠ 0 := by lia
  have hlc : p.leadingCoeff = 1 := hm
  have hE : (fun x : ℝ => p.eval x) ~[atBot] fun x : ℝ => x ^ p.natDegree := by
    have h := p.isEquivalent_atBot_lead
    rw [hlc] at h
    simpa using h
  have hE2 : (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * p.eval x) ~[atBot]
      fun x : ℝ => (-1 : ℝ) ^ p.natDegree * x ^ p.natDegree := by
    have h := (IsEquivalent.refl (u := fun _ : ℝ => (-1 : ℝ) ^ p.natDegree)).mul hE
    exact h
  have hT : Tendsto (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * x ^ p.natDegree) atBot atTop := by
    have h1 : Tendsto (fun x : ℝ => (-x) ^ p.natDegree) atBot atTop :=
      (tendsto_pow_atTop hn0).comp tendsto_neg_atBot_atTop
    refine h1.congr' ?_
    filter_upwards with x
    rw [neg_pow]
  have hT2 : Tendsto (fun x : ℝ => (-1 : ℝ) ^ p.natDegree * p.eval x) atBot atTop :=
    hE2.symm.tendsto_atTop hT
  obtain ⟨a, ha1, haB⟩ := ((hT2.eventually_ge_atTop (1 : ℝ)).and (eventually_lt_atBot B)).exists
  exact ⟨a, haB, by linarith⟩

end Usa2002P3
