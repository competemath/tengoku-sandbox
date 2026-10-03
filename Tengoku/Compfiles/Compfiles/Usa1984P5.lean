/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karl Mehltretter, Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1984, Problem 5

P(x) is a polynomial of degree 3n such that

  P(0) = P(3) = ... = P(3n) = 2,
  P(1) = P(4) = ... = P(3n - 2) = 1,
  P(2) = P(5) = ... = P(3n - 1) = 0,
  and P(3n + 1) = 730.

Determine n.
-/

namespace Usa1984P5

open Polynomial

abbrev solution_value : ℕ := 4

/- Proof sketch: since deg P = 3n < 3n + 1, the (3n+1)-th forward finite
difference of P at 0 vanishes, which gives a linear relation between
P(3n+1) = 730 and the values 2, 1, 0 at 0, ..., 3n.  Writing the periodic
values via a primitive cube root of unity ζ as
P(j) = 1 + (1-ζ)/3 · ζ^j + (1-ζ²)/3 · ζ^{2j} and using the binomial theorem,
the relation reduces to (-1)^(3n+1) · W = -2187 with
W = (1-ζ)^(3n+2) + (1-ζ²)^(3n+2).  Since (1-ζ)³ = 3(ζ²-ζ) and (ζ²-ζ)² = -3,
for n = 2s we get W = 3·(-27)^s, forcing 27^s = 729 = 27², so s = 2 and n = 4;
for n = 2s+1 we get W = (-27)^(s+1), forcing 27^(s+1) = 2187, impossible since
27² = 729 < 2187 < 19683 = 27³. -/

/-- The forward difference operator on real sequences. -/
def fwdDiff (f : ℕ → ℝ) : ℕ → ℝ := fun n ↦ f (n + 1) - f n

/-- The `m`-fold forward difference at `0` is the alternating binomial sum. -/
lemma fwdDiff_iter_zero (m : ℕ) (f : ℕ → ℝ) :
    fwdDiff^[m] f 0 = ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f j := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih (fwdDiff f)]
    have step : ∀ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * fwdDiff f j
          = (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f (j + 1)
            - (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f j := by
      intro j _
      show (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * (f (j + 1) - f j) = _
      ring
    rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib]
    have rhs_eq : ∑ j ∈ Finset.range (m + 2),
        (-1 : ℝ) ^ (m + 1 - j) * ((m + 1).choose j : ℝ) * f j
        = (∑ j ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m + 1 - (j + 1)) * ((m + 1).choose (j + 1) : ℝ) * f (j + 1))
          + (-1 : ℝ) ^ (m + 1) * f 0 := by
      simp only [Finset.sum_range_succ']
      rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [rhs_eq]
    have key : ∀ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + 1 - (j + 1)) * ((m + 1).choose (j + 1) : ℝ) * f (j + 1)
          = (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * f (j + 1)
            + (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.choose_succ_succ]
      have e : m + 1 - (j + 1) = m - j := by lia
      rw [e]
      push_cast
      ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    have reindex : ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
        = ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i
          - (-1 : ℝ) ^ (m + 1) * f 0 := by
      have g_def : ∀ j ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
            = (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (j + 1) := by
        intro j _
        show (-1 : ℝ) ^ (m - j) * (m.choose (j + 1) : ℝ) * f (j + 1)
          = (-1 : ℝ) ^ (m + 1 - (j + 1)) * (m.choose (j + 1) : ℝ) * f (j + 1)
        rw [Nat.succ_sub_succ]
      have hge := Finset.sum_congr rfl g_def
      rw [hge]
      have h1 := Finset.sum_range_succ'
        (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1)
      have h2 := Finset.sum_range_succ
        (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1)
      have hgm : (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) (m + 1) = 0 := by
        simp [Nat.choose_succ_self]
      have hg0 : (fun i ↦ (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i) 0
          = (-1 : ℝ) ^ (m + 1) * f 0 := by
        simp
      linear_combination -h1 + h2 - hg0 + hgm
    rw [reindex]
    have gneg : ∀ i ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m + 1 - i) * (m.choose i : ℝ) * f i
          = -((-1 : ℝ) ^ (m - i) * (m.choose i : ℝ) * f i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.sub_add_comm <| Nat.le_of_succ_le_succ hi, pow_succ]
      ring
    rw [Finset.sum_congr rfl gneg, Finset.sum_neg_distrib]
    ring

/-- The `m`-fold forward difference of a polynomial of degree `< m` vanishes. -/
lemma poly_fwdDiff (m : ℕ) (P : ℝ[X]) (hP : P.natDegree < m) (k : ℕ) :
    fwdDiff^[m] (fun j ↦ P.eval (j : ℝ)) k = 0 := by
  induction m generalizing P with
  | zero => simp at hP
  | succ m ih =>
    have fwdDiff_const {a : ℝ} : fwdDiff (fun _ : ℕ ↦ (a : ℝ)) = (fun _ : ℕ ↦ (0 : ℝ)) := by
      unfold fwdDiff
      simp
    have hz {a : ℝ} : ∀ t : ℕ, fwdDiff^[t + 1] (fun _ : ℕ ↦ (a : ℝ)) k = 0 := by
      intro t
      induction t generalizing a with
      | zero =>
        rw [Function.iterate_one]
        apply funext_iff.mp fwdDiff_const
      | succ t iht =>
        rw [Function.iterate_succ_apply, fwdDiff_const]
        apply iht
    by_cases hP0 : P = 0
    · subst hP0
      simp_rw [eval_zero]
      exact hz m
    · by_cases hdeg0 : P.natDegree = 0
      · have hPc : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        rw [hPc]
        simp only [eval_C]
        exact hz m
      · have hPm : P.natDegree ≤ m := by lia
        have hP1 : 1 ≤ P.natDegree := by lia
        have hm : 1 ≤ m := by lia
        have hcomp_deg : (P.comp (X + C 1)).natDegree = P.natDegree := by
          rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
        have hcomp_ne : P.comp (X + C 1) ≠ 0 := by
          intro hzero
          rw [hzero, Polynomial.natDegree_zero] at hcomp_deg
          lia
        have hcomp_lc : (P.comp (X + C 1)).leadingCoeff = P.leadingCoeff := by
          have hnd : (X + C (1 : ℝ)).natDegree ≠ 0 := by
            rw [Polynomial.natDegree_X_add_C]; norm_num
          rw [Polynomial.leadingCoeff_comp hnd,
            (Polynomial.monic_X_add_C (1 : ℝ)).leadingCoeff]
          simp
        have hdeg_lt : (P.comp (X + C 1) - P).degree < P.degree := by
          have hd : (P.comp (X + C 1)).degree = P.degree := by
            rw [Polynomial.degree_eq_natDegree hcomp_ne, Polynomial.degree_eq_natDegree hP0,
              hcomp_deg]
          have hlt := Polynomial.degree_sub_lt_left hd hcomp_ne hcomp_lc
          rwa [hd] at hlt
        have hQ : (P.comp (X + C 1) - P).natDegree < m := by
          rcases eq_or_ne (P.comp (X + C 1) - P) 0 with hz0 | hnz
          · rw [hz0, Polynomial.natDegree_zero]; lia
          · have h2 := (Polynomial.natDegree_lt_natDegree_iff hnz).mpr hdeg_lt
            lia
        rw [Function.iterate_succ_apply]
        convert ih _ hQ with j
        simp [fwdDiff]

end Usa1984P5
