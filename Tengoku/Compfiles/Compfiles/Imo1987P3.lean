/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1987, Problem 3

Let $x_1, x_2, \ldots, x_n$ be real numbers satisfying
$x_1^2 + x_2^2 + \cdots + x_n^2 = 1$. Prove that for every integer $k \geq 2$
there are integers $a_1, a_2, \ldots, a_n$, not all zero, such that
$|a_i| \leq k - 1$ for all $i$, and
$$|a_1 x_1 + a_2 x_2 + \cdots + a_n x_n| \leq \frac{(k - 1)\sqrt{n}}{k^n - 1}.$$
-/

namespace Imo1987P3

-- Solution formalized from https://prase.cz/kalva/imo/isoln/isoln873.html

/- The proof is an application of the pigeonhole principle. Consider the $k^n$
sums $\sum_i b_i |x_i|$ with $b_i \in \{0, 1, \ldots, k - 1\}$. By the
Cauchy-Schwarz inequality, $\sum_i |x_i| \leq \sqrt{n}$, so all of these sums lie
in the interval $[0, (k-1)\sqrt{n}]$. Splitting this interval into $k^n - 1$ equal
subintervals, two of the sums land in the same subinterval; their difference has
the form $\sum_i a_i |x_i|$ with $|a_i| \leq k - 1$ and not all $a_i$ zero, and its
absolute value is at most $\frac{(k-1)\sqrt{n}}{k^n - 1}$. Flipping the sign of
$a_i$ wherever $x_i < 0$ turns this into the required estimate for
$\sum_i a_i x_i$. -/

/-- The sum `∑ i, bᵢ * |x i|` attached to a tuple `b : Fin n → Fin k` of coefficients. -/
noncomputable def S {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b : Fin n → Fin k) : ℝ :=
  ∑ i, ((b i : ℕ) : ℝ) * |x i|

/-- Cauchy-Schwarz: `∑ i, |x i| ≤ √n` whenever `∑ i, x i ^ 2 = 1`. -/
lemma sum_abs_le_sqrt {n : ℕ} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1) :
    ∑ i, |x i| ≤ Real.sqrt n := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun i => |x i|) (fun _ => (1 : ℝ))
  have h2 : ∑ i, |x i| ^ 2 = 1 := by
    rw [← hx]
    exact Finset.sum_congr rfl fun i _ => sq_abs (x i)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h2] at h
  apply Real.le_sqrt_of_sq_le
  linarith [h]

/-- Every coefficient of `b : Fin k` is at most `k - 1`, as a real number. -/
lemma fin_coe_le {k : ℕ} (hk : 2 ≤ k) (b : Fin k) : ((b : ℕ) : ℝ) ≤ (k : ℝ) - 1 := by
  have h : (b : ℕ) ≤ k - 1 := Nat.le_pred_of_lt b.isLt
  calc ((b : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h
  _ = (k : ℝ) - 1 := by rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]

/-- Every coefficient of `b : Fin k` is at most `k - 1`, as an integer. -/
lemma fin_coe_le_int {k : ℕ} (hk : 2 ≤ k) (b : Fin k) : ((b : ℕ) : ℤ) ≤ (k : ℤ) - 1 := by
  have h : (b : ℕ) ≤ k - 1 := Nat.le_pred_of_lt b.isLt
  calc ((b : ℕ) : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by exact_mod_cast h
  _ = (k : ℤ) - 1 := by rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]

lemma S_nonneg {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b : Fin n → Fin k) : 0 ≤ S x b :=
  Finset.sum_nonneg fun i _ => by positivity

lemma S_le {n : ℕ} {x : Fin n → ℝ} (hx : ∑ i, x i ^ 2 = 1)
    {k : ℕ} (hk : 2 ≤ k) (b : Fin n → Fin k) :
    S x b ≤ ((k : ℝ) - 1) * Real.sqrt n := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  calc S x b ≤ ∑ i, ((k : ℝ) - 1) * |x i| := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (fin_coe_le hk (b i)) (abs_nonneg _)
  _ = ((k : ℝ) - 1) * ∑ i, |x i| := by rw [Finset.mul_sum]
  _ ≤ ((k : ℝ) - 1) * Real.sqrt n :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt hx) (by linarith)

/-- Pure floor lemma: if `u, v ≤ m` have the same clamped floor, then `|u - v| ≤ 1`. -/
lemma floor_min_sub_le {u v : ℝ} {m : ℤ} (hum : u ≤ (m : ℝ)) (hvm : v ≤ (m : ℝ))
    (h : min ⌊u⌋ (m - 1) = min ⌊v⌋ (m - 1)) : |u - v| ≤ 1 := by
  wlog huv : u ≤ v generalizing u v with H
  · rw [abs_sub_comm]
    exact H hvm hum h.symm (not_le.mp huv).le
  · have h1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    have h2 : v < (⌊v⌋ : ℝ) + 1 := Int.lt_floor_add_one v
    rcases le_total ⌊v⌋ (m - 1) with hc | hc
    · rw [min_eq_left hc] at h
      have h3 : ⌊v⌋ ≤ ⌊u⌋ := h ▸ min_le_left ⌊u⌋ (m - 1)
      have h4 : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_mono huv
      have h5 : (⌊u⌋ : ℝ) = (⌊v⌋ : ℝ) := by exact_mod_cast le_antisymm h4 h3
      rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
      linarith
    · rw [min_eq_right hc] at h
      have h8 : m - 1 ≤ ⌊u⌋ := h ▸ min_le_left ⌊u⌋ (m - 1)
      have h9 : ((m - 1 : ℤ) : ℝ) ≤ u := Int.le_floor.mp h8
      have h10 : ((m - 1 : ℤ) : ℝ) = (m : ℝ) - 1 := by push_cast; ring
      rw [h10] at h9
      rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
      linarith

/-- The choice of integer coefficients: take the differences `bᵢ - b'ᵢ`,
flipping the sign wherever `x i < 0`. -/
noncomputable def coef {n : ℕ} (x : Fin n → ℝ) {k : ℕ} (b b' : Fin n → Fin k) (i : Fin n) : ℤ :=
  (if 0 ≤ x i then (1 : ℤ) else -1) * (((b i : ℕ) : ℤ) - ((b' i : ℕ) : ℤ))

lemma coef_cast_mul {n : ℕ} {x : Fin n → ℝ} {k : ℕ} (b b' : Fin n → Fin k) (i : Fin n) :
    (coef x b b' i : ℝ) * x i = (((b i : ℕ) : ℝ) - ((b' i : ℕ) : ℝ)) * |x i| := by
  unfold coef
  by_cases h : 0 ≤ x i
  · rw [ite_eq_left h, abs_of_nonneg h]
    push_cast
    ring
  · rw [ite_eq_right h, abs_of_neg (lt_of_not_ge h)]
    push_cast
    ring

end Imo1987P3
