/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 1973, Problem 5

Show that the cube roots of three distinct primes cannot be terms in an
arithmetic progression (whether consecutive or not).
-/

namespace Usa1973P5

/-- Cubing a real cube root. -/
lemma cbrt_cubed {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  have e : (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, e, Real.rpow_one]

/-- The prime `p` occurs with multiplicity exactly one in a product of three
pairwise distinct primes `p`, `q`, `r`. -/
lemma factorization_pqr {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) : (p * q * r).factorization p = 1 := by
  have h : (p * q * r).factorization
      = p.factorization + q.factorization + r.factorization := by
    rw [Nat.factorization_mul (mul_ne_zero hp.pos.ne' hq.pos.ne') hr.pos.ne',
      Nat.factorization_mul hp.pos.ne' hq.pos.ne']
  rw [h, Finsupp.add_apply, Finsupp.add_apply, hp.factorization, hq.factorization,
    hr.factorization, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq,
    Finsupp.single_eq_of_ne hpr]
  rfl

/-- A product of three pairwise distinct primes times a nonzero cube is never a
cube: comparing the exponent of `p` in the prime factorizations of both sides of
`p * q * r * b ^ 3 = a ^ 3` would give `1 + 3k = 3j`. -/
lemma not_cube_mul_cube {p q r a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (_hqr : q ≠ r) (hpr : p ≠ r) (hb : b ≠ 0) :
    p * q * r * b ^ 3 ≠ a ^ 3 := by
  intro h
  have hcon := congrArg (Nat.factorization · p) h
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero hp.pos.ne' hq.pos.ne')
      hr.pos.ne') (pow_ne_zero 3 hb), Nat.factorization_pow,
    Nat.factorization_pow] at hcon
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    factorization_pqr hp hq hr hpq hpr] at hcon
  lia

/-- The cube root of a product of three pairwise distinct primes is irrational:
it cannot be written as a quotient of two integers. Indeed, from
`∛(pqr) = A / B` we would get `p * q * r * B³ = A³` in `ℕ`, contradicting
`not_cube_mul_cube`. -/
lemma cube_root_pqr_ne_rat {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {A B : ℤ} (hB : B ≠ 0)
    (h : ((p * q * r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = (A : ℝ) / (B : ℝ)) : False := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB
  have h1 : ((p * q * r : ℕ) : ℝ) ^ ((1 : ℝ) / 3) * (B : ℝ) = (A : ℝ) := by
    rw [h, div_mul_cancel₀ _ hB']
  have h2 : (((p * q * r : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 * (B : ℝ) ^ 3 = (A : ℝ) ^ 3 := by
    have h1' := congrArg (· ^ 3) h1
    rwa [mul_pow] at h1'
  rw [cbrt_cubed (by positivity)] at h2
  have h3 : ((p * q * r : ℕ) : ℤ) * B ^ 3 = A ^ 3 := by exact_mod_cast h2
  have h4 : p * q * r * B.natAbs ^ 3 = A.natAbs ^ 3 := by
    have h3' := congrArg Int.natAbs h3
    rwa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast] at h3'
  exact not_cube_mul_cube hp hq hr hpq hqr hpr (Int.natAbs_pos.mpr hB).ne' h4

/-- The algebraic heart of the argument. If `∛q = ∛p + m d` and `∛r = ∛p + n d`,
then `n ∛q - m ∛r = (n - m) ∛p`; cubing that relation and regrouping expresses
`3 m n (n - m) ∛p ∛q ∛r` as an integer polynomial in `p, q, r`. -/
lemma key_algebra {x y z : ℝ} {m n : ℤ}
    (h1 : (n : ℝ) * y - (m : ℝ) * z = ((n - m : ℤ) : ℝ) * x) :
    3 * (n : ℝ) * (m : ℝ) * ((n - m : ℤ) : ℝ) * (y * z * x)
      = (n : ℝ) ^ 3 * y ^ 3 - (m : ℝ) ^ 3 * z ^ 3 - ((n - m : ℤ) : ℝ) ^ 3 * x ^ 3 := by
  have h2 : ((n : ℝ) * y - (m : ℝ) * z) ^ 3
      = (n : ℝ) ^ 3 * y ^ 3 - (m : ℝ) ^ 3 * z ^ 3
        - 3 * (n : ℝ) * (m : ℝ) * (y * z) * ((n : ℝ) * y - (m : ℝ) * z) := by ring
  rw [h1] at h2
  linear_combination h2

-- If `∛p, ∛q, ∛r` are terms of an arithmetic progression with common
-- difference `d`, at integer positions differing by `m` and `n` from the
-- position of `∛p`, then `∛q = ∛p + m d` and `∛r = ∛p + n d` as below, so it
-- suffices to show that this is impossible for distinct primes `p, q, r`.

end Usa1973P5
