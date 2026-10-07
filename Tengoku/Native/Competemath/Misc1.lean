/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P23

/-- competemath.com problem 23. -/
theorem symmetric_pursuit (x y z : ℝ) (h1 : x + y + z = 1) (h2 : x ^ 2 + y ^ 2 + z ^ 2 = 5) (h3 : x ^ 3 + y ^ 3 + z ^ 3 = 7) : x ^ 4 + y ^ 4 + z ^ 4 = 17 := by
  have h1sq : (x + y + z) ^ 2 = 1 := by rw [h1]; norm_num
  have expand2 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by ring
  have e2 : x * y + y * z + z * x = -2 := by linarith
  have h1cu : (x + y + z) ^ 3 = 1 := by rw [h1]; norm_num
  have expand3 : (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * ((x + y + z) * (x * y + y * z + z * x)) - 3 * (x * y * z) := by ring
  have prod_e1_e2 : (x + y + z) * (x * y + y * z + z * x) = -2 := by rw [h1, e2]; ring
  have e3 : x * y * z = 0 := by linarith
  have newton4 : x ^ 4 + y ^ 4 + z ^ 4 = (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3) - (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) + x * y * z * (x + y + z) := by ring
  have prod1 : (x + y + z) * (x ^ 3 + y ^ 3 + z ^ 3) = 7 := by rw [h1, h3]; ring
  have prod2 : (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) = -10 := by rw [e2, h2]; norm_num
  have prod3 : x * y * z * (x + y + z) = 0 := by rw [e3]; ring
  linarith

end Native.Competemath.P23

namespace Native.Competemath.P44

/-- competemath.com problem 44. -/
theorem plus_one_pivot (f : ℕ → ℕ) (hmul : ∀ m n : ℕ, f (m * n) = f m + f n + f m * f n) (hbase : f 2 = 1) (k : ℕ) : f (2 ^ k) = 2 ^ k - 1 := by
  have h1 : f 1 = 0 := by
    have h := hmul 1 1
    simp only [one_mul] at h
    have hfm : 0 ≤ f 1 * f 1 := Nat.zero_le _
    omega
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, hmul, hbase, ih]
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [mul_one]
    omega

end Native.Competemath.P44

namespace Native.Competemath.P83

/-- competemath.com problem 83. -/
theorem feast_table_row : 4 * 7 - 2 * 6 = 16 := by decide

end Native.Competemath.P83

namespace Native.Competemath.P137

/-- competemath.com problem 137. -/
theorem stern_pi_value (s : ℕ → ℕ) (h0 : s 0 = 0) (h1 : s 1 = 1)
    (heven : ∀ n, s (2 * n) = s n)
    (hodd : ∀ n, s (2 * n + 1) = s n + s (n + 1)) :
    s 7847424 = 134 := by
  have hP0 : s 0 = 0 ∧ s 1 = 1 := ⟨h0, h1⟩
  have hP1 : s 1 = 1 ∧ s 2 = 1 := ⟨by rw [show 1 = 2*0+1 from by norm_num, hodd]; rw [hP0.1, hP0.2], by rw [show 2 = 2*(0+1) from by norm_num, heven]; exact hP0.2⟩
  have hP2 : s 3 = 2 ∧ s 4 = 1 := ⟨by rw [show 3 = 2*1+1 from by norm_num, hodd]; rw [hP1.1, hP1.2], by rw [show 4 = 2*(1+1) from by norm_num, heven]; exact hP1.2⟩
  have hP3 : s 7 = 3 ∧ s 8 = 1 := ⟨by rw [show 7 = 2*3+1 from by norm_num, hodd]; rw [hP2.1, hP2.2], by rw [show 8 = 2*(3+1) from by norm_num, heven]; exact hP2.2⟩
  have hP4 : s 14 = 3 ∧ s 15 = 4 := ⟨by rw [show 14 = 2*7 from by norm_num, heven]; exact hP3.1, by rw [show 15 = 2*7+1 from by norm_num, hodd]; rw [hP3.1, hP3.2]⟩
  have hP5 : s 29 = 7 ∧ s 30 = 4 := ⟨by rw [show 29 = 2*14+1 from by norm_num, hodd]; rw [hP4.1, hP4.2], by rw [show 30 = 2*(14+1) from by norm_num, heven]; exact hP4.2⟩
  have hP6 : s 59 = 11 ∧ s 60 = 4 := ⟨by rw [show 59 = 2*29+1 from by norm_num, hodd]; rw [hP5.1, hP5.2], by rw [show 60 = 2*(29+1) from by norm_num, heven]; exact hP5.2⟩
  have hP7 : s 119 = 15 ∧ s 120 = 4 := ⟨by rw [show 119 = 2*59+1 from by norm_num, hodd]; rw [hP6.1, hP6.2], by rw [show 120 = 2*(59+1) from by norm_num, heven]; exact hP6.2⟩
  have hP8 : s 239 = 19 ∧ s 240 = 4 := ⟨by rw [show 239 = 2*119+1 from by norm_num, hodd]; rw [hP7.1, hP7.2], by rw [show 240 = 2*(119+1) from by norm_num, heven]; exact hP7.2⟩
  have hP9 : s 478 = 19 ∧ s 479 = 23 := ⟨by rw [show 478 = 2*239 from by norm_num, heven]; exact hP8.1, by rw [show 479 = 2*239+1 from by norm_num, hodd]; rw [hP8.1, hP8.2]⟩
  have hP10 : s 957 = 42 ∧ s 958 = 23 := ⟨by rw [show 957 = 2*478+1 from by norm_num, hodd]; rw [hP9.1, hP9.2], by rw [show 958 = 2*(478+1) from by norm_num, heven]; exact hP9.2⟩
  have hP11 : s 1915 = 65 ∧ s 1916 = 23 := ⟨by rw [show 1915 = 2*957+1 from by norm_num, hodd]; rw [hP10.1, hP10.2], by rw [show 1916 = 2*(957+1) from by norm_num, heven]; exact hP10.2⟩
  have hP12 : s 3831 = 88 ∧ s 3832 = 23 := ⟨by rw [show 3831 = 2*1915+1 from by norm_num, hodd]; rw [hP11.1, hP11.2], by rw [show 3832 = 2*(1915+1) from by norm_num, heven]; exact hP11.2⟩
  have hP13 : s 7663 = 111 ∧ s 7664 = 23 := ⟨by rw [show 7663 = 2*3831+1 from by norm_num, hodd]; rw [hP12.1, hP12.2], by rw [show 7664 = 2*(3831+1) from by norm_num, heven]; exact hP12.2⟩
  have hP14 : s 15327 = 134 ∧ s 15328 = 23 := ⟨by rw [show 15327 = 2*7663+1 from by norm_num, hodd]; rw [hP13.1, hP13.2], by rw [show 15328 = 2*(7663+1) from by norm_num, heven]; exact hP13.2⟩
  have hP15 : s 30654 = 134 ∧ s 30655 = 157 := ⟨by rw [show 30654 = 2*15327 from by norm_num, heven]; exact hP14.1, by rw [show 30655 = 2*15327+1 from by norm_num, hodd]; rw [hP14.1, hP14.2]⟩
  have hP16 : s 61308 = 134 ∧ s 61309 = 291 := ⟨by rw [show 61308 = 2*30654 from by norm_num, heven]; exact hP15.1, by rw [show 61309 = 2*30654+1 from by norm_num, hodd]; rw [hP15.1, hP15.2]⟩
  have hP17 : s 122616 = 134 ∧ s 122617 = 425 := ⟨by rw [show 122616 = 2*61308 from by norm_num, heven]; exact hP16.1, by rw [show 122617 = 2*61308+1 from by norm_num, hodd]; rw [hP16.1, hP16.2]⟩
  have hP18 : s 245232 = 134 ∧ s 245233 = 559 := ⟨by rw [show 245232 = 2*122616 from by norm_num, heven]; exact hP17.1, by rw [show 245233 = 2*122616+1 from by norm_num, hodd]; rw [hP17.1, hP17.2]⟩
  have hP19 : s 490464 = 134 ∧ s 490465 = 693 := ⟨by rw [show 490464 = 2*245232 from by norm_num, heven]; exact hP18.1, by rw [show 490465 = 2*245232+1 from by norm_num, hodd]; rw [hP18.1, hP18.2]⟩
  have hP20 : s 980928 = 134 ∧ s 980929 = 827 := ⟨by rw [show 980928 = 2*490464 from by norm_num, heven]; exact hP19.1, by rw [show 980929 = 2*490464+1 from by norm_num, hodd]; rw [hP19.1, hP19.2]⟩
  have hP21 : s 1961856 = 134 ∧ s 1961857 = 961 := ⟨by rw [show 1961856 = 2*980928 from by norm_num, heven]; exact hP20.1, by rw [show 1961857 = 2*980928+1 from by norm_num, hodd]; rw [hP20.1, hP20.2]⟩
  have hP22 : s 3923712 = 134 ∧ s 3923713 = 1095 := ⟨by rw [show 3923712 = 2*1961856 from by norm_num, heven]; exact hP21.1, by rw [show 3923713 = 2*1961856+1 from by norm_num, hodd]; rw [hP21.1, hP21.2]⟩
  have hP23 : s 7847424 = 134 ∧ s 7847425 = 1229 := ⟨by rw [show 7847424 = 2*3923712 from by norm_num, heven]; exact hP22.1, by rw [show 7847425 = 2*3923712+1 from by norm_num, hodd]; rw [hP22.1, hP22.2]⟩
  exact hP23.1

end Native.Competemath.P137

namespace Native.Competemath.P142

/-- competemath.com problem 142. -/
theorem lucas_gcd_property (a : ℕ → ℤ) (h0 : a 0 = 0) (h1 : a 1 = 1) (hrec : ∀ n, a (n + 2) = 4 * a (n + 1) - a n) : Int.gcd (a 2024) (a 3040) = 10864 := by
  have hCassini : ∀ n : ℕ, a (n+2) * a n - a (n+1) * a (n+1) = -1 := by
    intro n
    induction n with
    | zero => simp [h0, h1]
    | succ n ih =>
      have e1 := hrec n
      have e2 := hrec (n+1)
      linear_combination ih + a (n+1) * e2 - a (n+2) * e1
  have hCoprime : ∀ n : ℕ, IsCoprime (a n) (a (n+1)) := by
    intro n
    exact ⟨-(a (n+2)), a (n+1), by linarith [hCassini n]⟩
  have hAdd : ∀ m n : ℕ, a (m + n + 1) = a (m+1) * a (n+1) - a m * a n := by
    intro m n
    have key : ∀ n : ℕ, (a (m + n + 1) = a (m+1) * a (n+1) - a m * a n) ∧ (a (m + n + 2) = a (m+1) * a (n+2) - a m * a (n+1)) := by
      intro n
      induction n with
      | zero =>
        constructor
        · simp [h0, h1]
        · have e0 : a 2 = 4 * a 1 - a 0 := hrec 0
          simp [h0, h1] at e0
          have em : a (m+2) = 4 * a (m+1) - a m := hrec m
          simp [h1, e0]
          linarith [em]
      | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        constructor
        · have e : m + (n+1) + 1 = m + n + 2 := by ring
          rw [e]
          exact ih2
        · have eL : a (m + n + 3) = 4 * a (m + n + 2) - a (m + n + 1) := by
            have hh := hrec (m + n + 1)
            have e : m + n + 1 + 2 = m + n + 3 := by ring
            rwa [e] at hh
          have eRn : a (n + 3) = 4 * a (n + 2) - a (n + 1) := by
            have hh := hrec (n+1)
            have e : n + 1 + 2 = n + 3 := by ring
            rwa [e] at hh
          have hEn : a (n + 2) = 4 * a (n + 1) - a n := hrec n
          have goalEq : m + (n + 1) + 2 = m + n + 3 := by ring
          rw [goalEq, eL, ih1, ih2, eRn]
          linear_combination (a m) * hEn
    exact (key n).1
  have hPeriod : ∀ m n : ℕ, Int.gcd (a m) (a (n + m)) = Int.gcd (a m) (a n) := by
    intro m n
    match m with | 0 => simp | m'+1 => ?_
    have heq : n + (m' + 1) = m' + n + 1 := by ring
    rw [heq, hAdd m' n]
    rw [sub_eq_add_neg, add_comm (a (m'+1) * a (n+1)) (-(a m' * a n)), mul_comm (a (m'+1)) (a (n+1)), Int.gcd_add_mul_right_right]
    simp only [Int.gcd_neg]
    have hc : IsCoprime (a (m'+1)) (a m') := (hCoprime m').symm
    have hcnat : (a (m'+1)).natAbs.Coprime (a m').natAbs := by
      rw [Int.isCoprime_iff_gcd_eq_one] at hc
      rw [Int.gcd] at hc
      exact hc
    rw [Int.gcd, Int.gcd, Int.natAbs_mul, Nat.gcd_comm (a (m'+1)).natAbs, Nat.Coprime.gcd_mul_left_cancel (a n).natAbs hcnat.symm, Nat.gcd_comm]
  have hDvdMul : ∀ m k : ℕ, a m ∣ a (m * k) := by
    intro m
    rcases m with _ | m'
    case zero => intro k; simp [h0]
    intro k; induction k with
    | zero => simp [h0]
    | succ k' ihk =>
      have heq : (m' + 1) * (k' + 1) = (m' + 1) * k' + m' + 1 := by ring
      rw [heq, hAdd ((m'+1)*k') m']
      exact dvd_sub (dvd_mul_left (a (m'+1)) (a ((m'+1)*k'+1))) (ihk.mul_right (a m'))
  have ha2 : a 2 = 4 := by simpa [h0, h1] using hrec 0
  have ha3 : a 3 = 15 := by simpa [ha2, h1] using hrec 1
  have ha4 : a 4 = 56 := by simpa [ha3, ha2] using hrec 2
  have ha5 : a 5 = 209 := by simpa [ha4, ha3] using hrec 3
  have ha6 : a 6 = 780 := by simpa [ha5, ha4] using hrec 4
  have ha7 : a 7 = 2911 := by simpa [ha6, ha5] using hrec 5
  have ha8 : a 8 = 10864 := by simpa [ha7, ha6] using hrec 6
  have step1 : Int.gcd (a 2024) (a 3040) = Int.gcd (a 2024) (a 1016) := by
    have h := hPeriod 2024 1016
    norm_num at h
    exact h
  have step2 : Int.gcd (a 2024) (a 1016) = Int.gcd (a 1016) (a 1008) := by
    have h := hPeriod 1016 1008
    norm_num at h
    rw [Int.gcd_comm (a 2024) (a 1016)]
    exact h
  have step3 : Int.gcd (a 1016) (a 1008) = Int.gcd (a 1008) (a 8) := by
    have h := hPeriod 1008 8
    norm_num at h
    rw [Int.gcd_comm (a 1016) (a 1008)]
    exact h
  have step4 : Int.gcd (a 1008) (a 8) = 10864 := by
    have hd : a 8 ∣ a 1008 := by
      have := hDvdMul 8 126
      norm_num at this
      exact this
    rw [Int.gcd_comm]
    have hnn : (0:ℤ) ≤ a 8 := by rw [ha8]; norm_num
    have := Int.gcd_eq_left hnn hd
    rw [ha8] at this ⊢
    exact_mod_cast this
  rw [step1, step2, step3, step4]

end Native.Competemath.P142

namespace Native.Competemath.P197

/-- competemath.com problem 197. -/
theorem circulant_det_value (S : ℕ → ℤ) (hS0 : S 0 = 2) (hS1 : S 1 = 1)
    (hSrec : ∀ n, S (n + 2) = S (n + 1) - S n) :
    S (2026 ^ 2026) - 2 * (-1 : ℤ) ^ (2026 ^ 2026) = -3 := by
  have h1 : ∀ n, S (n + 6) = S n := by
    have key : ∀ n, S (n + 6) = S n ∧ S (n + 7) = S (n + 1) := by
      intro n
      induction n with
      | zero =>
        have e2 : S 2 = S 1 - S 0 := hSrec 0
        have e3 : S 3 = S 2 - S 1 := hSrec 1
        have e4 : S 4 = S 3 - S 2 := hSrec 2
        have e5 : S 5 = S 4 - S 3 := hSrec 3
        have e6 : S 6 = S 5 - S 4 := hSrec 4
        have e7 : S 7 = S 6 - S 5 := hSrec 5
        constructor
        · show S 6 = S 0
          simp [hS0, hS1, e2, e3, e4, e5, e6]
        · show S 7 = S 1
          simp [hS0, hS1, e2, e3, e4, e5, e6, e7]
      | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have e8 : S (n + 6 + 2) = S (n + 6 + 1) - S (n + 6) := hSrec (n + 6)
        have idx1 : n + 6 + 2 = n + 8 := by omega
        have idx2 : n + 6 + 1 = n + 7 := by omega
        rw [idx1, idx2] at e8
        have e2 : S (n + 2) = S (n + 1) - S n := hSrec n
        have goal1 : S (n + 1 + 6) = S (n + 1) := by
          have idx3 : n + 1 + 6 = n + 7 := by omega
          rw [idx3]; exact ih2
        have goal2 : S (n + 1 + 7) = S (n + 1 + 1) := by
          have idx4 : n + 1 + 7 = n + 8 := by omega
          have idx5 : n + 1 + 1 = n + 2 := by omega
          rw [idx4, idx5, e8, ih1, ih2]
          exact e2.symm
        exact ⟨goal1, goal2⟩
    intro n
    exact (key n).1
  have h2 : ∀ k n, S (n + 6 * k) = S n := by
    intro k n
    induction k with
    | zero => simp
    | succ k ih =>
        have e : n + 6 * (k + 1) = (n + 6 * k) + 6 := by ring
        rw [e, h1, ih]
  have h3 : 2026 ^ 2026 % 6 = 4 := by
    rw [Nat.pow_mod]
    have e1 : (2026 : ℕ) % 6 = 4 := by decide
    rw [e1]
    have key : ∀ n, 4 ^ (n + 1) % 6 = 4 := by
      intro n
      induction n with
      | zero => decide
      | succ k ih => rw [pow_succ, Nat.mul_mod, ih]
    have h2026 : (2026 : ℕ) = 2025 + 1 := by decide
    rw [h2026]
    set_option maxRecDepth 4000 in
    set_option exponentiation.threshold 3000 in
    exact key 2025
  have h4 : S 4 = -1 := by
    have e2 : S 2 = S 1 - S 0 := hSrec 0
    have e3 : S 3 = S 2 - S 1 := hSrec 1
    have e4 : S 4 = S 3 - S 2 := hSrec 2
    simp [hS0, hS1, e2, e3, e4]
  have h6 : (-1 : ℤ) ^ (2026 ^ 2026) = 1 := by
    have h : Even (2026 ^ 2026) := (Nat.even_pow' (by decide)).mpr (by decide)
    exact h.neg_one_pow
  have h5 : S (2026 ^ 2026) = S 4 := by
    have hkey := h2 (2026 ^ 2026 / 6) (2026 ^ 2026 % 6)
    rw [Nat.mod_add_div] at hkey
    rw [h3] at hkey
    exact hkey
  rw [h5, h4, h6]
  ring

end Native.Competemath.P197

namespace Native.Competemath.P212

/-- competemath.com problem 212. -/
theorem giant_jacobi_symbol : jacobiSym (11 : ℤ) (5 ^ 2026 - 2 : ℕ) = -1 := by
  have h1 : Odd (5 ^ 2026 - 2 : ℕ) := by
    exact Nat.Odd.sub_even (le_trans (show (2:ℕ) ≤ 5^1 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 2026))) (Odd.pow (by decide)) (by decide)
  have h2 : (-1:ℤ) ^ ((11 / 2) * ((5 ^ 2026 - 2 : ℕ) / 2)) = -1 := by
    have htest := Nat.pow_mod 5 2026 4
    norm_num at htest
    have hge : (2:ℕ) ≤ 5^2026 := le_trans (show (2:ℕ) ≤ 5^1 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 2026))
    have hdiv2 : (5^2026 - 2 : ℕ) / 2 % 2 = 1 := by omega
    have hodd : Odd ((11/2) * ((5^2026 - 2 : ℕ)/2)) := by rw [show (11:ℕ)/2 = 5 by norm_num]; exact Odd.mul (by decide) (Nat.odd_iff.mpr hdiv2)
    exact Odd.neg_one_pow hodd
  have h3 : ((5 ^ 2026 - 2 : ℕ) : ℤ) ≡ (3:ℤ) [ZMOD (11:ℕ)] := by
    have hge : (2:ℕ) ≤ 5^2026 := le_trans (show (2:ℕ) ≤ 5^1 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by norm_num : 1 ≤ 2026))
    rw [Nat.cast_sub hge]
    push_cast
    rw [show (2026:ℕ) = 5*405+1 from by norm_num, pow_add, pow_mul, pow_one]
    have h5 : (5:ℤ)^5 ≡ 1 [ZMOD 11] := by decide
    have h405 := h5.pow 405
    simp only [one_pow] at h405
    have hmul := h405.mul_right 5
    simp only [one_mul] at hmul
    have hfinal := hmul.sub_right 2
    norm_num at hfinal
    exact hfinal
  have hrecip := jacobiSym.quadratic_reciprocity (show Odd (11:ℕ) by decide) h1
  rw [h2, jacobiSym.mod_left' h3] at hrecip
  norm_num [jacobiSym] at hrecip
  exact hrecip

end Native.Competemath.P212

namespace Native.Competemath.P214

/-- competemath.com problem 214. -/
theorem spanning_trees_two_adic_valuation :
    Nat.factorization ((4050:ℕ)^2026 * (4052:ℕ)^2024) 2 = 6074 := by
  have h4050 : (4050:ℕ) = 2 * 2025 := by norm_num
  have h4052 : (4052:ℕ) = 2^2 * 1013 := by norm_num
  have e1 : Nat.factorization (4050:ℕ) 2 = 1 := by
    rw [h4050, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2:ℕ) ∣ 2025)]
  have e2 : Nat.factorization (4052:ℕ) 2 = 2 := by
    rw [h4052, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 2),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (2:ℕ) ∣ 1013)]
  rw [Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_pow, Nat.factorization_pow]
  simp [e1, e2]

end Native.Competemath.P214

namespace Native.Competemath.P238

/-- competemath.com problem 238. -/
theorem enclosing_circle_radius :
    let k1 : ℚ := 1
    let k2 : ℚ := 1/2
    let k3 : ℚ := 1/3
    let R : ℚ := 6
    let k4 : ℚ := -1/R
    (k1 + k2 + k3 + k4)^2 = 2*(k1^2 + k2^2 + k3^2 + k4^2) := by
  norm_num

end Native.Competemath.P238

namespace Native.Competemath.P240

/-- competemath.com problem 240. -/
theorem zorath_coins :
    (¬ ∃ a b c : ℕ, 4 * a + 7 * b + 9 * c = 10) ∧
    (∃ a b c : ℕ, 4 * a + 7 * b + 9 * c = 11) ∧
    (∃ a b c : ℕ, 4 * a + 7 * b + 9 * c = 12) ∧
    (∃ a b c : ℕ, 4 * a + 7 * b + 9 * c = 13) ∧
    (∃ a b c : ℕ, 4 * a + 7 * b + 9 * c = 14) := by
  refine ⟨?_, ⟨1,1,0,?_⟩, ⟨3,0,0,?_⟩, ⟨1,0,1,?_⟩, ⟨0,2,0,?_⟩⟩
  · rintro ⟨a,b,c,h⟩
    have hc : c ≤ 1 := by omega
    have hb : b ≤ 1 := by omega
    interval_cases c <;> interval_cases b <;> omega
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end Native.Competemath.P240

namespace Native.Competemath.P254

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 254. -/
lemma val_a3 (a : ℕ → ℕ) (h1 : a 1 = 2) (h2 : a 2 = 4) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) : a 3 = 6 :=
  by
    rw [hrec 1, h2, h1]

lemma val_a4 (a : ℕ → ℕ) (h2 : a 2 = 4) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h3 : a 3 = 6) : a 4 = 10 :=
  by
    rw [hrec 2, h3, h2]

lemma val_a5 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h3 : a 3 = 6) (h4 : a 4 = 10) : a 5 = 16 :=
  by
    rw [hrec 3, h3, h4]

lemma val_a6 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h4 : a 4 = 10) (h5 : a 5 = 16) : a 6 = 26 :=
  by
    have h := hrec 4
    rw [h4, h5] at h
    norm_num at h
    exact h

lemma val_a7 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h5 : a 5 = 16) (h6 : a 6 = 26) : a 7 = 42 :=
  by
    have h := hrec 5
    rw [h5, h6] at h
    simp [Nat.add_comm] at h
    exact h

lemma val_a8 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h6 : a 6 = 26) (h7 : a 7 = 42) : a 8 = 68 :=
  by
    rw [hrec 6, h6, h7]

lemma val_a9 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h7 : a 7 = 42) (h8 : a 8 = 68) : a 9 = 110 :=
  by
    have h := hrec 7
    rw [h]
    rw [h7, h8]

lemma val_a10 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h8 : a 8 = 68) (h9 : a 9 = 110) : a 10 = 178 :=
  by
    have h := hrec 8
    rw [h8, h9] at h
    rw [h]

lemma val_a11 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h9 : a 9 = 110) (h10 : a 10 = 178) : a 11 = 288 :=
  by
    have h := hrec 9
    rw [h, h9, h10]

lemma val_a12 (a : ℕ → ℕ) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) (h10 : a 10 = 178) (h11 : a 11 = 288) : a 12 = 466 :=
  by
    have h := hrec 10
    rw [h10, h11] at h
    norm_num at h
    exact h

theorem coin_flip_no_triple (a : ℕ → ℕ) (h1 : a 1 = 2) (h2 : a 2 = 4) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) : a 12 = 466 :=
  by
    have h3 : a 3 = a 2 + a 1 := hrec 1
    rw [h1, h2] at h3; norm_num at h3
    have h4 : a 4 = a 3 + a 2 := hrec 2
    rw [h3, h2] at h4; norm_num at h4
    have h5 : a 5 = a 4 + a 3 := hrec 3
    rw [h4, h3] at h5; norm_num at h5
    have h6 : a 6 = a 5 + a 4 := hrec 4
    rw [h5, h4] at h6; norm_num at h6
    have h7 : a 7 = a 6 + a 5 := hrec 5
    rw [h6, h5] at h7; norm_num at h7
    have h8 : a 8 = a 7 + a 6 := hrec 6
    rw [h7, h6] at h8; norm_num at h8
    have h9 : a 9 = a 8 + a 7 := hrec 7
    rw [h8, h7] at h9; norm_num at h9
    have h10 : a 10 = a 9 + a 8 := hrec 8
    rw [h9, h8] at h10; norm_num at h10
    have h11 : a 11 = a 10 + a 9 := hrec 9
    rw [h10, h9] at h11; norm_num at h11
    exact val_a12 a hrec h10 h11

end Native.Competemath.P254

namespace Native.Competemath.P257

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 257. -/
theorem tidy_strings_count (a : ℕ → ℕ) (h0 : a 0 = 1) (h1 : a 1 = 1) (hrec : ∀ n, a (n + 2) = a (n + 1) + a n) : a 12 = 233 :=
  by
    have : ∀ n, a n = Nat.fib (n + 1) := by
      intro n
      induction n using Nat.strongRecOn with
      | ind k ih =>
        match k with
        | 0 => simp [h0, Nat.fib_one]
        | 1 => simp [h1, Nat.fib_two]
        | k + 2 =>
          rw [hrec k, ih k (by omega), ih (k + 1) (by omega)]
          simp only [Nat.fib_add_two]
          ring
    rw [this]
    simp
    norm_num

end Native.Competemath.P257

namespace Native.Competemath.P260

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 260. -/
lemma quartic_diff_expand (k : ℤ) : k^4 - (k-1)^4 = 4 * k^3 - 6 * k^2 + 4 * k - 1 :=
  by
    ring

lemma sum_quartic_telescope_aux (n : ℕ) :
  ∑ k ∈ Finset.Icc 1 n, ((k : ℤ)^4 - ((k : ℤ) - 1)^4) = (n : ℤ)^4 :=
  by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by simp)]
      rw [ih]
      simp [pow_succ]

lemma summand_eq_diff (k : ℕ) : 4*(k:ℤ)^3 - 6*k^2 + 4*k - 1 = (k:ℤ)^4 - ((k:ℤ)-1)^4 :=
  by
    exact (quartic_diff_expand k).symm

lemma sum_eq_n4 (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (4*(k:ℤ)^3 - 6*k^2 + 4*k - 1) = (n:ℤ)^4 :=
  by
    rw [Finset.sum_congr rfl (fun k hk => summand_eq_diff k)]
    exact sum_quartic_telescope_aux n

theorem sum_quartic_telescope : ∑ k ∈ Finset.Icc 1 2026, (4 * (k:ℤ)^3 - 6 * k^2 + 4 * k - 1) = 16848365064976 :=
  by
    exact (sum_eq_n4 2026).trans (by norm_num)

end Native.Competemath.P260

namespace Native.Competemath.P263

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 263. -/
lemma cross_term_step (a : ℕ → ℤ)
    (hrec : ∀ n, a (n + 2) = 5 * a (n + 1) - a n)
    (n : ℕ) :
    a (n + 1) * a (n + 3) - (a (n + 2))^2 = a n * a (n + 2) - (a (n + 1))^2 :=
  by
    rw [hrec (n + 1), hrec n]
    ring

theorem cross_term_constant (a : ℕ → ℤ) (h0 : a 0 = 2) (h1 : a 1 = 5) (hrec : ∀ n, a (n + 2) = 5 * a (n + 1) - a n) : ∀ n, a n * a (n + 2) - (a (n + 1))^2 = 21 :=
  by
    have h2 : a 2 = 5 * a 1 - a 0 := hrec 0
    have hbase : a 0 * a 2 - a 1 ^ 2 = 21 := by simp [h0, h1, h2]
    intro n
    induction n with
    | zero => exact hbase
    | succ k ih =>
      rw [cross_term_step a hrec k]
      exact ih

end Native.Competemath.P263

namespace Native.Competemath.P264

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 264. -/
lemma period6 (a : ℕ → ℤ) (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) (n : ℕ) :
    a (n + 6) = a n :=
  by
    have e2 := hrec n
    have e3 := hrec (n+1)
    have e4 := hrec (n+2)
    have e5 := hrec (n+3)
    have e6 := hrec (n+4)
    simp only [show n+1+1 = n+2 from rfl, show n+2+1 = n+3 from rfl,
      show n+3+1 = n+4 from rfl, show n+4+1 = n+5 from rfl, show n+5+1 = n+6 from rfl] at *
    linarith [e2, e3, e4, e5, e6]

lemma periodic_mul (a : ℕ → ℤ) (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) (m i : ℕ) :
    a (6 * m + i) = a i :=
  by
    induction m with
    | zero => simp
    | succ m ih =>
      have heq : 6 * (m + 1) + i = (6 * m + i) + 6 := by ring
      rw [heq, period6 a hrec, ih]

lemma six_block_sum_zero (a : ℕ → ℤ) (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) (n : ℕ) :
    a n + a (n+1) + a (n+2) + a (n+3) + a (n+4) + a (n+5) = 0 :=
  by
    have e2 := hrec n
    have e3 := hrec (n+1)
    have e4 := hrec (n+2)
    have e5 := hrec (n+3)
    simp only [show n+1+1 = n+2 from rfl, show n+2+1 = n+3 from rfl,
      show n+3+1 = n+4 from rfl, show n+4+1 = n+5 from rfl] at *
    linarith [e2, e3, e4, e5]

lemma sum_mul6_zero (a : ℕ → ℤ) (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) (m : ℕ) :
    ∑ k ∈ Finset.range (6 * m), a k = 0 :=
  by
    induction m with
    | zero => simp
    | succ m ih =>
      have h6 : 6 * (m + 1) = 6 * m + 6 := by ring
      rw [h6, Finset.sum_range_add, ih, zero_add]
      have h := six_block_sum_zero a hrec (6 * m)
      simp [Finset.sum_range_succ]
      linarith [h]

lemma four_remainder (a : ℕ → ℤ) (h0 : a 0 = 3) (h1 : a 1 = 8)
    (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) :
    a 0 + a 1 + a 2 + a 3 = 13 :=
  by
    have e2 := hrec 0
    have e3 := hrec 1
    norm_num at e2 e3
    linarith [e2, e3]

theorem subtractive_seq_sum (a : ℕ → ℤ) (h0 : a 0 = 3) (h1 : a 1 = 8) (hrec : ∀ n, a (n + 2) = a (n + 1) - a n) : ∑ k ∈ Finset.range 2026, a k = 13 :=
  by
    have hsplit : (2026 : ℕ) = 6 * 337 + 4 := by norm_num
    rw [hsplit, Finset.sum_range_add, sum_mul6_zero a hrec 337]
    have hp0 := periodic_mul a hrec 337 0
    have hp1 := periodic_mul a hrec 337 1
    have hp2 := periodic_mul a hrec 337 2
    have hp3 := periodic_mul a hrec 337 3
    simp [Finset.sum_range_succ]
    rw [show 6*337+0 = 6*337 from rfl] at hp0
    rw [hp0, hp1, hp2, hp3]
    linarith [four_remainder a h0 h1 hrec]

end Native.Competemath.P264

namespace Native.Competemath.P265

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 265. -/
lemma b_two_pow (b : ℕ → ℕ) (h1 : b 1 = 1) (heven : ∀ n, b (2 * n) = b n) :
    ∀ n : ℕ, b (2 ^ n) = 1 :=
  by
    intro n
    induction n with
    | zero => simpa using h1
    | succ k ih =>
      have e1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [e1, heven, ih]

lemma b_two_pow_add_one (b : ℕ → ℕ) (h1 : b 1 = 1) (heven : ∀ n, b (2 * n) = b n)
    (hodd : ∀ n, b (2 * n + 1) = b n + b (n + 1)) :
    ∀ n : ℕ, b (2 ^ n + 1) = n + 1 :=
  by
    intro n
    induction n with
    | zero =>
      have e0 : (2 : ℕ) ^ 0 + 1 = 2 * 1 := by norm_num
      rw [e0, heven, h1]
    | succ k ih =>
      have e1 : (2 : ℕ) ^ (k + 1) + 1 = 2 * 2 ^ k + 1 := by ring
      rw [e1, hodd, b_two_pow b h1 heven k, ih]
      omega

theorem halving_sequence_land (b : ℕ → ℕ) (h0 : b 0 = 0) (h1 : b 1 = 1) (heven : ∀ n, b (2 * n) = b n) (hodd : ∀ n, b (2 * n + 1) = b n + b (n + 1)) : b (2 ^ 2026 + 1) = 2027 :=
  by
    have h := b_two_pow_add_one b h1 heven hodd 2026
    simpa using h

end Native.Competemath.P265

namespace Native.Competemath.P235

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 235. -/
theorem bakery_loaves : (fun x : ℕ => 2 * x + 3)^[9] 1 = 2045 :=
  by
    decide

end Native.Competemath.P235

namespace Native.Competemath.P243

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 243. -/
lemma twelve_pow_eq (k : ℕ) : (12:ℕ) ^ k = 2 ^ (2 * k) * 3 ^ k :=
  by
    rw [pow_mul, ← mul_pow]
    norm_num

lemma coprime_two_pow_three_pow (m n : ℕ) : Nat.Coprime (2 ^ m) (3 ^ n) :=
  by
    exact Nat.Coprime.pow m n (by norm_num)

lemma two_pow_2018_dvd_factorial_2026 : (2:ℕ) ^ 2018 ∣ Nat.factorial 2026 :=
  by
    rw [Nat.Prime.pow_dvd_factorial_iff (b := 12) Nat.prime_two (by norm_num)]
    decide

lemma not_two_pow_2020_dvd_factorial_2026 : ¬ (2:ℕ) ^ 2020 ∣ Nat.factorial 2026 :=
  by
    rw [Nat.Prime.pow_dvd_factorial_iff Nat.prime_two (b := 12) (by norm_num [Nat.log])]
    decide

lemma three_pow_1009_dvd_factorial_2026 : (3:ℕ) ^ 1009 ∣ Nat.factorial 2026 :=
  by
    have hp : Nat.Prime 3 := by norm_num
    rw [Nat.Prime.pow_dvd_factorial_iff hp (b := 8) (by norm_num)]
    decide

lemma twelve_pow_1009_dvd_factorial_2026 : (12:ℕ) ^ 1009 ∣ Nat.factorial 2026 :=
  by
    have h : (12:ℕ) ^ 1009 = 2 ^ 2018 * 3 ^ 1009 := by
      rw [twelve_pow_eq]
    rw [h]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_two_pow_three_pow 2018 1009)
      two_pow_2018_dvd_factorial_2026 three_pow_1009_dvd_factorial_2026

lemma not_twelve_pow_1010_dvd_factorial_2026 : ¬ (12:ℕ) ^ 1010 ∣ Nat.factorial 2026 :=
  by
    intro h
    apply not_two_pow_2020_dvd_factorial_2026
    refine dvd_trans ?_ h
    have h12 : (12:ℕ) ^ 1010 = 2 ^ 2020 * 3 ^ 1010 := by
      rw [show (12:ℕ) = 2 ^ 2 * 3 by norm_num, mul_pow, ← pow_mul]
    rw [h12]
    exact dvd_mul_right _ _

theorem factorial_base12_trailing_zeros :
    (12:ℕ)^1009 ∣ Nat.factorial 2026 ∧ ¬ (12:ℕ)^1010 ∣ Nat.factorial 2026 :=
  by
    have hp2 : Nat.Prime 2 := by norm_num
    have hp3 : Nat.Prime 3 := by norm_num
    have hb2 : Nat.log 2 2026 < 12 := Nat.log_lt_of_lt_pow (by norm_num) (by norm_num)
    have hb3 : Nat.log 3 2026 < 8 := Nat.log_lt_of_lt_pow (by norm_num) (by norm_num)
    have key2 : ∀ r : ℕ, ((2:ℕ) ^ r ∣ Nat.factorial 2026 ↔ r ≤ ∑ i ∈ Finset.Ico 1 12, 2026 / 2 ^ i) :=
      fun r => hp2.pow_dvd_factorial_iff hb2
    have key3 : ∀ r : ℕ, ((3:ℕ) ^ r ∣ Nat.factorial 2026 ↔ r ≤ ∑ i ∈ Finset.Ico 1 8, 2026 / 3 ^ i) :=
      fun r => hp3.pow_dvd_factorial_iff hb3
    have s2 : (∑ i ∈ Finset.Ico 1 12, 2026 / 2 ^ i) = 2018 := by decide
    have s3 : (∑ i ∈ Finset.Ico 1 8, 2026 / 3 ^ i) = 1010 := by decide
    have e1 : (12:ℕ)^1009 = 2^2018 * 3^1009 := by
      rw [show (12:ℕ) = 2^2*3 from rfl, mul_pow, ← pow_mul]
    constructor
    · rw [e1]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
      · exact Nat.Coprime.pow _ _ (by norm_num)
      · rw [key2, s2]
      · rw [key3, s3]; norm_num
    · intro h
      have h2 : (2:ℕ)^2020 ∣ Nat.factorial 2026 := by
        refine dvd_trans ?_ h
        refine ⟨3^1010, ?_⟩
        rw [show (12:ℕ) = 2^2*3 from rfl, mul_pow, ← pow_mul]
      rw [key2, s2] at h2
      omega

end Native.Competemath.P243

namespace Native.Competemath.P239

/-- competemath.com problem 239. -/
theorem circles_in_angle : IsLeast {n : ℕ | 0 < n ∧ (2026:ℝ) * (1/3)^(n-1) < 1} 8 := by
  constructor
  · exact ⟨by norm_num, by norm_num⟩
  · intro n hn
    obtain ⟨hpos, hlt⟩ := hn
    by_contra h
    simp only [not_le] at h
    interval_cases n <;> norm_num at hlt

end Native.Competemath.P239

namespace Native.Competemath.P98

/-- competemath.com problem 98. -/
theorem tortoise_head_start : 5 * 9 = 3 * 6 + 3 * 9 ∧ ∀ n < 9, 5 * n < 3 * 6 + 3 * n := by decide

end Native.Competemath.P98

namespace Native.Competemath.P50

/-- competemath.com problem 50. -/
theorem pell_step_preserves (x y : ℤ) (h : x ^ 2 - 8 * y ^ 2 = 1) : (3 * x + 8 * y) ^ 2 - 8 * (x + 3 * y) ^ 2 = 1 := by
  linarith [show (3 * x + 8 * y) ^ 2 - 8 * (x + 3 * y) ^ 2 = x ^ 2 - 8 * y ^ 2 from by ring]

end Native.Competemath.P50

namespace Native.Competemath.P89

/-- competemath.com problem 89. -/
theorem folded_ribbon : 2 ^ 3 + 1 = 9 := by decide

end Native.Competemath.P89

namespace Native.Competemath.P102

/-- competemath.com problem 102. -/
theorem candle_keeper : 16 + 16 / 4 + 16 / 4 / 4 = 21 := by decide

end Native.Competemath.P102

namespace Native.Competemath.P104

/-- competemath.com problem 104. -/
theorem dice_tower_hidden : 7 + 7 + (7 - 4) = 17 := by norm_num

end Native.Competemath.P104

namespace Native.Competemath.P55

private def lucasSeq : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucasSeq (n + 1) + lucasSeq n

/-- competemath.com problem 55. -/
theorem lucas_double (n : ℕ) : (lucasSeq (2 * n) : ℤ) = (lucasSeq n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n := by
  have key : ∀ n : ℕ, (lucasSeq (2*n) : ℤ) = (lucasSeq n : ℤ)^2 - 2*(-1:ℤ)^n ∧
                      (lucasSeq (2*n+1) : ℤ) = (lucasSeq n : ℤ) * (lucasSeq (n+1) : ℤ) - (-1:ℤ)^n ∧
                      (lucasSeq n : ℤ) * (lucasSeq (n+2) : ℤ) - (lucasSeq (n+1) : ℤ)^2 = 5*(-1:ℤ)^n := by
    intro n
    induction n with
    | zero => norm_num [lucasSeq]
    | succ n ih =>
      obtain ⟨hP, hQ, hR⟩ := ih
      have rec1 : (lucasSeq (n+2) : ℤ) = (lucasSeq (n+1) : ℤ) + (lucasSeq n : ℤ) := by
        norm_cast
      have rec2 : (lucasSeq (2*n+2) : ℤ) = (lucasSeq (2*n+1) : ℤ) + (lucasSeq (2*n) : ℤ) := by
        norm_cast
      have rec3 : (lucasSeq (2*n+3) : ℤ) = (lucasSeq (2*n+2) : ℤ) + (lucasSeq (2*n+1) : ℤ) := by
        norm_cast
      have rec4 : (lucasSeq (n+3) : ℤ) = (lucasSeq (n+2) : ℤ) + (lucasSeq (n+1) : ℤ) := by
        norm_cast
      have hpow : (-1:ℤ)^(n+1) = (-1:ℤ)^n * -1 := pow_succ (-1) n
      refine ⟨?_, ?_, ?_⟩
      · show (lucasSeq (2*n+2) : ℤ) = (lucasSeq (n+1) : ℤ)^2 - 2*(-1:ℤ)^(n+1)
        rw [hpow]
        linear_combination rec2 + hP + hQ + hR - (lucasSeq n : ℤ) * rec1
      · show (lucasSeq (2*n+3) : ℤ) = (lucasSeq (n+1) : ℤ) * (lucasSeq (n+2) : ℤ) - (-1:ℤ)^(n+1)
        rw [hpow]
        linear_combination rec3 + rec2 + hP + 2*hQ + hR - ((lucasSeq n : ℤ) + (lucasSeq (n+1) : ℤ)) * rec1
      · show (lucasSeq (n+1) : ℤ) * (lucasSeq (n+3) : ℤ) - (lucasSeq (n+2) : ℤ)^2 = 5*(-1:ℤ)^(n+1)
        rw [hpow]
        linear_combination (lucasSeq (n+1) : ℤ) * rec4 - hR - (lucasSeq (n+2) : ℤ) * rec1
  exact (key n).1

end Native.Competemath.P55

namespace Native.Competemath.P78

/-- competemath.com problem 78. -/
theorem sticker_doubler : (fun x => 2 * x - 1)^[5] 3 = 65 := by decide

end Native.Competemath.P78

namespace Native.Competemath.P71

/-- competemath.com problem 71. -/
theorem lyness_phoenix (a : ℕ → ℚ) (h1 : a 1 = 20) (h2 : a 2 = 26) (hrec : ∀ n ≥ 1, a (n + 2) = (a (n + 1) + 1) / a n) : a (10 ^ 2026 + 1) = 20 := by
  have hkey : ∀ k : ℕ, a (5 * k + 1) = 20 ∧ a (5 * k + 2) = 26 := by
    intro k
    induction k with
    | zero => simpa using ⟨h1, h2⟩
    | succ n ih =>
      obtain ⟨hx, hy⟩ := ih
      have e3 : a (5 * n + 3) = (a (5 * n + 2) + 1) / a (5 * n + 1) := by
        have h := hrec (5 * n + 1) (by omega)
        have i1 : 5 * n + 1 + 2 = 5 * n + 3 := by ring
        have i2 : 5 * n + 1 + 1 = 5 * n + 2 := by ring
        rw [i1, i2] at h
        exact h
      have e4 : a (5 * n + 4) = (a (5 * n + 3) + 1) / a (5 * n + 2) := by
        have h := hrec (5 * n + 2) (by omega)
        have i1 : 5 * n + 2 + 2 = 5 * n + 4 := by ring
        have i2 : 5 * n + 2 + 1 = 5 * n + 3 := by ring
        rw [i1, i2] at h
        exact h
      have e5 : a (5 * n + 5) = (a (5 * n + 4) + 1) / a (5 * n + 3) := by
        have h := hrec (5 * n + 3) (by omega)
        have i1 : 5 * n + 3 + 2 = 5 * n + 5 := by ring
        have i2 : 5 * n + 3 + 1 = 5 * n + 4 := by ring
        rw [i1, i2] at h
        exact h
      have e6 : a (5 * n + 6) = (a (5 * n + 5) + 1) / a (5 * n + 4) := by
        have h := hrec (5 * n + 4) (by omega)
        have i1 : 5 * n + 4 + 2 = 5 * n + 6 := by ring
        have i2 : 5 * n + 4 + 1 = 5 * n + 5 := by ring
        rw [i1, i2] at h
        exact h
      have e7 : a (5 * n + 7) = (a (5 * n + 6) + 1) / a (5 * n + 5) := by
        have h := hrec (5 * n + 5) (by omega)
        have i1 : 5 * n + 5 + 2 = 5 * n + 7 := by ring
        have i2 : 5 * n + 5 + 1 = 5 * n + 6 := by ring
        rw [i1, i2] at h
        exact h
      rw [hx, hy] at e3
      norm_num at e3
      rw [e3, hy] at e4
      norm_num at e4
      rw [e4, e3] at e5
      norm_num at e5
      rw [e5, e4] at e6
      norm_num at e6
      rw [e6, e5] at e7
      norm_num at e7
      have g1 : 5 * (n + 1) + 1 = 5 * n + 6 := by ring
      have g2 : 5 * (n + 1) + 2 = 5 * n + 7 := by ring
      rw [g1, g2]
      exact ⟨e6, e7⟩
  have hpow : 10 ^ 2026 = 5 * (2 * 10 ^ 2025) := by
    have h2026 : (2026:ℕ) = 2025 + 1 := by norm_num
    rw [h2026, pow_succ]
    omega
  have hfin := (hkey (2 * 10 ^ 2025)).1
  rw [hpow]
  exact hfin

end Native.Competemath.P71

namespace Native.Competemath.P84

/-- competemath.com problem 84. -/
theorem sawyers_puzzle : (12 / (4 - 1)) * (7 - 1) = 24 := by norm_num

end Native.Competemath.P84

namespace Native.Competemath.P85

/-- competemath.com problem 85. -/
theorem backwards_bus : 11 + 5 - 3 + 2 - 6 = 9 := by decide

end Native.Competemath.P85

namespace Native.Competemath.P88

/-- competemath.com problem 88. -/
theorem fruit_scale (a o p w : ℕ) (h1 : w = 2 * p) (h2 : p = 3 * o) (h3 : o = 2 * a) : w = 12 * a := by omega

end Native.Competemath.P88

namespace Native.Competemath.P111

/-- competemath.com problem 111. -/
theorem eisenstein_rep (k : ℕ) : Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (7 : ℤ) ^ k} = 6 * (k + 1) := by
  have h1 : Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (7 : ℤ) ^ 0} = 6 := by
    have hset : {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (7 : ℤ) ^ 0}
        = (↑({(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff, Prod.mk.injEq, pow_zero]
      constructor
      · intro h
        have hy1 : y ≤ 1 := by nlinarith [sq_nonneg (2*x+y)]
        have hy2 : -1 ≤ y := by nlinarith [sq_nonneg (2*x+y)]
        have hx1 : x ≤ 1 := by nlinarith [sq_nonneg (2*y+x)]
        have hx2 : -1 ≤ x := by nlinarith [sq_nonneg (2*y+x)]
        interval_cases x <;> interval_cases y <;> omega
      · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> ring
    rw [hset]
    simp
  have h2 : ∀ n : ℕ, Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (7 : ℤ) ^ (n + 1)}
      = Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = (7 : ℤ) ^ n} + 6 := by
        have FINITE : ∀ N : ℤ, 0 ≤ N → {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = N}.Finite := by
          intro N hN
          apply Set.Finite.subset ((Set.finite_Icc (-(2*N+1)) (2*N+1)).prod (Set.finite_Icc (-(2*N+1)) (2*N+1)))
          rintro ⟨x, y⟩ hxy
          simp only [Set.mem_setOf_eq] at hxy
          constructor <;> constructor <;> nlinarith [sq_nonneg (x+y), sq_nonneg (x-y), sq_nonneg x, sq_nonneg y]
        have INJ_pi : Function.Injective (fun p : ℤ × ℤ => (p.1 - 2*p.2, 2*p.1+3*p.2)) := by
          rintro ⟨x,y⟩ ⟨x',y'⟩ h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2⟩ := h
          simp only [Prod.mk.injEq]
          constructor <;> omega
        have INJ_pib : Function.Injective (fun p : ℤ × ℤ => (3*p.1+2*p.2, -2*p.1+p.2)) := by
          rintro ⟨x,y⟩ ⟨x',y'⟩ h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2⟩ := h
          simp only [Prod.mk.injEq]
          constructor <;> omega
        have INJ_77 : Function.Injective (fun p : ℤ × ℤ => (7*p.1, 7*p.2)) := by
          rintro ⟨x,y⟩ ⟨x',y'⟩ h
          simp only [Prod.mk.injEq] at h
          obtain ⟨e1, e2⟩ := h
          simp only [Prod.mk.injEq]
          constructor <;> omega
        have MAPS_pi : ∀ (m : ℕ) (x y : ℤ), x^2+x*y+y^2 = (7:ℤ)^m →
            (x-2*y)^2 + (x-2*y)*(2*x+3*y) + (2*x+3*y)^2 = (7:ℤ)^(m+1) := by
          intro m x y h
          have := h
          ring_nf
          ring_nf at this
          nlinarith [this]
        have MAPS_pib : ∀ (m : ℕ) (x y : ℤ), x^2+x*y+y^2 = (7:ℤ)^m →
            (3*x+2*y)^2 + (3*x+2*y)*(-2*x+y) + (-2*x+y)^2 = (7:ℤ)^(m+1) := by
          intro m x y h
          have := h
          ring_nf
          ring_nf at this
          nlinarith [this]
        have COVER : ∀ (m : ℕ) (x y : ℤ), x^2+x*y+y^2 = (7:ℤ)^(m+1) →
            (∃ x' y' : ℤ, x'^2+x'*y'+y'^2 = (7:ℤ)^m ∧ (x'-2*y', 2*x'+3*y') = (x,y)) ∨
            (∃ x' y' : ℤ, x'^2+x'*y'+y'^2 = (7:ℤ)^m ∧ (3*x'+2*y', -2*x'+y') = (x,y)) := by
          intro m x y h
          have hd : (7:ℤ) ∣ (x^2+x*y+y^2) := ⟨7^m, by rw [h]; exact pow_succ' 7 m⟩
          have key := (ZMod.intCast_zmod_eq_zero_iff_dvd (x^2+x*y+y^2) 7).mpr hd
          push_cast at key
          have h7 : ∀ a b : ZMod 7, a^2+a*b+b^2=0 → a=4*b ∨ a=2*b := by decide
          rcases h7 (x:ZMod 7) (y:ZMod 7) key with h1' | h1'
          · have key1 : ((x - 4*y : ℤ) : ZMod 7) = 0 := by push_cast; linear_combination h1'
            have hdvd : (7:ℤ) ∣ (x - 4*y) := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x-4*y) 7).mp key1
            obtain ⟨k', hk⟩ := hdvd
            left
            refine ⟨2*y+3*k', -y-2*k', ?_, ?_⟩
            · have hx : x = 4*y+7*k' := by linarith [hk]
              have e7 : (7:ℤ)^(m+1) = 7 * 7^m := pow_succ' 7 m
              rw [hx, e7] at h
              have step : 7*((2*y+3*k')^2+(2*y+3*k')*(-y-2*k')+(-y-2*k')^2) = 7 * 7^m := by linear_combination h
              exact mul_left_cancel₀ (by norm_num) step
            · simp only [Prod.mk.injEq]
              constructor <;> linarith [hk]
          · have key2 : ((x - 2*y : ℤ) : ZMod 7) = 0 := by push_cast; linear_combination h1'
            have hdvd : (7:ℤ) ∣ (x - 2*y) := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x-2*y) 7).mp key2
            obtain ⟨k', hk⟩ := hdvd
            right
            refine ⟨k', y+2*k', ?_, ?_⟩
            · have hx : x = 2*y+7*k' := by linarith [hk]
              have e7 : (7:ℤ)^(m+1) = 7 * 7^m := pow_succ' 7 m
              rw [hx, e7] at h
              have step : 7*(k'^2+k'*(y+2*k')+(y+2*k')^2) = 7 * 7^m := by linear_combination h
              exact mul_left_cancel₀ (by norm_num) step
            · simp only [Prod.mk.injEq]
              constructor <;> linarith [hk]
        have INTER_GEN : ∀ (m : ℕ) (x y : ℤ),
            (∃ x1 y1 : ℤ, x1^2+x1*y1+y1^2=(7:ℤ)^m ∧ x=x1-2*y1 ∧ y=2*x1+3*y1) →
            (∃ x2 y2 : ℤ, x2^2+x2*y2+y2^2=(7:ℤ)^m ∧ x=3*x2+2*y2 ∧ y=-2*x2+y2) →
            ∃ a b : ℤ, x=7*a ∧ y=7*b ∧ 49*(a^2+a*b+b^2) = (7:ℤ)^(m+1) := by
          intro m x y hA hB
          obtain ⟨x1,y1,hq1,hx1,hy1⟩ := hA
          obtain ⟨x2,y2,hq2,hx2,hy2⟩ := hB
          have hdx : (7:ℤ) ∣ x := by omega
          have hdy : (7:ℤ) ∣ y := by omega
          obtain ⟨a, ha⟩ := hdx
          obtain ⟨b, hb⟩ := hdy
          refine ⟨a, b, ha, hb, ?_⟩
          have hx1eq : x1 = 3*a+2*b := by omega
          have hy1eq : y1 = b - 2*a := by omega
          have e7 : (7:ℤ)^(m+1) = 7 * 7^m := pow_succ' 7 m
          rw [e7, ← hq1, hx1eq, hy1eq]
          ring
        have UNION : ∀ (m : ℕ), {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(m+1)} =
            (fun p : ℤ×ℤ => (p.1-2*p.2,2*p.1+3*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m} ∪
            (fun p : ℤ×ℤ => (3*p.1+2*p.2,-2*p.1+p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m} := by
          intro m
          ext ⟨x,y⟩
          simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
          constructor
          · intro h
            rcases COVER m x y h with ⟨x',y',hq,heq⟩ | ⟨x',y',hq,heq⟩
            · exact Or.inl ⟨(x',y'), hq, heq⟩
            · exact Or.inr ⟨(x',y'), hq, heq⟩
          · rintro (⟨⟨x',y'⟩,hq,heq⟩ | ⟨⟨x',y'⟩,hq,heq⟩)
            · simp only [Prod.mk.injEq] at heq
              obtain ⟨e1,e2⟩ := heq
              rw [← e1, ← e2]
              exact MAPS_pi m x' y' hq
            · simp only [Prod.mk.injEq] at heq
              obtain ⟨e1,e2⟩ := heq
              rw [← e1, ← e2]
              exact MAPS_pib m x' y' hq
        have DECOMP : ∀ m : ℕ, Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(m+1)} +
            Set.ncard ( ((fun p : ℤ×ℤ => (p.1-2*p.2,2*p.1+3*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m}) ∩
                        ((fun p : ℤ×ℤ => (3*p.1+2*p.2,-2*p.1+p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m}) )
            = 2 * Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m} := by
          intro m
          have hSm : ({p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m}).Finite := FINITE _ (by positivity)
          have hA : ((fun p : ℤ×ℤ => (p.1-2*p.2,2*p.1+3*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m}).Finite :=
            hSm.image _
          have hB : ((fun p : ℤ×ℤ => (3*p.1+2*p.2,-2*p.1+p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^m}).Finite :=
            hSm.image _
          rw [UNION m]
          rw [Set.ncard_union_add_ncard_inter _ _ hA hB]
          rw [Set.ncard_image_of_injective _ INJ_pi, Set.ncard_image_of_injective _ INJ_pib]
          ring
        have INTERZERO : ( ((fun p : ℤ×ℤ => (p.1-2*p.2,2*p.1+3*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^0}) ∩
            ((fun p : ℤ×ℤ => (3*p.1+2*p.2,-2*p.1+p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^0}) ) = ∅ := by
          ext ⟨x,y⟩
          simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨⟨x1,y1⟩,hq1,heq1⟩,⟨⟨x2,y2⟩,hq2,heq2⟩⟩
          simp only [Prod.mk.injEq] at heq1 heq2
          obtain ⟨a,b,_,_,heq⟩ := INTER_GEN 0 x y ⟨x1,y1,hq1,heq1.1.symm,heq1.2.symm⟩ ⟨x2,y2,hq2,heq2.1.symm,heq2.2.symm⟩
          norm_num at heq
          generalize a^2+a*b+b^2 = n at heq
          omega
        have INTERSUCC : ∀ (k' : ℕ),
            ( ((fun p : ℤ×ℤ => (p.1-2*p.2,2*p.1+3*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(k'+1)}) ∩
              ((fun p : ℤ×ℤ => (3*p.1+2*p.2,-2*p.1+p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(k'+1)}) ) =
            (fun p : ℤ×ℤ => (7*p.1,7*p.2)) '' {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^k'} := by
          intro k'
          ext ⟨x,y⟩
          simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
          constructor
          · rintro ⟨⟨⟨x1,y1⟩,hq1,heq1⟩,⟨⟨x2,y2⟩,hq2,heq2⟩⟩
            simp only [Prod.mk.injEq] at heq1 heq2
            obtain ⟨a,b,ha,hb,heq⟩ := INTER_GEN (k'+1) x y ⟨x1,y1,hq1,heq1.1.symm,heq1.2.symm⟩ ⟨x2,y2,hq2,heq2.1.symm,heq2.2.symm⟩
            refine ⟨(a,b), ?_, ?_⟩
            · show a^2+a*b+b^2 = (7:ℤ)^k'
              have e7 : (7:ℤ)^(k'+1+1) = 49 * 7^k' := by
                rw [show k'+1+1 = k'+2 from rfl, pow_add]; ring
              rw [e7] at heq
              exact mul_left_cancel₀ (by norm_num) heq
            · simp only [Prod.mk.injEq]
              exact ⟨ha.symm, hb.symm⟩
          · rintro ⟨⟨a,b⟩,hab,heq⟩
            simp only [Prod.mk.injEq] at heq
            obtain ⟨hx,hy⟩ := heq
            constructor
            · refine ⟨(3*a+2*b,-2*a+b), ?_, ?_⟩
              · show (3*a+2*b)^2+(3*a+2*b)*(-2*a+b)+(-2*a+b)^2 = (7:ℤ)^(k'+1)
                have := hab
                ring_nf
                ring_nf at this
                nlinarith [this]
              · simp only [Prod.mk.injEq]
                constructor <;> nlinarith [hx, hy]
            · refine ⟨(a-2*b,2*a+3*b), ?_, ?_⟩
              · show (a-2*b)^2+(a-2*b)*(2*a+3*b)+(2*a+3*b)^2 = (7:ℤ)^(k'+1)
                have := hab
                ring_nf
                ring_nf at this
                nlinarith [this]
              · simp only [Prod.mk.injEq]
                constructor <;> nlinarith [hx, hy]
        have BASE : Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^1} = Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^0} + 6 := by
          have hd := DECOMP 0
          rw [INTERZERO] at hd
          simp only [Set.ncard_empty, add_zero] at hd
          rw [h1] at hd ⊢
          omega
        have STEP : ∀ k' : ℕ, Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(k'+1)} = Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^k'} + 6 →
            Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(k'+2)} = Set.ncard {p:ℤ×ℤ | p.1^2+p.1*p.2+p.2^2=(7:ℤ)^(k'+1)} + 6 := by
          intro k' ih
          have hd := DECOMP (k'+1)
          rw [show k'+1+1 = k'+2 from rfl] at hd
          rw [INTERSUCC k'] at hd
          rw [Set.ncard_image_of_injective _ INJ_77] at hd
          omega
        intro n
        induction n with
        | zero => exact BASE
        | succ k' ih => exact STEP k' ih
  induction k with
  | zero => simpa using h1
  | succ n ih => rw [h2 n, ih]; ring

end Native.Competemath.P111

namespace Native.Competemath.P174

/-- competemath.com problem 174. -/
theorem eleven_streak_expectation : (2^11 - 1 : ℤ) = 2047 := by norm_num

end Native.Competemath.P174

namespace Native.Competemath.P135

/-- competemath.com problem 135. -/
theorem descartes_chain_closed_form (f : ℕ → ℤ) (h0 : f 0 = 0) (h1 : f 1 = 25)
    (hrec : ∀ n : ℕ, f (n + 2) = 2 * (13 + f (n + 1)) - f n) :
    ∀ n : ℕ, f n = (n : ℤ) * (13 * n + 12) := by
  have key : ∀ n : ℕ, f n = (n : ℤ) * (13 * n + 12) ∧ f (n+1) = ((n:ℤ)+1) * (13 * ((n:ℤ)+1) + 12) := by
    intro n
    induction n with
    | zero => constructor <;> simp [h0, h1]
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      constructor
      · push_cast
        linarith [ihk1]
      · have hk := hrec k
        push_cast
        push_cast at ihk hk
        linarith [hk, ihk, ihk1]
  intro n
  exact (key n).1

end Native.Competemath.P135

namespace Native.Competemath.P139

/-- competemath.com problem 139. -/
theorem pell_fundamental_solution :
 (8201251 : ℤ)^2 - 4100626 * (4050 : ℤ)^2 = 1 ∧
 (∀ x y : ℤ, 0 < y → y < 4050 → x^2 - 4100626 * y^2 ≠ 1) ∧
 (8201251 : ℤ) + 4050 = 8205301 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  intro x y hy0 hy4050 heq
  have hlow : (2025*y)^2 < x^2 := by nlinarith [heq]
  have hhigh : x^2 < (2025*y+1)^2 := by nlinarith [heq]
  have h1 : 2025*y < |x| := by
    have := (sq_lt_sq (a := 2025*y) (b := x)).mp hlow
    rwa [abs_of_nonneg (by linarith : (0:ℤ) ≤ 2025*y)] at this
  have h2 : |x| < 2025*y + 1 := abs_lt_of_sq_lt_sq hhigh (by linarith)
  omega

end Native.Competemath.P139

namespace Native.Competemath.P175

/-- competemath.com problem 175. -/
theorem coin_race_answer :
    ∃ e0 eH eT eTT : ℚ,
      e0 = 1 + (1/2)*eH + (1/2)*eT ∧
      eH = 1 + (1/2)*eT ∧
      eT = 1 + (1/2)*eTT + (1/2)*eH ∧
      eTT = 1 + (1/2)*eH ∧
      e0 = 21/5 ∧ (21 + 5 = 26) := by
  refine ⟨21/5, 14/5, 18/5, 12/5, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;> norm_num

end Native.Competemath.P175

namespace Native.Competemath.P189

/-- competemath.com problem 189. -/
theorem csc_sum_answer : (2026 ^ 2 - 1) / 3 = 1368225 := by norm_num

end Native.Competemath.P189

namespace Native.Competemath.P181

/-- competemath.com problem 181. -/
theorem parabola_tangent_triangle_area :
    let P : ℝ × ℝ := (13, 25)
    let T1 : ℝ × ℝ := (25, 625)
    let T2 : ℝ × ℝ := (1, 1)
    (1/2 : ℝ) * |P.1 * (T1.2 - T2.2) + T1.1 * (T2.2 - P.2) + T2.1 * (P.2 - T1.2)| = 3456 := by
  norm_num

end Native.Competemath.P181

namespace Native.Competemath.P188

/-- competemath.com problem 188. -/
theorem wedge_circles : (3:ℕ)^12 ≤ 1000000 ∧ (3:ℕ)^13 > 1000000 := by decide

end Native.Competemath.P188

namespace Native.Competemath.P193

set_option maxHeartbeats 4000000 in
/-- competemath.com problem 193. -/
theorem degree_sum_of_coprime_radicals :
 (minpoly ℚ ((2:ℝ) ^ ((1:ℝ)/3) + (3:ℝ) ^ ((1:ℝ)/5))).natDegree = 15 := by
  set α : ℝ := (2:ℝ) ^ ((1:ℝ)/3) with hα_def
  set β : ℝ := (3:ℝ) ^ ((1:ℝ)/5) with hβ_def
  have h1 : (minpoly ℚ α).natDegree = 3 := by
    have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C (2:ℚ)) := by
      refine X_pow_sub_C_irreducible_of_prime ?_ ?_
      · norm_num
      · intro b hb
        have h2 : ((b.num:ℚ) / (b.den:ℚ))^3 = 2 := by rw [Rat.num_div_den]; exact hb
        have hden : (b.den:ℚ) ≠ 0 := by exact_mod_cast b.den_nz
        rw [div_pow, div_eq_iff (by positivity)] at h2
        have h3 : b.num ^ 3 = 2 * (b.den:ℤ) ^ 3 := by exact_mod_cast h2
        have hp2 : Prime (2:ℤ) := Int.prime_two
        have h4 : (2:ℤ) ∣ b.num := hp2.dvd_of_dvd_pow ⟨(b.den:ℤ)^3, h3⟩
        obtain ⟨k, hk⟩ := h4
        rw [hk] at h3
        have h5 : (b.den:ℤ) ^ 3 = 4 * k ^ 3 := by nlinarith [h3]
        have h6 : (2:ℤ) ∣ (b.den:ℤ) := hp2.dvd_of_dvd_pow (n := 3) ⟨2 * k ^ 3, by rw [h5]; ring⟩
        have h7 : (2:ℕ) ∣ b.den := by exact_mod_cast h6
        have h8 : (2:ℕ) ∣ b.num.natAbs := by
          have hd : (2:ℤ) ∣ b.num := ⟨k, hk⟩
          have := Int.natAbs_dvd_natAbs.mpr hd
          simpa using this
        have h9 : (2:ℕ) ∣ Nat.gcd b.num.natAbs b.den := Nat.dvd_gcd h8 h7
        have h10 := b.reduced
        unfold Nat.Coprime at h10
        rw [h10] at h9
        norm_num at h9
    have hmonic : (Polynomial.X ^ 3 - Polynomial.C (2:ℚ)).Monic := by
      apply Polynomial.monic_X_pow_sub_C
      norm_num
    have hroot : Polynomial.aeval α (Polynomial.X ^ 3 - Polynomial.C (2:ℚ)) = 0 := by
      have : α ^ 3 = 2 := by
        rw [hα_def, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul (by norm_num)]
        norm_num
      simp [this]
    have heq : minpoly ℚ α = Polynomial.X ^ 3 - Polynomial.C (2:ℚ) :=
      (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
    rw [heq]
    compute_degree!
  have h2 : (minpoly ℚ β).natDegree = 5 := by
    have hirr : Irreducible (Polynomial.X ^ 5 - Polynomial.C (3:ℚ)) := by
      refine X_pow_sub_C_irreducible_of_prime ?_ ?_
      · norm_num
      · intro b hb
        have h2 : ((b.num:ℚ) / (b.den:ℚ))^5 = 3 := by rw [Rat.num_div_den]; exact hb
        have hden : (b.den:ℚ) ≠ 0 := by exact_mod_cast b.den_nz
        rw [div_pow, div_eq_iff (by positivity)] at h2
        have h3 : b.num ^ 5 = 3 * (b.den:ℤ) ^ 5 := by exact_mod_cast h2
        have hp3 : Prime (3:ℤ) := Int.prime_three
        have h4 : (3:ℤ) ∣ b.num := hp3.dvd_of_dvd_pow ⟨(b.den:ℤ)^5, h3⟩
        obtain ⟨k, hk⟩ := h4
        rw [hk] at h3
        have h5 : (b.den:ℤ) ^ 5 = 3^4 * k ^ 5 := by nlinarith [h3]
        have h6 : (3:ℤ) ∣ (b.den:ℤ) := hp3.dvd_of_dvd_pow (n := 5) ⟨3^3 * k ^ 5, by rw [h5]; ring⟩
        have h7 : (3:ℕ) ∣ b.den := by exact_mod_cast h6
        have h8 : (3:ℕ) ∣ b.num.natAbs := by
          have hd : (3:ℤ) ∣ b.num := ⟨k, hk⟩
          have := Int.natAbs_dvd_natAbs.mpr hd
          simpa using this
        have h9 : (3:ℕ) ∣ Nat.gcd b.num.natAbs b.den := Nat.dvd_gcd h8 h7
        have h10 := b.reduced
        unfold Nat.Coprime at h10
        rw [h10] at h9
        norm_num at h9
    have hmonic : (Polynomial.X ^ 5 - Polynomial.C (3:ℚ)).Monic := by
      apply Polynomial.monic_X_pow_sub_C
      norm_num
    have hroot : Polynomial.aeval β (Polynomial.X ^ 5 - Polynomial.C (3:ℚ)) = 0 := by
      have : β ^ 5 = 3 := by
        rw [hβ_def, ← Real.rpow_natCast ((3:ℝ) ^ ((1:ℝ)/5)) 5, ← Real.rpow_mul (by norm_num)]
        norm_num
      simp [this]
    have heq : minpoly ℚ β = Polynomial.X ^ 5 - Polynomial.C (3:ℚ) :=
      (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
    rw [heq]
    compute_degree!
  have hα3 : α ^ 3 = 2 := by
    rw [hα_def, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hβ5 : β ^ 5 = 3 := by
    rw [hβ_def, ← Real.rpow_natCast ((3:ℝ) ^ ((1:ℝ)/5)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hα1 : (1:ℝ) < α := by
    have hnn : (0:ℝ) ≤ α := Real.rpow_nonneg (by norm_num) _
    by_contra hc
    simp only [not_lt] at hc
    nlinarith [pow_le_one₀ (n := 3) hnn hc, hα3]
  have hβ1 : (1:ℝ) < β := by
    have hnn : (0:ℝ) ≤ β := Real.rpow_nonneg (by norm_num) _
    by_contra hc
    simp only [not_lt] at hc
    nlinarith [pow_le_one₀ (n := 5) hnn hc, hβ5]
  clear_value α β
  have h3 : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α, β} : Set ℝ)) = 15 := by
    have hiα : IsIntegral ℚ α := by by_contra hc; rw [minpoly.eq_zero hc] at h1; simp at h1
    have hiβ : IsIntegral ℚ β := by by_contra hc; rw [minpoly.eq_zero hc] at h2; simp at h2
    have hKfin : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α}:Set ℝ)) = 3 := by
      rw [IntermediateField.adjoin.finrank hiα, h1]
    have hLfin : Module.finrank ℚ (IntermediateField.adjoin ℚ ({β}:Set ℝ)) = 5 := by
      rw [IntermediateField.adjoin.finrank hiβ, h2]
    have hunion : IntermediateField.adjoin ℚ ({α, β} : Set ℝ) = IntermediateField.adjoin ℚ ({α}:Set ℝ) ⊔ IntermediateField.adjoin ℚ ({β}:Set ℝ) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        rcases hx with hx | hx
        · rw [hx]
          exact SetLike.le_def.mp le_sup_left (IntermediateField.mem_adjoin_simple_self ℚ α)
        · simp only [Set.mem_singleton_iff] at hx
          rw [hx]
          exact SetLike.le_def.mp le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)
      · apply sup_le
        · rw [IntermediateField.adjoin_le_iff]
          intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; apply IntermediateField.subset_adjoin; simp
        · rw [IntermediateField.adjoin_le_iff]; intro x hx; simp only [Set.mem_singleton_iff] at hx; rw [hx]; apply IntermediateField.subset_adjoin; simp
    have hub : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α, β} : Set ℝ)) ≤ 15 := by
      rw [hunion]
      have hle := IntermediateField.finrank_sup_le (IntermediateField.adjoin ℚ ({α}:Set ℝ)) (IntermediateField.adjoin ℚ ({β}:Set ℝ))
      rw [hKfin, hLfin] at hle
      exact hle
    have hdvd3 : (3:ℕ) ∣ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := by
      have heq := IntermediateField.adjoin_adjoin_left ℚ ({α} : Set ℝ) ({β} : Set ℝ)
      have hset : ({α}:Set ℝ) ∪ ({β}:Set ℝ) = ({α,β} : Set ℝ) := by rw [Set.singleton_union]
      rw [hset] at heq
      have htower := Module.finrank_mul_finrank ℚ (↥(IntermediateField.adjoin ℚ ({α}:Set ℝ))) (IntermediateField.adjoin (↥(IntermediateField.adjoin ℚ ({α}:Set ℝ))) ({β}:Set ℝ))
      have hfr : Module.finrank ℚ (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin ℚ ({α}:Set ℝ))) ({β}:Set ℝ))) = Module.finrank ℚ (↥(IntermediateField.adjoin ℚ ({α,β}:Set ℝ))) := by
        rw [← heq]; rfl
      have hdvd3raw : Module.finrank ℚ (IntermediateField.adjoin ℚ ({α}:Set ℝ)) ∣ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := ⟨_, hfr ▸ htower.symm⟩
      rw [hKfin] at hdvd3raw
      exact hdvd3raw
    have hdvd5 : (5:ℕ) ∣ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := by
      have heq := IntermediateField.adjoin_adjoin_left ℚ ({β} : Set ℝ) ({α} : Set ℝ)
      have hset : ({β}:Set ℝ) ∪ ({α}:Set ℝ) = ({α,β} : Set ℝ) := by rw [Set.singleton_union]; exact Set.pair_comm β α
      rw [hset] at heq
      have htower := Module.finrank_mul_finrank ℚ (↥(IntermediateField.adjoin ℚ ({β}:Set ℝ))) (IntermediateField.adjoin (↥(IntermediateField.adjoin ℚ ({β}:Set ℝ))) ({α}:Set ℝ))
      have hfr : Module.finrank ℚ (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin ℚ ({β}:Set ℝ))) ({α}:Set ℝ))) = Module.finrank ℚ (↥(IntermediateField.adjoin ℚ ({α,β}:Set ℝ))) := by
        rw [← heq]; rfl
      have hdvd5raw : Module.finrank ℚ (IntermediateField.adjoin ℚ ({β}:Set ℝ)) ∣ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := ⟨_, hfr ▸ htower.symm⟩
      rw [hLfin] at hdvd5raw
      exact hdvd5raw
    have hdvd15 : (15:ℕ) ∣ Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := by
      have hcop : Nat.Coprime 3 5 := by decide
      exact hcop.mul_dvd_of_dvd_of_dvd hdvd3 hdvd5
    have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := by
      haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({α,β}:Set ℝ)) := by
        apply IntermediateField.finiteDimensional_adjoin
        intro x hx
        rcases hx with hx | hx
        · rw [hx]; exact hiα
        · simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact hiβ
      exact Module.finrank_pos
    omega
  have h4 : IntermediateField.adjoin ℚ ({α + β} : Set ℝ) = IntermediateField.adjoin ℚ ({α, β} : Set ℝ) := by
    set F := IntermediateField.adjoin ℚ ({α+β} : Set ℝ) with hF_def
    set M := IntermediateField.adjoin ℚ ({α, β} : Set ℝ) with hM_def
    have hFM : F ≤ M := by
      rw [hF_def, hM_def, IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      apply add_mem <;> [exact IntermediateField.subset_adjoin ℚ _ (by simp); exact IntermediateField.subset_adjoin ℚ _ (by simp)]
    have hC0 : (10*(α+β)^3 - 2 : ℝ) ≠ 0 := by
      intro h
      nlinarith [sq_nonneg (α+β), sq_nonneg (α+β-2), mul_pos (show (0:ℝ) < α + β - 2 + 2 by linarith) (show (0:ℝ) < α+β-2+2 by linarith)]
    have hboth : IsIntegral (↥F) α ∧ (minpoly (↥F) α).natDegree ≤ 2 := by
      have hmem : (α + β) ∈ F := IntermediateField.mem_adjoin_simple_self ℚ (α+β)
      set γF : ↥F := ⟨α+β, hmem⟩ with hγF_def
      set AF : ↥F := γF^5 - 20*γF^2 - 3 with hAF_def
      set BF : ↥F := 10*γF - 5*γF^4 with hBF_def
      set CF : ↥F := 10*γF^3 - 2 with hCF_def
      have hCFcoe : (CF : ℝ) = 10*(α+β)^3 - 2 := by rw [hCF_def, hγF_def]; norm_cast
      have hAFcoe : (AF : ℝ) = (α+β)^5 - 20*(α+β)^2 - 3 := by rw [hAF_def, hγF_def]; norm_cast
      have hBFcoe : (BF : ℝ) = 10*(α+β) - 5*(α+β)^4 := by rw [hBF_def, hγF_def]; norm_cast
      have hCFne : CF ≠ 0 := by intro hc; apply hC0; rw [← hCFcoe, hc]; simp
      set q : Polynomial ↥F := Polynomial.C CF * Polynomial.X^2 + Polynomial.C BF * Polynomial.X + Polynomial.C AF with hq_def
      have hqne : q ≠ 0 := by
        rw [hq_def]
        intro hzero
        apply hCFne
        have := congrArg (fun p => Polynomial.coeff p 2) hzero
        simpa using this
      have haeval : Polynomial.aeval α q = 0 := by
        rw [hq_def]
        simp only [Polynomial.aeval_add, Polynomial.aeval_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        show (CF:ℝ) * α^2 + (BF:ℝ) * α + (AF:ℝ) = 0
        rw [hAFcoe, hBFcoe, hCFcoe]
        have hkey : (α + β - α)^5 = 3 := by rw [show α + β - α = β from by ring]; exact hβ5
        linear_combination hkey + (10*(α+β)^2 - 5*(α+β)*α + α^2) * hα3
      have hqdeg : q.natDegree ≤ 2 := by
        rw [hq_def]; compute_degree
      have halg : IsAlgebraic (↥F) α := ⟨q, hqne, haeval⟩
      have hint : IsIntegral (↥F) α := halg.isIntegral
      exact ⟨hint, le_trans (Polynomial.natDegree_le_of_dvd (minpoly.dvd (↥F) α haeval) hqne) hqdeg⟩
    obtain ⟨hint, hdeg2⟩ := hboth
    have hFadjeq : IntermediateField.restrictScalars ℚ (IntermediateField.adjoin (↥F) ({α}:Set ℝ)) = M := by
      have heq := IntermediateField.adjoin_adjoin_left ℚ ({α+β} : Set ℝ) ({α} : Set ℝ)
      have hgoal2 : IntermediateField.adjoin ℚ (({α+β}:Set ℝ) ∪ ({α}:Set ℝ)) = M := by
        rw [hM_def]
        apply le_antisymm
        · rw [IntermediateField.adjoin_le_iff]
          intro x hx
          rcases hx with hx | hx
          · simp only [Set.mem_singleton_iff] at hx; rw [hx]
            exact add_mem (IntermediateField.subset_adjoin ℚ _ (by simp)) (IntermediateField.subset_adjoin ℚ _ (by simp))
          · rw [hx]
            exact IntermediateField.subset_adjoin ℚ _ (by simp)
        · rw [IntermediateField.adjoin_le_iff]
          intro x hx
          rcases hx with hx | hx
          · rw [hx]
            exact IntermediateField.subset_adjoin ℚ _ (by simp)
          · rw [hx]
            have h1 : (α+β) ∈ IntermediateField.adjoin ℚ (({α+β}:Set ℝ) ∪ ({α}:Set ℝ)) := IntermediateField.subset_adjoin ℚ _ (by simp)
            have h2 : α ∈ IntermediateField.adjoin ℚ (({α+β}:Set ℝ) ∪ ({α}:Set ℝ)) := IntermediateField.subset_adjoin ℚ _ (by simp)
            have hmem2 : (α + β) - α ∈ IntermediateField.adjoin ℚ (({α+β}:Set ℝ) ∪ ({α}:Set ℝ)) := sub_mem h1 h2
            have hβeq : (α + β) - α = β := by ring
            rwa [hβeq] at hmem2
      exact heq.trans hgoal2
    have hbot : IntermediateField.adjoin (↥F) ({α}:Set ℝ) = ⊥ := by
      haveI : FiniteDimensional (↥F) (IntermediateField.adjoin (↥F) ({α}:Set ℝ)) := IntermediateField.adjoin.finiteDimensional hint
      have hfrE : Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) = (minpoly (↥F) α).natDegree :=
        IntermediateField.adjoin.finrank hint
      have htower := Module.finrank_mul_finrank ℚ (↥F) (IntermediateField.adjoin (↥F) ({α}:Set ℝ))
      have hfr : Module.finrank ℚ (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) = Module.finrank ℚ (↥M) := by
        rw [← hFadjeq]; rfl
      rw [hfr, h3] at htower
      have he1 : 1 ≤ Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) := Module.finrank_pos
      have he2 : Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) ≤ 2 := by
        rw [hfrE]; exact hdeg2
      have hedvd : Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) ∣ 15 :=
        ⟨Module.finrank ℚ F, by rw [← htower]; ring⟩
      have he1' : Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ))) = 1 := by
        interval_cases (Module.finrank (↥F) (↥(IntermediateField.adjoin (↥F) ({α}:Set ℝ)))) <;> omega
      exact IntermediateField.finrank_eq_one_iff.mp he1'
    have hαF : α ∈ F := by
      have hmemadj : α ∈ IntermediateField.adjoin (↥F) ({α}:Set ℝ) := IntermediateField.mem_adjoin_simple_self (↥F) α
      rw [hbot] at hmemadj
      rw [IntermediateField.mem_bot] at hmemadj
      obtain ⟨c, hc⟩ := hmemadj
      rw [← hc]
      exact c.2
    have hβF : β ∈ F := by
      have : β = (α+β) - α := by ring
      rw [this]
      exact sub_mem (IntermediateField.mem_adjoin_simple_self ℚ (α+β)) hαF
    have hMF : M ≤ F := by
      rw [hM_def, IntermediateField.adjoin_le_iff]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact hαF
      · simp only [Set.mem_singleton_iff] at hx; rw [hx]; exact hβF
    exact le_antisymm hFM hMF
  have h5 : (minpoly ℚ (α + β)).natDegree = Module.finrank ℚ (IntermediateField.adjoin ℚ ({α + β} : Set ℝ)) := by
    have hiα : IsIntegral ℚ α := by by_contra hc; rw [minpoly.eq_zero hc] at h1; simp at h1
    have hiβ : IsIntegral ℚ β := by by_contra hc; rw [minpoly.eq_zero hc] at h2; simp at h2
    rw [IntermediateField.adjoin.finrank (hiα.add hiβ)]
  rw [h5, h4, h3]

end Native.Competemath.P193

namespace Native.Competemath.P100

/-- competemath.com problem 100. -/
theorem middle_penguin : 6 + 1 + 6 = 13 := by norm_num

end Native.Competemath.P100
