/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P176

/-- competemath.com problem 176. -/
theorem hoop_radius_six :
    ∃ R x y : ℝ, R = 6 ∧
      Real.sqrt (x^2 + y^2) = R - 3 ∧
      Real.sqrt ((x-6)^2 + y^2) = R - 3 ∧
      Real.sqrt ((x-3)^2 + (y-4)^2) = R - 2 := by
  refine ⟨6, 3, 0, rfl, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

end Native.Competemath.P176

namespace Native.Competemath.P266

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 266. -/
lemma term_eq (k : ℕ) (hk : 1 ≤ k) :
    (1:ℝ) / (Real.sqrt (k:ℝ) + Real.sqrt ((k:ℝ) + 1)) = Real.sqrt ((k:ℝ) + 1) - Real.sqrt (k:ℝ) :=
  by
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hk1 : (0:ℝ) ≤ (k:ℝ) + 1 := by linarith
    have hpos : (0:ℝ) < Real.sqrt (k:ℝ) + Real.sqrt ((k:ℝ)+1) := by
      have h1 := Real.sqrt_nonneg (k:ℝ)
      have h2 : (0:ℝ) < Real.sqrt ((k:ℝ)+1) := Real.sqrt_pos.mpr (by linarith)
      linarith
    rw [div_eq_iff (ne_of_gt hpos)]
    have e1 : Real.sqrt (k:ℝ) * Real.sqrt (k:ℝ) = (k:ℝ) := Real.mul_self_sqrt hk0
    have e2 : Real.sqrt ((k:ℝ)+1) * Real.sqrt ((k:ℝ)+1) = (k:ℝ)+1 := Real.mul_self_sqrt hk1
    nlinarith [e1, e2]

lemma telescope_sum (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc (1:ℕ) N, (Real.sqrt ((k:ℝ) + 1) - Real.sqrt (k:ℝ)) = Real.sqrt ((N:ℝ) + 1) - Real.sqrt (1:ℝ) :=
  by
    induction N with
    | zero => omega
    | succ n ih =>
      rcases eq_or_lt_of_le hN with h | h
      · simp [← h]
      · have hn : 1 ≤ n := by omega
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        rw [ih hn]
        push_cast
        ring

lemma sqrt_4108729_eq : Real.sqrt (4108729:ℝ) = 2027 :=
  by
    rw [show (4108729:ℝ) = (2027:ℝ)^2 by norm_num]
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2027)]

theorem surd_telescope : (∑ k ∈ Finset.Icc (1:ℕ) 4108728, (1:ℝ) / (Real.sqrt (k : ℝ) + Real.sqrt ((k : ℝ) + 1))) = 2026 :=
  by
    have h1 : ∀ k ∈ Finset.Icc (1:ℕ) 4108728,
        (1:ℝ) / (Real.sqrt (k:ℝ) + Real.sqrt ((k:ℝ) + 1)) = Real.sqrt ((k:ℝ) + 1) - Real.sqrt (k:ℝ) :=
      fun k hk => term_eq k (Finset.mem_Icc.mp hk).1
    rw [Finset.sum_congr rfl h1, telescope_sum 4108728 (by norm_num)]
    rw [show ((4108728:ℕ):ℝ) + 1 = (4108729:ℝ) by norm_num, sqrt_4108729_eq, Real.sqrt_one]
    norm_num

end Native.Competemath.P266

namespace Native.Competemath.P180

/-- competemath.com problem 180. -/
theorem nested_radical_floor : ⌊(1 + Real.sqrt 8105) / 2⌋ = 45 := by
  have h1 : (90:ℝ) ≤ Real.sqrt 8105 := by
    have : (90:ℝ) = Real.sqrt (90^2) := by
      rw [Real.sqrt_sq]; norm_num
    rw [this]
    apply Real.sqrt_le_sqrt
    norm_num
  have h2 : Real.sqrt 8105 < 91 := by
    have : (91:ℝ) = Real.sqrt (91^2) := by
      rw [Real.sqrt_sq]; norm_num
    rw [this]
    apply Real.sqrt_lt_sqrt
    · norm_num
    · norm_num
  rw [Int.floor_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

end Native.Competemath.P180

namespace Native.Competemath.P182

/-- competemath.com problem 182. -/
theorem two_ladders_never_both : ⌊(2027 : ℝ) / Real.sqrt 2⌋ = 1433 := by
  have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ h2]
    push_cast
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ),
      sq_nonneg (1433 * Real.sqrt 2 - 2027)]
  · rw [div_lt_iff₀ h2]
    push_cast
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ),
      sq_nonneg (1434 * Real.sqrt 2 - 2027)]

end Native.Competemath.P182

namespace Native.Competemath.P210

/-- competemath.com problem 210. -/
theorem newton_sqrt2_threshold (x : ℕ → ℝ) (hx0 : x 0 = 2)
    (hrec : ∀ n, x (n + 1) = (x n + 2 / x n) / 2) :
    x 12 - Real.sqrt 2 < (10:ℝ) ^ (-2026 : ℤ) ∧
    ¬ (x 11 - Real.sqrt 2 < (10:ℝ) ^ (-2026 : ℤ)) := by
  have h1 : ∀ n, 0 < x n ∧ Real.sqrt 2 < x n ∧ x n ≤ 2 := by
    intro n
    induction n
    rw [hx0]; refine ⟨by norm_num, ?_, le_refl 2⟩; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    rename_i n ih
    rw [hrec]; obtain ⟨hpos, hgt, hle⟩ := ih; refine ⟨by positivity, ?_, ?_⟩
    have hcancel : 2 / x n * x n = 2 := div_mul_cancel₀ 2 hpos.ne'
    nlinarith [sq_nonneg (x n - Real.sqrt 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hcancel, mul_pos hpos hpos, hgt, hpos]
    have hcancel2 : 2 / x n * x n = 2 := div_mul_cancel₀ 2 hpos.ne'
    have hkey : 2 / x n < Real.sqrt 2 := by rw [div_lt_iff₀ hpos]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), hgt, Real.sqrt_nonneg 2]
    have hsqrt2lt2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith [hkey, hle, hsqrt2lt2]
  have h2 : ∀ n, (x (n+1) - Real.sqrt 2) / (x (n+1) + Real.sqrt 2) =
      ((x n - Real.sqrt 2)/(x n + Real.sqrt 2))^2 := by
        intro n
        obtain ⟨hpos, hgt, hle⟩ := h1 n
        rw [hrec n]
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hxne : x n ≠ 0 := hpos.ne'
        have hsum : x n + Real.sqrt 2 ≠ 0 := by positivity
        have hden : (x n + 2 / x n) / 2 + Real.sqrt 2 ≠ 0 := by positivity
        field_simp
        linear_combination (-4 * x n * Real.sqrt 2) * hs
  have h3 : ∀ n, (x n - Real.sqrt 2)/(x n + Real.sqrt 2) =
      ((2 - Real.sqrt 2)/(2 + Real.sqrt 2))^(2^n) := by
        intro n
        induction n with
        | zero => rw [hx0]; norm_num
        | succ n ih => rw [h2 n, ih, ← pow_mul, ← pow_succ]
  have h4 : (1:ℝ)/6 < (2 - Real.sqrt 2)/(2 + Real.sqrt 2) ∧
      (2 - Real.sqrt 2)/(2 + Real.sqrt 2) < 1/5 := by
        constructor
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h5 : x 11 - Real.sqrt 2 ≥ (1/6:ℝ)^(2^11) * Real.sqrt 2 := by
    have hn := h3 11
    obtain ⟨hpos, hgt, hle⟩ := h1 11
    have hb : (0:ℝ) ≤ 1/6 := by norm_num
    have hab : (1/6:ℝ) ≤ (2 - Real.sqrt 2)/(2 + Real.sqrt 2) := le_of_lt h4.1
    have hpow : (1/6:ℝ)^(2^11) ≤ ((2 - Real.sqrt 2)/(2 + Real.sqrt 2))^(2^11) := pow_le_pow_left₀ hb hab (2^11)
    rw [← hn] at hpow
    have hsum : (0:ℝ) < x 11 + Real.sqrt 2 := by positivity
    have hfinal : (1/6:ℝ)^(2^11) * (x 11 + Real.sqrt 2) ≤ x 11 - Real.sqrt 2 :=
      (le_div_iff₀ hsum).mp hpow
    have hnn : (0:ℝ) ≤ (1/6:ℝ)^(2^11) * x 11 := mul_nonneg (pow_nonneg hb (2^11)) hpos.le
    have hexpand : (1/6:ℝ)^(2^11) * (x 11 + Real.sqrt 2) = (1/6:ℝ)^(2^11) * x 11 + (1/6:ℝ)^(2^11) * Real.sqrt 2 := by ring
    linarith [hfinal, hnn, hexpand]
  have h6 : x 12 - Real.sqrt 2 ≤ (1/5:ℝ)^(2^12) * 4 := by
    have hn := h3 12
    obtain ⟨hpos, hgt, hle⟩ := h1 12
    have hb : (0:ℝ) ≤ (2 - Real.sqrt 2)/(2 + Real.sqrt 2) := by apply div_nonneg; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]; positivity
    have hab : (2 - Real.sqrt 2)/(2 + Real.sqrt 2) ≤ (1/5:ℝ) := le_of_lt h4.2
    have hpow : ((2 - Real.sqrt 2)/(2 + Real.sqrt 2))^(2^12) ≤ (1/5:ℝ)^(2^12) := pow_le_pow_left₀ hb hab (2^12)
    rw [← hn] at hpow
    have hsum : (0:ℝ) < x 12 + Real.sqrt 2 := by positivity
    have hfinal : x 12 - Real.sqrt 2 ≤ (1/5:ℝ)^(2^12) * (x 12 + Real.sqrt 2) := (div_le_iff₀ hsum).mp hpow
    have hb4 : x 12 + Real.sqrt 2 ≤ 4 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, hle]
    have hpownn : (0:ℝ) ≤ (1/5:ℝ)^(2^12) := by positivity
    nlinarith [hfinal, hb4, hpownn, mul_le_mul_of_nonneg_left hb4 hpownn]
  have h7 : (1/6:ℝ)^(2^11) * Real.sqrt 2 ≥ (10:ℝ)^(-2026:ℤ) := by
    have hsqrt1 : (1:ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hbase : (10:ℝ)^(-2026:ℤ) ≤ (1/6:ℝ)^(2^11) := by
      rw [zpow_neg]
      rw [show ((2026:ℤ)) = ((2026:ℕ):ℤ) from rfl, zpow_natCast]
      rw [div_pow, one_pow]
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      rw [one_mul, one_mul]
      rw [show (2^11:ℕ) = 2048 from by norm_num]
      have hbase57 : (6:ℝ)^5 ≤ 10^4 := by norm_num
      have h1' : (6:ℝ)^2050 ≤ 10^1640 := by
        have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 6^5) hbase57 410
        rw [← pow_mul, ← pow_mul, show 5*410 = 2050 from by norm_num, show 4*410 = 1640 from by norm_num] at hp
        exact hp
      have h2' : (6:ℝ)^2048 ≤ 6^2050 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      have h3' : (10:ℝ)^1640 ≤ 10^2026 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact le_trans h2' (le_trans h1' h3')
    nlinarith [mul_le_mul_of_nonneg_left hsqrt1 (show (0:ℝ) ≤ (1/6:ℝ)^(2^11) by positivity), hbase]
  have h8 : (1/5:ℝ)^(2^12) * 4 < (10:ℝ)^(-2026:ℤ) := by
    rw [show (2^12:ℕ) = 4096 from by norm_num]
    rw [zpow_neg]
    rw [show ((2026:ℤ)) = ((2026:ℕ):ℤ) from rfl, zpow_natCast]
    rw [div_pow, one_pow]
    rw [inv_eq_one_div, div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [one_mul]
    have hbase57 : (10:ℝ)^4 ≤ 5^7 := by norm_num
    have h1' : (10:ℝ)^2340 ≤ 5^4095 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10^4) hbase57 585
      rw [← pow_mul, ← pow_mul, show 4*585 = 2340 from by norm_num, show 7*585 = 4095 from by norm_num] at hp
      exact hp
    have h2' : (5:ℝ)^4095 ≤ 5^4096 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h3' : (10:ℝ)^2027 ≤ 10^2340 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h4' : (4:ℝ) * 10^2026 < 10^2027 := by
      have hpos : (0:ℝ) < 10^2026 := by positivity
      have heq : (10:ℝ)^2027 = 10 * 10^2026 := by rw [pow_succ']
      rw [heq]; exact mul_lt_mul_of_pos_right (by norm_num) hpos
    exact lt_of_lt_of_le h4' (le_trans h3' (le_trans h1' h2'))
  constructor
  · calc x 12 - Real.sqrt 2 ≤ (1/5:ℝ)^(2^12) * 4 := h6
    _ < (10:ℝ)^(-2026:ℤ) := h8
  · intro hcon
    linarith [h5, h7]

end Native.Competemath.P210
