/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P67

/-- competemath.com problem 67. -/
theorem cubic_sentinel (n : ℤ) (hn : 0 < n) : (n ^ 2 + n + 1) ∣ (n ^ 2023 - 1) ↔ n = 1 := by
  have key1 : (n ^ 2 + n + 1) ∣ (n ^ 3 - 1) := ⟨n - 1, by ring⟩
  have key2 : (n ^ 2 + n + 1) ∣ ((n ^ 3) ^ 674 - 1) := by
    have h := sub_dvd_pow_sub_pow (n ^ 3) 1 674
    simpa using key1.trans h
  have key3 : (n ^ 2 + n + 1) ∣ (n ^ 2023 - n) := by
    have heq : n ^ 2023 - n = n * ((n ^ 3) ^ 674 - 1) := by ring
    rw [heq]
    exact key2.mul_left n
  constructor
  · intro hdvd
    have hdvd2 : (n ^ 2 + n + 1) ∣ (n - 1) := by
      have hd := dvd_sub hdvd key3
      have heq : (n ^ 2023 - 1) - (n ^ 2023 - n) = n - 1 := by ring
      rwa [heq] at hd
    by_contra hne
    have hpos2 : (0:ℤ) < n - 1 := by omega
    have hle := Int.le_of_dvd hpos2 hdvd2
    nlinarith
  · intro hn1
    subst hn1
    norm_num

end Native.Competemath.P67

namespace Native.Competemath.P113

/-- competemath.com problem 113. -/
theorem absent_root_general (p : ℕ) [Fact (Nat.Prime p)] (h : p % 4 = 3) : ∏ a : ZMod p, (1 + a ^ 2) = 4 := by
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  set K := GaloisField p 2 with hKdef
  have hp2 : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
  have hpolyZ : (∏ a : ZMod p, (Polynomial.X - Polynomial.C a) : Polynomial (ZMod p)) = Polynomial.X ^ p - Polynomial.X := by
    rw [Finset.prod_eq_multiset_prod, ← FiniteField.roots_X_pow_card_sub_X (ZMod p), ZMod.card]
    apply Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    case hp =>
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hp2
    have hroots' : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).roots = Finset.univ.val := by
      have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
      rwa [ZMod.card] at this
    rw [hroots', ← Finset.card_def, Finset.card_univ, ZMod.card]
    have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).degree = (p : WithBot ℕ) := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt, Polynomial.degree_X_pow]
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast hp2
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  have heval : ∀ x : K, ∏ a : ZMod p, (x - algebraMap (ZMod p) K a) = x ^ p - x := by
    intro x
    have h2 := congrArg (Polynomial.eval₂ (algebraMap (ZMod p) K) x) hpolyZ
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map, Polynomial.map_prod] at h2
    simp [Polynomial.eval_prod] at h2
    exact h2
  have hsq : IsSquare (-1 : K) := by
    apply FiniteField.isSquare_neg_one_iff.mpr
    have hcard : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 (by norm_num)
    rw [hcard, Nat.pow_mod, h]
    decide
  obtain ⟨i, hi⟩ := hsq
  have hi2 : i * i = -1 := hi.symm
  have hinj : Function.Injective (algebraMap (ZMod p) K) := RingHom.injective _
  have hi4 : i ^ 4 = 1 := by
    have e : i ^ 4 = (i * i) * (i * i) := by ring
    rw [e, hi2]; ring
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hip : i ^ p = -i := by
    have step : i ^ p = i ^ (4 * k + 3) := congrArg (fun n => i ^ n) hk
    rw [step, pow_add, pow_mul, hi4]
    have e3 : i ^ 3 = -i := by
      have e3' : i ^ 3 = (i * i) * i := by ring
      rw [e3', hi2]; ring
    rw [e3]; ring
  have hnegip : (-i) ^ p = i := by
    have hnegi4 : (-i) ^ 4 = 1 := by
      have e4 : (-i) ^ 4 = i ^ 4 := by ring
      rw [e4, hi4]
    have step : (-i) ^ p = (-i) ^ (4 * k + 3) := congrArg (fun n => (-i) ^ n) hk
    rw [step, pow_add, pow_mul, hnegi4]
    have e3 : (-i) ^ 3 = -((i * i) * i) := by ring
    rw [e3, hi2]; ring
  have hnegone : (-1 : K) ^ p = -1 := Odd.neg_one_pow ⟨2 * k + 1, by omega⟩
  have hprod1 : ∏ a : ZMod p, (algebraMap (ZMod p) K a - i) = 2 * i := by
    have step : ∏ a : ZMod p, (algebraMap (ZMod p) K a - i) = (-1) ^ p * ∏ a : ZMod p, (i - algebraMap (ZMod p) K a) := by
      rw [show (fun a => algebraMap (ZMod p) K a - i) = (fun a => -(i - algebraMap (ZMod p) K a)) from funext (fun a => by ring)]
      rw [show (fun a : ZMod p => -(i - algebraMap (ZMod p) K a)) = (fun a : ZMod p => (-1) * (i - algebraMap (ZMod p) K a)) from funext (fun a => by ring)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
    rw [step, heval i, hip, hnegone]
    ring
  have hprod2 : ∏ a : ZMod p, (algebraMap (ZMod p) K a + i) = -2 * i := by
    have step : ∏ a : ZMod p, (algebraMap (ZMod p) K a + i) = (-1) ^ p * ∏ a : ZMod p, (-i - algebraMap (ZMod p) K a) := by
      rw [show (fun a => algebraMap (ZMod p) K a + i) = (fun a => -(-i - algebraMap (ZMod p) K a)) from funext (fun a => by ring)]
      rw [show (fun a : ZMod p => -(-i - algebraMap (ZMod p) K a)) = (fun a : ZMod p => (-1) * (-i - algebraMap (ZMod p) K a)) from funext (fun a => by ring)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
    rw [step, heval (-i), hnegip, hnegone]
    ring
  have hkey : (algebraMap (ZMod p) K) (∏ a : ZMod p, (1 + a ^ 2)) = (algebraMap (ZMod p) K) 4 := by
    rw [map_prod]
    have hterm : ∀ a : ZMod p, (algebraMap (ZMod p) K) (1 + a ^ 2) = (algebraMap (ZMod p) K a - i) * (algebraMap (ZMod p) K a + i) := by
      intro a
      rw [map_add, map_one, map_pow]
      have expand : (algebraMap (ZMod p) K a - i) * (algebraMap (ZMod p) K a + i) = (algebraMap (ZMod p) K a) ^ 2 - i * i := by ring
      rw [expand, hi2]; ring
    rw [Finset.prod_congr rfl (fun a _ => hterm a), Finset.prod_mul_distrib, hprod1, hprod2]
    have hmap4 : (algebraMap (ZMod p) K) 4 = 4 := map_ofNat _ 4
    have hval : (2 : K) * i * (-2 * i) = -4 * (i * i) := by ring
    rw [hmap4, hval, hi2]; ring
  exact hinj hkey

end Native.Competemath.P113

namespace Native.Competemath.P128

/-- competemath.com problem 128. -/
theorem b_mod_77 (b : ℕ → ℤ) (h0 : b 0 = 3) (hrec : ∀ n, b (n+1) = (b n)^3 - 3 * (b n)) :
    b (10^100 + 1) % 77 = 18 := by
  have step : ∀ x : ℤ, x % 77 = 3 → (x^3 - 3*x) % 77 = 18 := by
    intro x hx
    have h1 : x ≡ 3 [ZMOD 77] := by unfold Int.ModEq; omega
    have h2 : x^3 - 3*x ≡ 3^3 - 3*3 [ZMOD 77] := (h1.pow 3).sub (h1.mul_left 3)
    have h3 : (3:ℤ)^3 - 3*3 ≡ 18 [ZMOD 77] := by decide
    have h4 := h2.trans h3
    unfold Int.ModEq at h4
    omega
  have step2 : ∀ x : ℤ, x % 77 = 18 → (x^3 - 3*x) % 77 = 3 := by
    intro x hx
    have h1 : x ≡ 18 [ZMOD 77] := by unfold Int.ModEq; omega
    have h2 : x^3 - 3*x ≡ 18^3 - 3*18 [ZMOD 77] := (h1.pow 3).sub (h1.mul_left 3)
    have h3 : (18:ℤ)^3 - 3*18 ≡ 3 [ZMOD 77] := by decide
    have h4 := h2.trans h3
    unfold Int.ModEq at h4
    omega
  have key : ∀ k : ℕ, b (2*k) % 77 = 3 ∧ b (2*k+1) % 77 = 18 := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [show 2*0 = 0 from rfl, h0]
          decide
        · have hb1 : b 1 = (b 0)^3 - 3 * b 0 := hrec 0
          rw [show 2*0+1 = 1 from rfl, hb1, h0]
          decide
    | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have e1 : 2*(n+1) = (2*n+1)+1 := by ring
        have hA : b (2*(n+1)) % 77 = 3 := by
          rw [e1, hrec (2*n+1)]
          exact step2 (b (2*n+1)) ih2
        have hB : b (2*(n+1)+1) % 77 = 18 := by
          rw [hrec (2*(n+1))]
          exact step (b (2*(n+1))) hA
        exact ⟨hA, hB⟩
  have hfinal : (10:ℕ)^100 + 1 = 2 * (5*10^99) + 1 := by ring
  rw [hfinal]
  exact (key (5*10^99)).2

end Native.Competemath.P128

namespace Native.Competemath.P140

/-- competemath.com problem 140. -/
theorem tower_of_threes_mod_1000 (T : ℕ → ℕ) (h1 : T 1 = 3) (hrec : ∀ n ≥ 1, T (n+1) = 3 ^ (T n)) : T 10 % 1000 = 387 := by
  have hh1 : T 2 = 27 := by
    have := hrec 1 (le_refl 1)
    rw [h1] at this
    norm_num at this
    exact this
  have hh2 : T 3 % 4 = 3 := by
    have e3 : T 3 = 3 ^ 27 := by rw [hrec 2 (by norm_num), hh1]
    rw [e3]
    decide
  have hh3 : T 4 % 8 = 3 := by
    have e4 : T 4 = 3 ^ (T 3) := hrec 3 (by norm_num)
    obtain ⟨m, hm⟩ : ∃ m, T 3 = 2 * m + 1 := ⟨T 3 / 2, by omega⟩
    rw [e4, hm, pow_succ, pow_mul]
    have h9 : (3:ℕ)^2 % 8 = 1 := by norm_num
    rw [Nat.mul_mod, Nat.pow_mod, h9, one_pow]
    norm_num
  have hh4 : T 5 % 16 = 11 := by
    have e4 : T 5 = 3 ^ (T 4) := hrec 4 (by norm_num)
    obtain ⟨k, hk⟩ : ∃ k, T 4 = 4 * k + 3 := ⟨T 4 / 4, by omega⟩
    rw [hk] at e4
    rw [e4]
    clear e4 hk hh3 hrec
    induction k with
    | zero => decide
    | succ n ih =>
        have hstep : 3 ^ (4 * (n+1) + 3) = 3 ^ (4*n+3) * 3^4 := by ring
        rw [hstep, Nat.mul_mod, ih]
        decide
  have hh5 : T 6 % 32 = 27 := by
    have e6 : T 6 = 3 ^ (T 5) := hrec 5 (by norm_num)
    have hk : T 5 = 16 * (T 5 / 16) + 11 := by omega
    rw [e6, hk, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hh6 : T 7 % 64 = 59 := by
    have e7 : T 7 = 3 ^ (T 6) := hrec 6 (by norm_num)
    have hk : T 6 = 32 * (T 6 / 32) + 27 := by rw [← hh5]; omega
    rw [e7, hk, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hh7 : T 8 % 160 = 27 := by
    have e8 : T 8 = 3 ^ T 7 := hrec 7 (by norm_num)
    have hk : T 7 = 64 * (T 7 / 64) + 59 := by have hdm := Nat.div_add_mod (T 7) 64; omega
    rw [e8, hk, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hh8 : T 9 % 400 = 187 := by
    have hT9 : T 9 = 3 ^ (T 8) := hrec 8 (by norm_num)
    have hq : T 8 = 160 * (T 8 / 160) + 27 := by omega
    rw [hq, pow_add, pow_mul] at hT9
    rw [hT9, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hh9 : T 10 % 1000 = 387 := by
    have e1 : T 10 = 3 ^ (T 9) := hrec 9 (by norm_num)
    rw [e1]
    have e2 : T 9 % 100 = 87 := by omega
    have e3 : T 9 = 100 * (T 9 / 100) + 87 := by omega
    rw [e3, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact hh9

end Native.Competemath.P140

namespace Native.Competemath.P143

/-- competemath.com problem 143. -/
theorem chebyshev_period :
 IsLeast {n : ℕ | 0 < n ∧ (3^45 - 1 : ℤ) ∣ (3^n - 1) ∧ (3^30 + 1 : ℤ) ∣ (3^n - 1)} 180 := by
  constructor
  · refine ⟨by norm_num, ?_, ?_⟩
    · have h1 : (3^45 - 1 : ℤ) ∣ (3^180 - 1) := by
        have h := sub_dvd_pow_sub_pow (3^45 : ℤ) 1 4
        simp only [one_pow] at h
        rw [← pow_mul, show (45*4 = 180) from by norm_num] at h
        exact h
      exact h1
    · have h2 : (3^30 + 1 : ℤ) ∣ (3^180 - 1) := by
        have key : (3^180 - 1 : ℤ) = (3^30 + 1) * (3^150 - 3^120 + 3^90 - 3^60 + 3^30 - 1) := by ring
        exact ⟨_, key⟩
      exact h2
  · intro n hn
    obtain ⟨hpos, hd1, hd2⟩ := hn
    have h3 : (45:ℕ) ∣ n := by
      have h1 : (1:ℕ) ≤ 3^45 := Nat.one_le_pow 45 3 (by norm_num)
      have h2 : (1:ℕ) ≤ 3^n := Nat.one_le_pow n 3 (by norm_num)
      have hnat : (3^45 - 1 : ℕ) ∣ (3^n - 1 : ℕ) := by zify [h1, h2]; exact hd1
      have hgcd : (3^45 - 1 : ℕ).gcd (3^n - 1) = 3 ^ (Nat.gcd 45 n) - 1 := Nat.pow_sub_one_gcd_pow_sub_one 3 45 n
      rw [Nat.gcd_eq_left hnat] at hgcd
      have heq : (3:ℕ)^45 = 3 ^ (Nat.gcd 45 n) := by
        have h3' : (1:ℕ) ≤ 3 ^ (Nat.gcd 45 n) := Nat.one_le_pow _ _ (by norm_num)
        omega
      have h45 : (45:ℕ) = Nat.gcd 45 n := Nat.pow_right_injective (by norm_num) heq
      rw [h45]; exact Nat.gcd_dvd_right 45 n
    have h4 : (60:ℕ) ∣ n := by
      set d : ℕ := 3^30 + 1 with hd_def
      have hx : (3 : ZMod d)^n = 1 := by
        have h0 : ((3^n - 1 : ℤ) : ZMod d) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast [hd_def]
          exact hd2
        push_cast at h0
        linear_combination h0
      have hord_dvd_n : orderOf (3 : ZMod d) ∣ n := orderOf_dvd_of_pow_eq_one hx
      have h30 : (3 : ZMod d)^30 = -1 := by
        have : ((d : ℕ) : ZMod d) = 0 := ZMod.natCast_self d
        rw [hd_def] at this
        push_cast at this
        linear_combination this
      have h60 : (3 : ZMod d)^60 = 1 := by
        have : (3:ZMod d)^60 = ((3:ZMod d)^30)^2 := by ring
        rw [this, h30]; ring
      have hne30 : (3 : ZMod d)^30 ≠ 1 := by
        rw [h30]
        intro h
        have h2 : ((2:ℕ) : ZMod d) = 0 := by
          have : (-1 : ZMod d) - 1 = 0 := by rw [h]; ring
          push_cast
          linear_combination -this
        have h3 : d ∣ 2 := (ZMod.natCast_eq_zero_iff 2 d).mp h2
        rw [hd_def] at h3
        norm_num at h3
      have hne20 : (3 : ZMod d)^20 ≠ 1 := by
        intro h
        have h2 : ((3^20 - 1 : ℕ) : ZMod d) = 0 := by
          have e : (3:ZMod d)^20 - 1 = 0 := by rw [h]; ring
          push_cast [Nat.cast_sub (by norm_num : (1:ℕ) ≤ 3^20)]
          linear_combination e
        have h3 : d ∣ (3^20 - 1) := (ZMod.natCast_eq_zero_iff _ d).mp h2
        rw [hd_def] at h3
        norm_num at h3
      have hne12 : (3 : ZMod d)^12 ≠ 1 := by
        intro h
        have h2 : ((3^12 - 1 : ℕ) : ZMod d) = 0 := by
          have e : (3:ZMod d)^12 - 1 = 0 := by rw [h]; ring
          push_cast [Nat.cast_sub (by norm_num : (1:ℕ) ≤ 3^12)]
          linear_combination e
        have h3 : d ∣ (3^12 - 1) := (ZMod.natCast_eq_zero_iff _ d).mp h2
        rw [hd_def] at h3
        norm_num at h3
      have hord : orderOf (3 : ZMod d) = 60 := by
        apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h60
        intro p hp hpdvd
        have hp60 : p ≤ 60 := Nat.le_of_dvd (by norm_num) hpdvd
        have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
          interval_cases p <;> revert hp hpdvd <;> decide
        rcases hcases with rfl | rfl | rfl
        · exact hne30
        · exact hne20
        · exact hne12
      rw [hord] at hord_dvd_n
      exact hord_dvd_n
    have h5 : (180:ℕ) ∣ n := by
      have hl : Nat.lcm 45 60 ∣ n := Nat.lcm_dvd h3 h4
      norm_num [Nat.lcm] at hl
      exact hl
    exact Nat.le_of_dvd hpos h5

end Native.Competemath.P143

namespace Native.Competemath.P194

/-- competemath.com problem 194. -/
theorem last_digit_conjugate_recurrence (a : ℕ → ℤ) (h0 : a 0 = 2) (h1 : a 1 = 4)
    (hrec : ∀ n, a (n + 2) = 4 * a (n + 1) - a n) :
    a (2026 ^ 2026) % 10 = 4 := by
  have hmod3 : 2026 ^ 2026 % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hperiod : ∀ k : ℕ, a (3 * k) % 10 = 2 ∧ a (3 * k + 1) % 10 = 4 ∧ a (3 * k + 2) % 10 = 4 := by
    intro k
    induction k with
    | zero =>
        have e0 : a 2 = 4 * a 1 - a 0 := hrec 0
        refine ⟨?_, ?_, ?_⟩ <;> simp only [Nat.mul_zero, Nat.zero_add] <;> omega
    | succ k ih =>
        obtain ⟨ihk0, ihk1, ihk2⟩ := ih
        have e1 : a (3 * k + 3) = 4 * a (3 * k + 2) - a (3 * k + 1) := by
          have h := hrec (3 * k + 1); rw [show 3 * k + 1 + 2 = 3 * k + 3 from by ring, show 3 * k + 1 + 1 = 3 * k + 2 from by ring] at h; exact h
        have e2 : a (3 * k + 4) = 4 * a (3 * k + 3) - a (3 * k + 2) := by
          have h := hrec (3 * k + 2); rw [show 3 * k + 2 + 2 = 3 * k + 4 from by ring, show 3 * k + 2 + 1 = 3 * k + 3 from by ring] at h; exact h
        have e3 : a (3 * k + 5) = 4 * a (3 * k + 4) - a (3 * k + 3) := by
          have h := hrec (3 * k + 3); rw [show 3 * k + 3 + 2 = 3 * k + 5 from by ring, show 3 * k + 3 + 1 = 3 * k + 4 from by ring] at h; exact h
        have hgoal : 3 * (k + 1) = 3 * k + 3 := by ring
        rw [hgoal, show 3 * k + 3 + 1 = 3 * k + 4 from by ring, show 3 * k + 3 + 2 = 3 * k + 5 from by ring]
        refine ⟨?_, ?_, ?_⟩ <;> omega
  have hk : 2026 ^ 2026 = 3 * (2026 ^ 2026 / 3) + 1 := by
    have hdm := Nat.div_add_mod (2026 ^ 2026) 3
    omega
  rw [hk]
  exact (hperiod (2026 ^ 2026 / 3)).2.1

end Native.Competemath.P194

namespace Native.Competemath.P195

/-- competemath.com problem 195. -/
theorem prime_order_field_forces_full_order
    [Fact (Nat.Prime 2)] (hprime : Nat.Prime (2 ^ 127 - 1)) :
    ∀ x : GaloisField 2 127, x ≠ 0 → x ≠ 1 → orderOf x = 2 ^ 127 - 1 := by
  intro x hx0 hx1
  have hcard : Nat.card (GaloisField 2 127) = 2 ^ 127 := GaloisField.card 2 127 (by norm_num)
  have hu : IsUnit x := Ne.isUnit hx0
  set u : (GaloisField 2 127)ˣ := hu.unit with hudef
  have hux : (u : GaloisField 2 127) = x := hu.unit_spec
  have hordu : orderOf x = orderOf u := by
    rw [← hux, orderOf_units]
  have hdvd : orderOf u ∣ Nat.card (GaloisField 2 127)ˣ := orderOf_dvd_natCard u
  have hcardu : Nat.card (GaloisField 2 127)ˣ = 2 ^ 127 - 1 := by
    rw [Nat.card_units, hcard]
  rw [hcardu] at hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h
  · exfalso
    apply hx1
    have hu1 : u = 1 := orderOf_eq_one_iff.mp h
    rw [← hux, hu1, Units.val_one]
  · rw [hordu, h]

end Native.Competemath.P195

namespace Native.Competemath.P206

/-- competemath.com problem 206. -/
theorem valuation_of_a2026 (a : ℕ → ℤ)
    (h0 : a 0 = 0) (h1 : a 1 = 3) (h2 : a 2 = 36)
    (hrec : ∀ n, a (n + 3) = 9 * a (n + 2) - 27 * a (n + 1) + 27 * a n) :
    padicValNat 3 (a 2026).natAbs = 2026 := by
  have hpow : ∀ n : ℕ, a n = (n:ℤ)^2 * 3^n ∧ a (n+1) = ((n:ℤ)+1)^2 * 3^(n+1) ∧ a (n+2) = ((n:ℤ)+2)^2 * 3^(n+2) := by
    intro n
    induction n with
    | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [h0, h1, h2]
    | succ n ih =>
      obtain ⟨ihn, ihn1, ihn2⟩ := ih
      refine ⟨ihn1, ihn2, ?_⟩
      have hr := hrec n
      rw [ihn2, ihn1, ihn] at hr
      push_cast
      rw [hr]
      ring
  have hnat : (a 2026).natAbs = 2026 ^ 2 * 3 ^ 2026 := by
    rw [(hpow 2026).1]
    push_cast
    rw [Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  have hval : padicValNat 3 (2026 ^ 2 * 3 ^ 2026) = 2026 := by
    rw [padicValNat.mul (by norm_num) (by norm_num)]
    rw [padicValNat_base_pow (by norm_num)]
    have h : padicValNat 3 (2026 ^ 2) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      norm_num
    rw [h]
  rw [hnat]
  exact hval

end Native.Competemath.P206

namespace Native.Competemath.P222

/-- competemath.com problem 222. -/
theorem cycle_coloring_mod_1000 (n k : ℕ) (hn : n = 2025) (hk : k = 6) :
    (((k : ℤ) - 1)^n + (-1:ℤ)^n * ((k:ℤ) - 1)) % 1000 = 120 := by
  subst hn hk
  have h2 : ((6:ℕ):ℤ) - 1 = 5 := by norm_num
  rw [h2]
  have h3 : (-1:ℤ)^(2025:ℕ) = -1 := by norm_num
  rw [h3]
  have h1 : (5:ℤ)^2025 % 1000 = 125 := by
    have key : ∀ k : ℕ, (5:ℤ)^(3+2*k) % 1000 = 125 := by
      intro k
      induction k with
      | zero => norm_num
      | succ n ih =>
        have : 3 + 2 * (n+1) = (3 + 2*n) + 2 := by ring
        rw [this, pow_add]
        have h25 : (5:ℤ)^2 = 25 := by norm_num
        rw [h25]
        have := Int.mul_emod ((5:ℤ)^(3+2*n)) 25 1000
        rw [this, ih]
        norm_num
    have := key 1011
    norm_num at this
    exact this
  have h4 := Int.emod_add_mul_ediv ((5:ℤ)^2025) 1000
  rw [h1] at h4
  generalize hq : (5:ℤ)^2025 / 1000 = q at h4
  generalize hp : (5:ℤ)^2025 = p at h4
  have h5 : p + (-1) * 5 = 1000 * q + 120 := by linarith
  rw [h5]
  omega

end Native.Competemath.P222

namespace Native.Competemath.P232

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 232. -/
lemma filter_mod_3_4_iff_dvd_12 (n : ℕ) :
    (n % 3 = 0 ∧ n % 4 = 0) ↔ 12 ∣ n :=
  by
    constructor
    · intro ⟨h3, h4⟩
      have d3 : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
      have d4 : 4 ∣ n := Nat.dvd_of_mod_eq_zero h4
      have : Nat.lcm 3 4 = 12 := by norm_num
      rw [← this]
      exact Nat.lcm_dvd d3 d4
    · intro h
      have d3 : 3 ∣ n := dvd_trans (by norm_num : 3 ∣ 12) h
      have d4 : 4 ∣ n := dvd_trans (by norm_num : 4 ∣ 12) h
      exact ⟨Nat.mod_eq_zero_of_dvd d3, Nat.mod_eq_zero_of_dvd d4⟩

theorem purple_pickets : (Finset.filter (fun n => n % 3 = 0 ∧ n % 4 = 0) (Finset.Icc 1 100)).card = 8 :=
  by
    have h : Finset.filter (fun n => n % 3 = 0 ∧ n % 4 = 0) (Finset.Icc 1 100) = Finset.filter (fun n => 12 ∣ n) (Finset.Icc 1 100) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨⟨h1, h2⟩, (filter_mod_3_4_iff_dvd_12 n).1 ⟨h3, h4⟩⟩
      · intro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, (filter_mod_3_4_iff_dvd_12 n).2 h3⟩
    rw [h]
    decide

end Native.Competemath.P232

namespace Native.Competemath.P60

def quadA : ℕ → ZMod 23
  | 0 => 4
  | n + 1 => quadA n ^ 2 - 2

/-- competemath.com problem 60. -/
theorem quadA_5n (n : ℕ) : quadA (5 * n) = 4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : quadA (5 * n + 1) = 14 := by
      show quadA (5 * n) ^ 2 - 2 = 14; rw [ih]; decide
    have h2 : quadA (5 * n + 2) = 10 := by
      show quadA (5 * n + 1) ^ 2 - 2 = 10; rw [h1]; decide
    have h3 : quadA (5 * n + 3) = 6 := by
      show quadA (5 * n + 2) ^ 2 - 2 = 6; rw [h2]; decide
    have h4 : quadA (5 * n + 4) = 11 := by
      show quadA (5 * n + 3) ^ 2 - 2 = 11; rw [h3]; decide
    show quadA (5 * n + 4) ^ 2 - 2 = 4
    rw [h4]; decide

end Native.Competemath.P60

namespace Native.Competemath.P107

/-- competemath.com problem 107. -/
theorem triadic_tower : 3^2026 ∣ 2026^(3^2025) + 2027^(3^2025) ∧ ¬ (3^2027 ∣ 2026^(3^2025) + 2027^(3^2025)) := by
  have hp : Nat.Prime 3 := by norm_num
  have hp1 : Odd (3:ℕ) := by decide
  have hn : Odd ((3:ℕ)^2025) := hp1.pow
  have hxy : (3:ℤ) ∣ (2026:ℤ) + 2027 := by norm_num
  have hx : ¬ (3:ℤ) ∣ (2026:ℤ) := by norm_num
  have key : emultiplicity (3:ℤ) ((2026:ℤ)^(3^2025) + (2027:ℤ)^(3^2025))
      = emultiplicity (3:ℤ) ((2026:ℤ)+2027) + emultiplicity 3 (3^2025) :=
    Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn
  have e1 : emultiplicity (3:ℤ) ((2026:ℤ)+2027) = (1:ℕ∞) := by
    rw [show (2026:ℤ)+2027 = 3^1 * 1351 by norm_num]
    exact emultiplicity_eq_coe.mpr ⟨by norm_num, by norm_num⟩
  have e2 : emultiplicity (3:ℕ) (3^2025) = (2025:ℕ∞) :=
    emultiplicity_pow_self (by norm_num) (by simp) 2025
  have total : emultiplicity (3:ℤ) ((2026:ℤ)^(3^2025) + (2027:ℤ)^(3^2025)) = (2026:ℕ∞) := by
    rw [key, e1, e2]; decide
  have final := emultiplicity_eq_coe.mp total
  obtain ⟨fd, fnd⟩ := final
  have cast_eq : ((2026^(3^2025) + 2027^(3^2025) : ℕ) : ℤ)
      = (2026:ℤ)^(3^2025) + (2027:ℤ)^(3^2025) := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · have hc : ((3^2026 : ℕ) : ℤ) ∣ ((2026^(3^2025) + 2027^(3^2025) : ℕ) : ℤ) := by
      rw [cast_eq, Nat.cast_pow, Nat.cast_ofNat]
      exact fd
    exact Int.natCast_dvd_natCast.mp hc
  · intro hcontra
    apply fnd
    have hc : ((3^2027 : ℕ) : ℤ) ∣ ((2026^(3^2025) + 2027^(3^2025) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hcontra
    rw [cast_eq, Nat.cast_pow, Nat.cast_ofNat] at hc
    have e : (2026:ℕ) + 1 = 2027 := by norm_num
    rw [e]
    exact hc

end Native.Competemath.P107

namespace Native.Competemath.P108

/-- competemath.com problem 108. -/
theorem lucas_nresidue_prime (p : ℕ) (hp : Nat.Prime p) (h : p % 5 = 2 ∨ p % 5 = 3)
    (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hrec : ∀ n : ℕ, a (n + 2) = 3 * a (n + 1) - a n) :
    (p : ℤ) ∣ a (p - 1) + 3 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have e1 : a (2 - 1) + 3 = 4 := by norm_num [ha1]
    rw [e1]; norm_num
  · set f : Polynomial (ZMod p) := Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X + Polynomial.C 1 with hf_def
    have h1 : Irreducible f := by
      rw [hf_def]
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      case hdeg => rw [show (Polynomial.X ^ 2 - Polynomial.C 3 * Polynomial.X + Polynomial.C 1 : Polynomial (ZMod p)).natDegree = 2 by compute_degree!]; decide
      intro x hx
      simp [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hx
      have hp5 : p ≠ 5 := by rintro rfl; omega
      have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
      have h5 : ¬ IsSquare (5 : ZMod p) := by
        haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        show ¬ IsSquare ((5:ℕ) : ZMod p)
        rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) (by omega)]
        rw [show (p : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) from (ZMod.natCast_mod p 5).symm]
        rcases h with hh | hh
        · rw [hh]; decide +revert
        · rw [hh]; decide +revert
      exact h5 ⟨2 * x - 3, by linear_combination -4 * hx⟩
    haveI : Fact (Irreducible f) := ⟨h1⟩
    set α : AdjoinRoot f := AdjoinRoot.root f with hα_def
    have hα_eq : α ^ 2 - 3 * α + 1 = 0 := by
      have heval := AdjoinRoot.eval₂_root f
      simpa [hf_def] using heval
    have h3 : α ^ p ≠ α ∧ (α ^ p) ^ 2 - 3 * (α ^ p) + 1 = 0 := by
      have hCharP : CharP (AdjoinRoot f) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot f)).injective p
      have hfrob : (α ^ 2 - 3 * α + 1) ^ p = (α ^ p) ^ 2 - 3 * α ^ p + 1 := by rw [add_pow_char, sub_pow_char, mul_pow]; ring_nf; rw [show ((3:AdjoinRoot f))^p = 3 from by rw [show (3:AdjoinRoot f) = ((3:ZMod p) : AdjoinRoot f) from by norm_cast, ← map_pow, ZMod.pow_card]]
      have hzero : (0:AdjoinRoot f) ^ p = (α ^ p) ^ 2 - 3 * α ^ p + 1 := by rw [← hα_eq]; exact hfrob
      have hβeq : (α ^ p) ^ 2 - 3 * α ^ p + 1 = 0 := by rw [← hzero]; exact zero_pow (Fact.out (p := Nat.Prime p)).pos.ne'
      have hfdeg : f.natDegree = 2 := by rw [hf_def]; compute_degree!
      have hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c := by
        intro c hc
        obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hc
        rcases h1.isUnit_or_isUnit hg with hu | hu
        · rw [Polynomial.isUnit_iff] at hu
          obtain ⟨r, hr, hrc⟩ := hu
          have := congrArg Polynomial.natDegree hrc
          simp at this
        · rw [Polynomial.isUnit_iff] at hu
          obtain ⟨r, hr, hrc⟩ := hu
          have hdeg : f.natDegree = (Polynomial.X - Polynomial.C c).natDegree + g.natDegree := by
            rw [hg]; exact Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) (by rw [← hrc]; exact (Polynomial.C_ne_zero.mpr hr.ne_zero))
          rw [hfdeg, Polynomial.natDegree_X_sub_C, ← hrc, Polynomial.natDegree_C] at hdeg
          omega
      have hnotmem : ∀ c : ZMod p, algebraMap (ZMod p) (AdjoinRoot f) c ≠ α := by
        intro c hceq
        apply hnoroot c
        have heq2 : (algebraMap (ZMod p) (AdjoinRoot f)) (c ^ 2 - 3 * c + 1) = 0 := by
          rw [map_add, map_sub, map_pow, map_mul, map_one, hceq]
          exact hα_eq
        have hinj := (algebraMap (ZMod p) (AdjoinRoot f)).injective
        have hc0 : c ^ 2 - 3 * c + 1 = 0 := by
          apply hinj
          rw [heq2, map_zero]
        show f.eval c = 0
        rw [hf_def]
        simp [hc0]
      have hne : α ^ p ≠ α := by
        intro hEq
        set g : Polynomial (AdjoinRoot f) := Polynomial.X ^ p - Polynomial.X with hg_def
        have hp1 : p ≠ 1 := (Fact.out (p := Nat.Prime p)).one_lt.ne'
        have hpge2 : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
        have hgdeg : g.natDegree = p := by
          rw [hg_def]
          compute_degree!
          · rw [if_neg (fun h => hp1 h.symm)]
            simp
          · omega
        have hgne : g ≠ 0 := by
          intro hcontra
          rw [hcontra, Polynomial.natDegree_zero] at hgdeg
          omega
        set S : Finset (AdjoinRoot f) := insert α (Finset.image (algebraMap (ZMod p) (AdjoinRoot f)) Finset.univ) with hS_def
        have hScard : S.card = p + 1 := by
          rw [hS_def, Finset.card_insert_of_notMem]
          · rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) (AdjoinRoot f)).injective, Finset.card_univ, ZMod.card]
          · simp only [Finset.mem_image, Finset.mem_univ, true_and]
            rintro ⟨c, hc⟩
            exact hnotmem c hc
        have hSsub : S ⊆ g.roots.toFinset := by
          rw [hS_def]
          intro x hx
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
          simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
          rcases hx with hx | ⟨c, hxc⟩
          · rw [hx]; show g.IsRoot α; rw [hg_def]; simp [Polynomial.IsRoot, hEq]
          · rw [← hxc]
            show g.IsRoot (algebraMap (ZMod p) (AdjoinRoot f) c)
            have heq2 : (algebraMap (ZMod p) (AdjoinRoot f) c) ^ p = algebraMap (ZMod p) (AdjoinRoot f) c := by
              rw [← map_pow, ZMod.pow_card]
            rw [hg_def, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, heq2, sub_self]
        have hcard_le : S.card ≤ g.natDegree := by
          calc S.card ≤ g.roots.toFinset.card := Finset.card_le_card hSsub
          _ ≤ g.roots.card := Multiset.toFinset_card_le _
          _ ≤ g.natDegree := Polynomial.card_roots' g
        rw [hScard, hgdeg] at hcard_le
        omega
      exact ⟨hne, hβeq⟩
    obtain ⟨hβne, hβeq⟩ := h3
    have h5 : α + α ^ p = 3 ∧ α * α ^ p = 1 := by
      have hne : α - α ^ p ≠ 0 := sub_ne_zero.mpr (Ne.symm hβne)
      have key : (α - α ^ p) * (α + α ^ p - 3) = 0 := by linear_combination hα_eq - hβeq
      have hsum' : α + α ^ p - 3 = 0 := (mul_eq_zero.mp key).resolve_left hne
      have hsum : α + α ^ p = 3 := sub_eq_zero.mp hsum'
      have hprod : α * α ^ p = 1 := by linear_combination α * hsum - hα_eq
      exact ⟨hsum, hprod⟩
    obtain ⟨hsum, hprod⟩ := h5
    have h6 : α ^ (p + 1) = 1 := by
      rw [pow_succ, mul_comm, hprod]
    have h7 : ∀ n : ℕ, (a n : AdjoinRoot f) * (α - α ^ p) = α ^ n - (α ^ p) ^ n := by
      have key : ∀ m : ℕ, (a m : AdjoinRoot f) * (α - α ^ p) = α ^ m - (α ^ p) ^ m ∧
          (a (m+1) : AdjoinRoot f) * (α - α ^ p) = α ^ (m+1) - (α ^ p) ^ (m+1) := by
        intro m
        induction m with
        | zero => constructor <;> simp [ha0, ha1]
        | succ k ih =>
          obtain ⟨ih0, ih1⟩ := ih
          refine ⟨ih1, ?_⟩
          rw [hrec k]
          push_cast
          linear_combination 3 * ih1 - ih0 - α ^ k * hα_eq + (α ^ p) ^ k * hβeq
      intro n
      exact (key n).1
    have h8 : (a (p - 1) : AdjoinRoot f) = -3 := by
      have hp2' : 2 ≤ p := (Fact.out (p := Nat.Prime p)).two_le
      have e2 : p - 1 + (p + 1) = 2 * p := by omega
      have key1 : α ^ (p - 1) = (α ^ p) ^ 2 := by rw [← pow_mul, mul_comm p 2, ← e2, pow_add, h6, mul_one]
      have hnz : α ^ p ≠ 0 := by rintro h0; rw [h0, mul_zero] at hprod; exact zero_ne_one hprod
      have step : (α ^ p) ^ (p - 1) * α ^ (p - 1) = 1 := by
        rw [← mul_pow, mul_comm (α ^ p) α, hprod, one_pow]
      rw [key1] at step
      have e4 : α ^ 2 * (α ^ p) ^ 2 = 1 := by rw [← mul_pow, hprod, one_pow]
      have key2 : (α ^ p) ^ (p - 1) = α ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hnz) (step.trans e4.symm)
      have hne : α - α ^ p ≠ 0 := sub_ne_zero.mpr (Ne.symm hβne)
      have heq := h7 (p - 1)
      rw [key1, key2] at heq
      have heq2 : (a (p - 1) : AdjoinRoot f) * (α - α ^ p) = (-3) * (α - α ^ p) := by
        rw [heq]; linear_combination (α ^ p - α) * hsum
      exact mul_right_cancel₀ hne heq2
    have h9 : (a (p - 1) : ZMod p) = -3 := by
      have hmap := map_intCast (algebraMap (ZMod p) (AdjoinRoot f)) (a (p - 1))
      rw [h8] at hmap
      have hneg : (algebraMap (ZMod p) (AdjoinRoot f)) (-3 : ZMod p) = -3 := by
        rw [map_neg]
        exact congrArg Neg.neg (map_ofNat _ 3)
      rw [← hneg] at hmap
      exact (algebraMap (ZMod p) (AdjoinRoot f)).injective hmap
    have h10 : ((a (p - 1) + 3 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [h9]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a (p - 1) + 3) p).mp h10

end Native.Competemath.P108

namespace Native.Competemath.P66

/-- competemath.com problem 66. -/
theorem n_pow_n_mod_succ (n : ℕ) (hn : 1 ≤ n) : n ^ n % (n + 1) = if n % 2 = 0 then 1 else n := by
  have hm : 1 < n + 1 := by omega
  haveI : Fact (1 < n + 1) := ⟨hm⟩
  have hcast : (n : ZMod (n+1)) = -1 := by
    have h0 : ((n+1 : ℕ) : ZMod (n+1)) = 0 := by exact_mod_cast ZMod.natCast_self (n+1)
    push_cast at h0
    linear_combination h0
  have hpow : ((n^n : ℕ) : ZMod (n+1)) = (-1:ZMod (n+1))^n := by
    push_cast
    rw [hcast]
  by_cases h : n % 2 = 0
  · have heq1 : ((n^n:ℕ) : ZMod (n+1)) = 1 := by
      rw [hpow]
      exact (Nat.even_iff.mpr h).neg_one_pow
    have hval : n^n % (n+1) = 1 := by
      have hv : ((n^n:ℕ) : ZMod (n+1)).val = (1 : ZMod (n+1)).val := by rw [heq1]
      rwa [ZMod.val_natCast, ZMod.val_one] at hv
    simp [h, hval]
  · have heq2 : ((n^n:ℕ) : ZMod (n+1)) = (n : ZMod (n+1)) := by
      rw [hpow, Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), hcast]
    have hval2 : n^n % (n+1) = n % (n+1) := by
      have hv : ((n^n:ℕ) : ZMod (n+1)).val = ((n:ℕ) : ZMod (n+1)).val := by rw [heq2]
      rwa [ZMod.val_natCast, ZMod.val_natCast] at hv
    have hlt : n % (n+1) = n := Nat.mod_eq_of_lt (by omega)
    simp [h, hval2, hlt]

end Native.Competemath.P66

namespace Native.Competemath.P122

/-- competemath.com problem 122. -/
theorem billiard_corner_bounces : (∀ n : ℕ, 0 < n → Nat.lcm n (n + 1) / n + Nat.lcm n (n + 1) / (n + 1) - 2 = 2 * n - 1) ∧ Nat.lcm (10 ^ 12) (10 ^ 12 + 1) / 10 ^ 12 + Nat.lcm (10 ^ 12) (10 ^ 12 + 1) / (10 ^ 12 + 1) - 2 = 1999999999999 := by
  have key : ∀ n : ℕ, 0 < n → Nat.lcm n (n + 1) / n + Nat.lcm n (n + 1) / (n + 1) - 2 = 2 * n - 1 := by
    intro n hn
    have hcop : Nat.Coprime n (n+1) := by simp [Nat.Coprime]
    have hlcm : Nat.lcm n (n+1) = n * (n+1) := Nat.Coprime.lcm_eq_mul hcop
    rw [hlcm]
    have h1 : n * (n+1) / n = n+1 := by
      rw [Nat.mul_div_cancel_left]
      exact hn
    have h2 : n * (n+1) / (n+1) = n := by
      rw [Nat.mul_div_cancel]
      omega
    rw [h1, h2]
    omega
  refine ⟨key, ?_⟩
  have hk := key (10^12) (by norm_num)
  rw [hk]
  norm_num

end Native.Competemath.P122

namespace Native.Competemath.P133

/-- competemath.com problem 133. -/
theorem pell_sequence_freezes_at_two (c : ℕ → ZMod 127) (h0 : c 0 = 14) (hrec : ∀ n, c (n + 1) = c n ^ 2 - 2) : ∀ n : ℕ, 6 ≤ n → c n = 2 := by
  have hc1 : c 1 = 67 := by rw [hrec 0, h0]; decide
  have hc2 : c 2 = 42 := by rw [hrec 1, hc1]; decide
  have hc3 : c 3 = 111 := by rw [hrec 2, hc2]; decide
  have hc4 : c 4 = 0 := by rw [hrec 3, hc3]; decide
  have hc5 : c 5 = 125 := by rw [hrec 4, hc4]; decide
  have hc6 : c 6 = 2 := by rw [hrec 5, hc5]; decide
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hc6
  | succ k hk ih => rw [hrec k, ih]; decide

end Native.Competemath.P133

namespace Native.Competemath.P161

/-- competemath.com problem 161. -/
theorem smallest_f1 :
    IsLeast {c : ℤ | 1 < c ∧ ∃ f : ℤ → ℤ,
      (∀ m n : ℤ, 0 < n → n < m → f (m + n) + f (m - n) = 2 * f m + 2 * f n) ∧
      f 1 = c ∧
      (∀ p ∈ ({3,5,7,11,13,17,19,23} : Finset ℤ), (p - 1) ∣ (f p - 1))}
    7921 := by
  constructor
  · have h1 : 1 < (7921:ℤ) ∧ ∃ f : ℤ → ℤ,
        (∀ m n : ℤ, 0 < n → n < m → f (m + n) + f (m - n) = 2 * f m + 2 * f n) ∧
        f 1 = 7921 ∧
        (∀ p ∈ ({3,5,7,11,13,17,19,23} : Finset ℤ), (p - 1) ∣ (f p - 1)) := by
          refine ⟨by norm_num, fun n => 7921 * n^2, ?_, ?_, ?_⟩
          · intro m n hn hm
            ring
          · norm_num
          · intro p hp
            fin_cases hp <;> decide
    exact h1
  · intro c hc
    obtain ⟨hc1, f, hfeq, hf1, hfdvd⟩ := hc
    have h2 : f 2 = 4 * c := by
      have e1 := hfeq 2 1 (by norm_num) (by norm_num)
      have e2 := hfeq 3 1 (by norm_num) (by norm_num)
      have e3 := hfeq 3 2 (by norm_num) (by norm_num)
      have e4 := hfeq 4 1 (by norm_num) (by norm_num)
      norm_num at e1 e2 e3 e4
      omega
    have h3 : ∀ n : ℤ, 1 ≤ n → f n = c * n ^ 2 := by
      intro n hn
      have key : f n = c * n ^ 2 ∧ f (n+1) = c * (n+1)^2 := by
        induction n, hn using Int.le_induction with
        | base =>
            constructor
            · rw [hf1]; ring
            · have e : (1:ℤ)+1 = 2 := by norm_num
              rw [e, h2]; ring
        | succ n hn ih =>
            obtain ⟨ih1, ih2⟩ := ih
            refine ⟨ih2, ?_⟩
            have heq := hfeq (n+1) 1 (by norm_num) (by omega)
            have hsub : (n+1) - 1 = n := by ring
            rw [hsub] at heq
            have goal_eq : f (n+1+1) = 2 * f (n+1) + 2 * f 1 - f n := by linarith [heq]
            rw [goal_eq, ih2, hf1, ih1]
            ring
      exact key.1
    have h4 : (7920:ℤ) ∣ (c - 1) := by
      have hp17 := hfdvd 17 (by decide)
      have hp19 := hfdvd 19 (by decide)
      have hp11 := hfdvd 11 (by decide)
      have hp23 := hfdvd 23 (by decide)
      rw [h3 17 (by norm_num)] at hp17
      rw [h3 19 (by norm_num)] at hp19
      rw [h3 11 (by norm_num)] at hp11
      rw [h3 23 (by norm_num)] at hp23
      norm_num at hp17 hp19 hp11 hp23
      have f16 : (16:ℤ) ∣ (c - 1) := by
        obtain ⟨k, hk⟩ := hp17
        exact ⟨k - 18 * c, by linarith⟩
      have f18 : (18:ℤ) ∣ (c - 1) := by
        obtain ⟨k, hk⟩ := hp19
        exact ⟨k - 20 * c, by linarith⟩
      have f10 : (10:ℤ) ∣ (c - 1) := by
        obtain ⟨k, hk⟩ := hp11
        exact ⟨k - 12 * c, by linarith⟩
      have f22 : (22:ℤ) ∣ (c - 1) := by
        obtain ⟨k, hk⟩ := hp23
        exact ⟨k - 24 * c, by linarith⟩
      have f9 : (9:ℤ) ∣ (c - 1) := dvd_trans (by norm_num) f18
      have f5 : (5:ℤ) ∣ (c - 1) := dvd_trans (by norm_num) f10
      have f11 : (11:ℤ) ∣ (c - 1) := dvd_trans (by norm_num) f22
      clear hp17 hp19 hp11 hp23 hfdvd h3 hc1 hfeq hf1 h2 f18 f10 f22 f
      omega
    have h5 : (0:ℤ) < c - 1 := by omega
    have h6 : (7920:ℤ) ≤ c - 1 := Int.le_of_dvd h5 h4
    omega

end Native.Competemath.P161

namespace Native.Competemath.P196

/-- competemath.com problem 196. -/
theorem bipartite_spanning_trees_mod (k : ℕ) :
    (2026 * 2 ^ (100 * k + 25)) % 1000 = 232 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    have heq : 100 * (n + 1) + 25 = (100 * n + 25) + 100 := by ring
    rw [heq, pow_add, ← Nat.mul_assoc, Nat.mul_mod, ih]
    norm_num

end Native.Competemath.P196

namespace Native.Competemath.P204

/-- competemath.com problem 204. -/
theorem safe_prime_two_groups (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hqeq : q = 2 * p + 1) : ∃ x : (ZMod q)ˣ, orderOf x = p := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := ZMod.card_units q
  have hdvd : p ∣ Fintype.card (ZMod q)ˣ := by
    rw [hcard, hqeq]
    simp
  exact exists_prime_orderOf_dvd_card p hdvd

end Native.Competemath.P204

namespace Native.Competemath.P205

/-- competemath.com problem 205. -/
theorem paley_triangle_count (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) (h2 : 5 < p) : 48 ∣ (p * (p - 1) * (p - 5)) ∧ (p = 1000000009 → (p * (p - 1) * (p - 5)) / 48 = 20833333770833336250000006) := by
  have hStep1 : 48 ∣ (p - 1) * (p - 5) := by
    have hp4 : p = 4 * (p / 4) + 1 := by have := Nat.div_add_mod p 4; omega
    have e1 : p - 1 = 4 * (p / 4) := by omega
    have e2 : p - 5 = 4 * (p / 4 - 1) := by omega
    have h16 : 16 ∣ (p - 1) * (p - 5) := ⟨(p / 4) * (p / 4 - 1), by rw [e1, e2]; ring⟩
    have h3ne : ¬ (3 ∣ p) := by
      intro hdvd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h | h
      · omega
      · omega
    have hmod3 : p % 3 ≠ 0 := fun h => h3ne (Nat.dvd_of_mod_eq_zero h)
    have hp3 : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
    have h3 : 3 ∣ (p - 1) * (p - 5) := by
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with hm | hm
      · have e3 : p - 1 = 3 * (p / 3) := by omega
        have hd : (3:ℕ) ∣ (p - 1) := ⟨p / 3, e3⟩
        exact hd.mul_right _
      · have e4 : p - 5 = 3 * (p / 3 - 1) := by omega
        have hd : (3:ℕ) ∣ (p - 5) := ⟨p / 3 - 1, e4⟩
        exact hd.mul_left _
    have hcop : Nat.Coprime 16 3 := by decide
    have := hcop.mul_dvd_of_dvd_of_dvd h16 h3
    norm_num at this
    exact this
  have hStep2 : p = 1000000009 → (p * (p - 1) * (p - 5)) / 48 = 20833333770833336250000006 := by
    intro hp
    subst hp
    norm_num
  refine ⟨?_, hStep2⟩
  have hmul : 48 ∣ p * ((p - 1) * (p - 5)) := hStep1.mul_left p
  rwa [mul_assoc]

end Native.Competemath.P205

namespace Native.Competemath.P230

/-- competemath.com problem 230. -/
lemma two_pow_ten_mod_41 : 2 ^ 10 % 41 = 40 :=
  by
    rfl

lemma two_pow_twenty_mod_41 : 2 ^ 20 % 41 = 1 :=
  by
    rw [show 20 = 10 * 2 by norm_num, pow_mul, Nat.pow_mod, two_pow_ten_mod_41]

lemma no_smaller_positive_exponent : ∀ k < 20, 0 < k → 2 ^ k % 41 ≠ 1 :=
  by
    intro k hk hkpos
    interval_cases k <;> simp <;> decide

theorem card_shuffle_order :
    2 ^ 20 % 41 = 1 ∧ ∀ k < 20, 0 < k → 2 ^ k % 41 ≠ 1 :=
  by
    exact ⟨two_pow_twenty_mod_41, no_smaller_positive_exponent⟩

end Native.Competemath.P230
