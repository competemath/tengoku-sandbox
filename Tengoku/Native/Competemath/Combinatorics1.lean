/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P51

/-- competemath.com problem 51. -/
theorem vandermonde_self (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 = Nat.choose (2 * n) n := by
  have h := Nat.add_choose_eq n n n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i * n.choose j)] at h
  simp only [Nat.succ_eq_add_one] at h
  have h2 : ∀ k ∈ Finset.range (n + 1), n.choose k * n.choose (n - k) = n.choose k ^ 2 := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.choose_symm hk, sq]
  rw [Finset.sum_congr rfl h2] at h
  rw [← h]
  ring_nf

end Native.Competemath.P51

namespace Native.Competemath.P52

/-- competemath.com problem 52. -/
theorem stirling_diagonal (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * ↑(n.choose k) * (k : ℤ) ^ n = ↑(Nat.factorial n) := by
  have key : (fwdDiff (1:ℤ))^[n] (fun r : ℤ => r ^ n) = fun _ => (n.factorial : ℤ) := fwdDiff_iter_eq_factorial
  have key2 := fwdDiff_iter_eq_sum_shift (1:ℤ) (fun r : ℤ => r ^ n) n (0:ℤ)
  rw [key] at key2
  simp only [smul_eq_mul, zero_add, nsmul_eq_mul, mul_one] at key2
  rw [← key2]

end Native.Competemath.P52

namespace Native.Competemath.P53

/-- competemath.com problem 53. -/
theorem radical_census (n : ℕ) (hn : 0 < n) : ((Finset.Icc 1 (n ^ 2 - 1)).filter (fun k => k - Nat.sqrt k ^ 2 < Nat.sqrt k)).card = Nat.choose n 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hbase : (Finset.Icc 1 (1 ^ 2 - 1) : Finset ℕ) = ∅ := by decide
    rw [hbase]
    simp
  | succ n hn ih =>
    have e1 : (n+1)^2 = n^2 + 2*n + 1 := by ring
    have e2 : 1 ≤ n^2 := by nlinarith
    have hsplit : (Finset.Icc 1 ((n+1)^2 - 1) : Finset ℕ) = Finset.Icc 1 (n^2-1) ∪ Finset.Ioc (n^2-1) ((n+1)^2-1) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (n^2-1) : Finset ℕ) (Finset.Ioc (n^2-1) ((n+1)^2-1)) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1
      simp only [Finset.mem_Ioc] at hx2
      omega
    have hcard2 : ((Finset.Ioc (n^2-1) ((n+1)^2-1) : Finset ℕ).filter (fun k => k - Nat.sqrt k ^ 2 < Nat.sqrt k)).card = n := by
      have hset : (Finset.Ioc (n^2-1) ((n+1)^2-1) : Finset ℕ) = Finset.Icc (n^2) (n^2+2*n) := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      have hsqrt_eq : ∀ k, n^2 ≤ k → k ≤ n^2 + 2*n → Nat.sqrt k = n := by
        intro k h1 h2
        have le1 : n * n ≤ k := by nlinarith
        have lt1 : k < (n+1) * (n+1) := by nlinarith
        have hle : n ≤ Nat.sqrt k := Nat.le_sqrt.mpr le1
        have hlt : Nat.sqrt k < n + 1 := Nat.sqrt_lt.mpr lt1
        omega
      have hfilter_eq : (Finset.Icc (n^2) (n^2+2*n) : Finset ℕ).filter (fun k => k - Nat.sqrt k ^ 2 < Nat.sqrt k) = Finset.Icc (n^2) (n^2+n-1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hk1, hk2⟩, hk3⟩
          have hs := hsqrt_eq k hk1 hk2
          rw [hs] at hk3
          omega
        · rintro ⟨hk1, hk2⟩
          have hk2' : k ≤ n^2 + 2*n := by omega
          have hs := hsqrt_eq k hk1 hk2'
          refine ⟨⟨hk1, hk2'⟩, ?_⟩
          rw [hs]
          omega
      rw [hset, hfilter_eq, Nat.card_Icc]
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    rw [ih, hcard2]
    have hpascal : Nat.choose (n+1) 2 = Nat.choose n 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      ring
    omega

end Native.Competemath.P53

namespace Native.Competemath.P54

/-- competemath.com problem 54. -/
theorem carry_count (n : ℕ) (hn : 1 ≤ n) : padicValNat 2 (Nat.choose (2 ^ (2 * n)) (2 ^ n)) = n := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdig_sub1 : ∀ m : ℕ, (Nat.digits 2 (2 ^ m - 1)).sum = m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h2 : 2 ^ (k+1) - 1 = 2 * (2 ^ k - 1) + 1 := by
        have h1k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hpow : 2 ^ (k+1) = 2 * 2 ^ k := by ring
        omega
      rw [h2, Nat.digits_def' (by norm_num : 1 < 2) (by omega)]
      have hdiv : (2 * (2 ^ k - 1) + 1) / 2 = 2 ^ k - 1 := by omega
      rw [hdiv]
      simp [ih]
      omega
  have hshift : ∀ k m : ℕ, m ≠ 0 → (Nat.digits 2 (2 ^ k * m)).sum = (Nat.digits 2 m).sum := by
    intro k
    induction k with
    | zero => intro m hm; simp
    | succ j ih =>
      intro m hm
      have hpow : 2 ^ (j+1) * m = 2 * (2 ^ j * m) := by ring
      rw [hpow, Nat.digits_def' (by norm_num : 1 < 2) (by positivity)]
      have hmod : (2 * (2 ^ j * m)) % 2 = 0 := by omega
      have hdiv : (2 * (2 ^ j * m)) / 2 = 2 ^ j * m := by omega
      rw [hmod, hdiv]
      simp [ih m hm]
  have hchoose_formula : ∀ n' k' : ℕ, k' ≤ n' → padicValNat 2 (n'.choose k') = (Nat.digits 2 k').sum + (Nat.digits 2 (n' - k')).sum - (Nat.digits 2 n').sum := by
    intro n' k' h
    have := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := k') (n := n') h
    simpa using this
  have hk_le_n : 2 ^ n ≤ 2 ^ (2 * n) := by
    apply Nat.pow_le_pow_right
    · norm_num
    · omega
  have hdig_k : (Nat.digits 2 (2 ^ n)).sum = 1 := by
    have := hshift n 1 (by norm_num)
    simpa using this
  have hdig_N : (Nat.digits 2 (2 ^ (2 * n))).sum = 1 := by
    have := hshift (2 * n) 1 (by norm_num)
    simpa using this
  have hsub_eq : 2 ^ (2 * n) - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
    have h1n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpow2 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
    rw [hpow2, Nat.mul_sub_one]
  have hdig_diff : (Nat.digits 2 (2 ^ (2 * n) - 2 ^ n)).sum = n := by
    rw [hsub_eq]
    have hm_ne : 2 ^ n - 1 ≠ 0 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by ring
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    rw [hshift n (2 ^ n - 1) hm_ne]
    exact hdig_sub1 n
  rw [hchoose_formula (2 ^ (2*n)) (2^n) hk_le_n, hdig_k, hdig_N, hdig_diff]
  omega

end Native.Competemath.P54

namespace Native.Competemath.P56

/-- competemath.com problem 56. -/
theorem alternating_binom_collapse (n : ℕ) : ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) * ((n + k).choose k : ℤ)) = (-1 : ℤ)^n := by
  have hneg1 : ∀ (m : ℕ) (x : ℤ), (Int.negOnePow (m:ℤ)) • x = (-1:ℤ)^m * x := by
    intro m x
    exact?
  have hterm : ∀ k, Ring.choose (-(n:ℤ)-1) k = (-1:ℤ)^k * ((n+k).choose k : ℤ) := by
    intro k
    have h1 : -(n:ℤ)-1 = -((n:ℤ)+1) := by ring
    rw [h1, Ring.choose_neg]
    have h2 : (n:ℤ)+1+(k:ℤ)-1 = ((n+k : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Ring.choose_natCast, hneg1]
  have hvander : Ring.choose (-1 : ℤ) n = ∑ ij ∈ Finset.antidiagonal n, Ring.choose (-(n:ℤ)-1) ij.1 * Ring.choose (n:ℤ) ij.2 := by
    have h := Ring.add_choose_eq (R:=ℤ) (r:=-(n:ℤ)-1) (s:=(n:ℤ)) n (mul_comm _ _)
    have heq : -(n:ℤ)-1+(n:ℤ) = -1 := by ring
    rwa [heq] at h
  have hrange : ∑ ij ∈ Finset.antidiagonal n, Ring.choose (-(n:ℤ)-1) ij.1 * Ring.choose (n:ℤ) ij.2
      = ∑ k ∈ Finset.range (n+1), Ring.choose (-(n:ℤ)-1) k * Ring.choose (n:ℤ) (n-k) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => Ring.choose (-(n:ℤ)-1) i * Ring.choose (n:ℤ) j) n
  have hsymm : ∀ k ∈ Finset.range (n+1), Ring.choose (n:ℤ) (n-k) = Ring.choose (n:ℤ) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : k ≤ n := by omega
    rw [Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm hk']
  have hchooseneg1 : Ring.choose (-1:ℤ) n = (-1:ℤ)^n := by
    have h1 : (-1:ℤ) = -(1:ℤ) := by ring
    rw [h1, Ring.choose_neg]
    have h2 : (1:ℤ)+(n:ℤ)-1 = (n:ℤ) := by ring
    rw [h2, Ring.choose_natCast, Nat.choose_self]
    simp [hneg1]
  have final : ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) * ((n + k).choose k : ℤ))
      = ∑ k ∈ Finset.range (n+1), Ring.choose (-(n:ℤ)-1) k * Ring.choose (n:ℤ) k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hterm k, Ring.choose_natCast]
    ring
  rw [final, ← hchooseneg1, hvander, hrange]
  exact Finset.sum_congr rfl (fun k hk => by rw [hsymm k hk])

end Native.Competemath.P56

namespace Native.Competemath.P57

/-- competemath.com problem 57. -/
theorem pascal_ternary_count (m : ℕ) : (Finset.filter (fun p : ℕ × ℕ => ¬ 3 ∣ Nat.choose p.1 p.2) (Finset.range (3 ^ m) ×ˢ Finset.range (3 ^ m))).card = 6 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have key : ∀ n k : ℕ, ¬ (3 ∣ Nat.choose n k) ↔ (¬ 3 ∣ Nat.choose (n % 3) (k % 3)) ∧ (¬ 3 ∣ Nat.choose (n / 3) (k / 3)) := by
      intro n k
      have hmod : Nat.choose n k ≡ (Nat.choose (n % 3) (k % 3)) * (Nat.choose (n / 3) (k / 3)) [MOD 3] :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat
      have hdvd : 3 ∣ Nat.choose n k ↔ 3 ∣ (Nat.choose (n % 3) (k % 3)) * (Nat.choose (n / 3) (k / 3)) := by
        rw [Nat.ModEq] at hmod
        rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hmod]
      rw [hdvd, Nat.Prime.dvd_mul Nat.prime_three]
      tauto
    have hbij : ∀ n < 3 ^ (m + 1), n % 3 < 3 ∧ n / 3 < 3 ^ m := by
      intro n hn
      refine ⟨Nat.mod_lt n (by norm_num), ?_⟩
      have h3 : n < 3 ^ m * 3 := by rw [pow_succ] at hn; exact hn
      exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr h3
    have hcard3 : (Finset.filter (fun p : ℕ × ℕ => ¬ 3 ∣ Nat.choose p.1 p.2) (Finset.range 3 ×ˢ Finset.range 3)).card = 6 := by
      decide
    have hbijcard : (Finset.filter (fun p : ℕ × ℕ => ¬ 3 ∣ Nat.choose p.1 p.2) (Finset.range (3 ^ (m+1)) ×ˢ Finset.range (3 ^ (m+1)))).card
        = ((Finset.filter (fun p : ℕ × ℕ => ¬ 3 ∣ Nat.choose p.1 p.2) (Finset.range 3 ×ˢ Finset.range 3)) ×ˢ (Finset.filter (fun p : ℕ × ℕ => ¬ 3 ∣ Nat.choose p.1 p.2) (Finset.range (3^m) ×ˢ Finset.range (3^m)))).card := by
      apply Finset.card_bij' (fun p _ => ((p.1 % 3, p.2 % 3), (p.1 / 3, p.2 / 3))) (fun q _ => (3 * q.2.1 + q.1.1, 3 * q.2.2 + q.1.2))
      · intro a ha
        rw [Prod.ext_iff]
        simp only []
        omega
      · intro a ha
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at ha
        obtain ⟨⟨⟨ha11, ha12⟩, _⟩, ⟨⟨ha21, ha22⟩, _⟩⟩ := ha
        ext <;> simp <;> omega
      · intro a ha
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at ha ⊢
        exact ⟨⟨⟨(hbij a.1 ha.1.1).1, (hbij a.2 ha.1.2).1⟩, ((key a.1 a.2).mp ha.2).1⟩, ⟨(hbij a.1 ha.1.1).2, (hbij a.2 ha.1.2).2⟩, ((key a.1 a.2).mp ha.2).2⟩
      · intro a ha
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at ha ⊢
        have hn : 3 * a.2.1 + a.1.1 < 3 ^ (m + 1) := by
          rw [pow_succ]
          omega
        have hk : 3 * a.2.2 + a.1.2 < 3 ^ (m + 1) := by
          rw [pow_succ]
          omega
        refine ⟨⟨hn, hk⟩, ?_⟩
        rw [key]
        have e1 : (3 * a.2.1 + a.1.1) % 3 = a.1.1 := by omega
        have e2 : (3 * a.2.2 + a.1.2) % 3 = a.1.2 := by omega
        have e3 : (3 * a.2.1 + a.1.1) / 3 = a.2.1 := by omega
        have e4 : (3 * a.2.2 + a.1.2) / 3 = a.2.2 := by omega
        rw [e1, e2, e3, e4]
        exact ⟨ha.1.2, ha.2.2⟩
    rw [hbijcard, Finset.card_product, hcard3, ih, pow_succ]
    ring

end Native.Competemath.P57

namespace Native.Competemath.P62

/-- competemath.com problem 62. -/
theorem totient_collapse (n : ℕ) : ∑ k ∈ Finset.range n, Nat.totient ((k + 1) ^ 2) / Nat.totient (k + 1) = n * (n + 1) / 2 := by
  have key : ∀ m : ℕ, Nat.totient (m^2) = m * Nat.totient m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      match m, ih with
      | 0, _ => simp
      | 1, _ => simp
      | (m+2), ih =>
        set p := (m+2).minFac with hp_def
        have hp : p.Prime := Nat.minFac_prime (by omega)
        obtain ⟨m', hm'⟩ := Nat.minFac_dvd (m+2)
        have hm'pos : 0 < m' := by
          rcases Nat.eq_zero_or_pos m' with h0 | h0
          · rw [h0, Nat.mul_zero] at hm'; omega
          · exact h0
        have hp1 : 1 < p := hp.one_lt
        have hm'lt : m' < m + 2 := by
          rw [hm']
          nlinarith
        by_cases hdvd : p ∣ m'
        · have e1 : Nat.totient (m+2) = p * Nat.totient m' := by
            rw [hm']
            exact Nat.totient_mul_of_prime_of_dvd hp hdvd
          have hdvd2 : p ∣ m'^2 := by rw [pow_two]; exact hdvd.mul_right m'
          have e2 : Nat.totient ((m+2)^2) = p * Nat.totient (p * m'^2) := by
            have : (m+2)^2 = p * (p * m'^2) := by rw [hm']; ring
            rw [this]
            exact Nat.totient_mul_of_prime_of_dvd hp (Dvd.dvd.mul_left hdvd2 p)
          have e3 : Nat.totient (p * m'^2) = p * Nat.totient (m'^2) := Nat.totient_mul_of_prime_of_dvd hp hdvd2
          have e4 : Nat.totient (m'^2) = m' * Nat.totient m' := ih m' hm'lt
          rw [e2, e3, e4, e1, hm']
          ring
        · have e1 : Nat.totient (m+2) = (p-1) * Nat.totient m' := by
            rw [hm']
            exact Nat.totient_mul_of_prime_of_not_dvd hp hdvd
          have hcop : Nat.Coprime p m' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
          have hcop2 : Nat.Coprime (p^2) (m'^2) := hcop.pow 2 2
          have e2 : Nat.totient ((m+2)^2) = Nat.totient (p^2) * Nat.totient (m'^2) := by
            have : (m+2)^2 = p^2 * m'^2 := by rw [hm']; ring
            rw [this]
            exact Nat.totient_mul hcop2
          have e3 : Nat.totient (p^2) = p * (p-1) := by
            have hpp : p^2 = p^(1+1) := by ring
            rw [hpp, Nat.totient_prime_pow_succ hp 1]
            ring
          have e4 : Nat.totient (m'^2) = m' * Nat.totient m' := ih m' hm'lt
          rw [e2, e3, e4, e1, hm']
          ring
  have term : ∀ k ∈ Finset.range n, Nat.totient ((k+1)^2) / Nat.totient (k+1) = k+1 := by
    intro k _
    rw [key (k+1)]
    exact Nat.mul_div_cancel _ (Nat.totient_pos.mpr (Nat.succ_pos k))
  have gauss2 : ∀ N : ℕ, 2 * (∑ k ∈ Finset.range N, (k+1)) = N * (N+1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring
  rw [Finset.sum_congr rfl term]
  have h2 := gauss2 n
  omega

end Native.Competemath.P62

namespace Native.Competemath.P105

/-- competemath.com problem 105. -/
theorem parity_balanced_grid (n : ℕ) (hn : 0 < n) : Fintype.card {M : Matrix (Fin n) (Fin n) (ZMod 2) // (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)} = 2 ^ ((n - 1) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hnm : (m + 1 - 1) = m := by omega
  rw [hnm]
  let f : {M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) // (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)} → Matrix (Fin m) (Fin m) (ZMod 2) :=
    fun M i j => M.1 i.castSucc j.castSucc
  let ext : Matrix (Fin m) (Fin m) (ZMod 2) → Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) := fun A i j =>
    if hi : i.val < m then
      if hj : j.val < m then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 1 - ∑ k : Fin m, A ⟨i.val, hi⟩ k
    else
      if hj : j.val < m then 1 - ∑ k : Fin m, A k ⟨j.val, hj⟩
      else 1 - (m : ZMod 2) + ∑ k : Fin m, ∑ l : Fin m, A k l
  have h1 : ∀ A : Matrix (Fin m) (Fin m) (ZMod 2), (∀ i, ∑ j, ext A i j = 1) ∧ (∀ j, ∑ i, ext A i j = 1) := by
    intro A
    simp only [ext]
    constructor
    intro i
    refine Fin.lastCases ?_ ?_ i
    simp only [Fin.val_last, lt_irrefl, dite_false]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dite_false]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [Fin.eta]
    rw [Finset.sum_comm]
    rw [nsmul_eq_mul, mul_one]; ring
    intro i
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta, Fin.val_last, lt_irrefl, dite_false]
    ring
    intro j
    refine Fin.lastCases ?_ ?_ j
    simp only [Fin.val_last, lt_irrefl, dite_false]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta, Fin.val_last, lt_irrefl, dite_false]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]; ring
    intro i
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta, Fin.val_last, lt_irrefl, dite_false]
    ring
  let g : Matrix (Fin m) (Fin m) (ZMod 2) → {M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) // (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)} :=
    fun A => ⟨ext A, h1 A⟩
  have h2 : ∀ A : Matrix (Fin m) (Fin m) (ZMod 2), f (g A) = A := by
    intro A
    funext i j
    simp only [f, g, ext, Fin.val_castSucc]
    rw [dif_pos i.isLt, dif_pos j.isLt]
  have h3 : ∀ M : {M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) // (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)}, g (f M) = M := by
    intro M
    apply Subtype.ext
    show ext (f M) = M.1
    funext i j
    show (if hi : i.val < m then if hj : j.val < m then f M ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 1 - ∑ k, f M ⟨i.val,hi⟩ k else if hj : j.val < m then 1 - ∑ k, f M k ⟨j.val,hj⟩ else 1 - (m:ZMod 2) + ∑ k, ∑ l, f M k l) = M.1 i j
    split_ifs with hi hj hj
    case pos => show f M ⟨i.val,hi⟩ ⟨j.val,hj⟩ = M.1 i j; show M.1 (⟨i.val,hi⟩ : Fin m).castSucc (⟨j.val,hj⟩ : Fin m).castSucc = M.1 i j; congr 1
    case neg => have hj' : j = Fin.last m := (by apply Fin.ext; rw [Fin.val_last]; omega); subst hj'; have hrow := M.2.1 i; rw [Fin.sum_univ_castSucc] at hrow; have heq : ∀ k : Fin m, f M ⟨i.val, hi⟩ k = M.1 i k.castSucc := (by intro k; show M.1 (⟨i.val,hi⟩ : Fin m).castSucc k.castSucc = M.1 i k.castSucc; congr 1); simp only [heq]; rw [eq_comm, eq_sub_iff_add_eq, add_comm]; exact hrow
    case pos => have hi' : i = Fin.last m := (by apply Fin.ext; rw [Fin.val_last]; omega); subst hi'; have hcol := M.2.2 j; rw [Fin.sum_univ_castSucc] at hcol; have heq : ∀ k : Fin m, f M k ⟨j.val, hj⟩ = M.1 k.castSucc j := (by intro k; show M.1 k.castSucc (⟨j.val,hj⟩:Fin m).castSucc = M.1 k.castSucc j; congr 1); simp only [heq]; rw [eq_comm, eq_sub_iff_add_eq, add_comm]; exact hcol
    case neg => have hi' : i = Fin.last m := (by apply Fin.ext; rw [Fin.val_last]; omega); have hj' : j = Fin.last m := (by apply Fin.ext; rw [Fin.val_last]; omega); subst hi'; subst hj'; show 1 - (m:ZMod 2) + ∑ k : Fin m, ∑ l : Fin m, M.1 k.castSucc l.castSucc = M.1 (Fin.last m) (Fin.last m); have hrowlast := M.2.1 (Fin.last m); rw [Fin.sum_univ_castSucc] at hrowlast; have hcollast := M.2.2 (Fin.last m); rw [Fin.sum_univ_castSucc] at hcollast; have hrows : ∀ i : Fin (m+1), ∑ j, M.1 i j = 1 := M.2.1; have htot : ∑ i : Fin (m+1), ∑ j : Fin (m+1), M.1 i j = ((m+1:ℕ) : ZMod 2) := (by simp [hrows]); rw [Fin.sum_univ_castSucc] at htot; simp_rw [Fin.sum_univ_castSucc] at htot; rw [Finset.sum_add_distrib] at htot; push_cast at htot; linear_combination htot - hcollast - hrowlast
  have hcard : Fintype.card {M : Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) // (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)}
      = Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) :=
    Fintype.card_congr ⟨f, g, h3, h2⟩
  rw [hcard]
  have hpi : Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) = Fintype.card (Fin m → Fin m → ZMod 2) := rfl
  rw [hpi, Fintype.card_pi]
  simp [ZMod.card, sq, pow_mul]

end Native.Competemath.P105

namespace Native.Competemath.P114

/-- competemath.com problem 114. -/
theorem kindly_zeros_sum : (Finset.Icc 1 9999999999).sum (fun n => ((Nat.digits 10 n).map (fun d => max d 1)).prod) = 42420747482776575 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, f = fun n => ((Nat.digits 10 n).map (fun d => max d 1)).prod := ⟨_, rfl⟩
  rw [← hf]
  have step : ∀ q r : ℕ, r < 10 → f (q * 10 + r) = max r 1 * f q := by
    intro q r hr
    rcases Nat.eq_zero_or_pos (q * 10 + r) with h0 | h0
    · have hq0 : q = 0 := by omega
      have hr0 : r = 0 := by omega
      subst hq0; subst hr0
      simp [hf]
    · rw [hf]
      simp only
      rw [Nat.digits_def' (by norm_num : 2 ≤ 10) h0]
      have e1 : (q * 10 + r) % 10 = r := by omega
      have e2 : (q * 10 + r) / 10 = q := by omega
      rw [e1, e2]
      simp
  have key : ∀ k : ℕ, (Finset.range (10^k)).sum f = 46^k := by
    intro k
    induction k with
    | zero => simp [hf]
    | succ k ih =>
      have bij : (Finset.range (10^(k+1))).sum f
          = ((Finset.range (10^k)) ×ˢ (Finset.range 10)).sum (fun p => f (p.1 * 10 + p.2)) := by
        apply Finset.sum_nbij' (fun n => (n / 10, n % 10)) (fun p => p.1 * 10 + p.2)
        · intro n hn
          simp only [Finset.mem_range] at hn
          simp only [Finset.mem_product, Finset.mem_range]
          constructor
          · rw [pow_succ] at hn; exact Nat.div_lt_of_lt_mul (by omega)
          · omega
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_range] at hp
          simp only [Finset.mem_range, pow_succ]
          omega
        · intro n hn
          simp only [Finset.mem_range] at hn
          omega
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_range] at hp
          ext <;> simp <;> omega
        · intro n hn
          simp only [hf]
          have heq : n / 10 * 10 + n % 10 = n := by omega
          rw [heq]
      rw [bij, Finset.sum_product]
      have inner : ∀ q ∈ Finset.range (10^k), (Finset.range 10).sum (fun r => f (q * 10 + r)) = 46 * f q := by
        intro q hq
        have heq2 : (Finset.range 10).sum (fun r => f (q * 10 + r)) = (Finset.range 10).sum (fun r => max r 1 * f q) := by
          apply Finset.sum_congr rfl
          intro r hr
          simp only [Finset.mem_range] at hr
          exact step q r hr
        rw [heq2, ← Finset.sum_mul]
        norm_num [Finset.sum_range_succ]
      rw [Finset.sum_congr rfl inner, ← Finset.mul_sum, ih, pow_succ]
      ring
  have h10 : (Finset.range (10^10)).sum f = 46^10 := key 10
  have hset : Finset.range (10^10) = insert 0 (Finset.Icc 1 9999999999) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor
    · intro h; omega
    · intro h; omega
  have hnotmem : (0:ℕ) ∉ Finset.Icc 1 9999999999 := by simp
  rw [hset, Finset.sum_insert hnotmem] at h10
  have hf0 : f 0 = 1 := by simp [hf]
  rw [hf0] at h10
  norm_num at h10
  linarith

end Native.Competemath.P114

namespace Native.Competemath.P123

/-- competemath.com problem 123. -/
theorem flea_fifty_jumps :
    ((Finset.univ : Finset (Fin 50 → Bool)).image
      (fun s => ∑ k : Fin 50, if s k then (2 : ℤ) ^ (k : ℕ) else -((2 : ℤ) ^ (k : ℕ)))).card
    = 1125899906842624 := by
  have bound : ∀ n : ℕ, ∀ s : Fin n → Bool,
      |∑ k : Fin n, if s k then (2:ℤ)^(k:ℕ) else -((2:ℤ)^(k:ℕ))| ≤ 2^n - 1 := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Fin.sum_univ_castSucc]
      have hb := ih (fun i => s (Fin.castSucc i))
      have h1 : |(if s (Fin.last n) then (2:ℤ)^n else -(2:ℤ)^n)| = 2^n := by
        split <;> simp
      have h2 := abs_add_le (∑ i : Fin n, if s (Fin.castSucc i) then (2:ℤ)^(i:ℕ) else -(2:ℤ)^(i:ℕ))
        (if s (Fin.last n) then (2:ℤ)^n else -(2:ℤ)^n)
      rw [h1] at h2
      calc |∑ i : Fin n, (if s (Fin.castSucc i) then (2:ℤ)^(i:ℕ) else -(2:ℤ)^(i:ℕ)) + (if s (Fin.last n) then (2:ℤ)^n else -(2:ℤ)^n)|
          ≤ |∑ i : Fin n, (if s (Fin.castSucc i) then (2:ℤ)^(i:ℕ) else -(2:ℤ)^(i:ℕ))| + 2^n := h2
        _ ≤ (2^n - 1) + 2^n := by linarith [hb]
        _ = 2^(n+1) - 1 := by ring
  have inj : ∀ n : ℕ, Function.Injective (fun s : Fin n → Bool =>
      ∑ k : Fin n, if s k then (2:ℤ)^(k:ℕ) else -((2:ℤ)^(k:ℕ))) := by
    intro n
    induction n with
    | zero => intro s t _; funext i; exact absurd i.2 (Nat.not_lt_zero _)
    | succ n ih =>
      intro s t h
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at h
      have hlast : s (Fin.last n) = t (Fin.last n) := by
        have hbs := bound n (fun i => s (Fin.castSucc i))
        have hbt := bound n (fun i => t (Fin.castSucc i))
        rw [abs_le] at hbs hbt
        by_contra hne
        rcases Bool.eq_false_or_eq_true (s (Fin.last n)) with hs | hs <;>
          rcases Bool.eq_false_or_eq_true (t (Fin.last n)) with ht | ht <;>
          simp only [hs, ht, if_true, if_false, Bool.false_eq_true] at h <;>
          first
            | exact hne (hs.trans ht.symm)
            | nlinarith [hbs.1, hbs.2, hbt.1, hbt.2]
      rw [hlast] at h
      have hsum : (∑ i : Fin n, if s (Fin.castSucc i) then (2:ℤ)^(i:ℕ) else -(2:ℤ)^(i:ℕ)) =
          ∑ i : Fin n, if t (Fin.castSucc i) then (2:ℤ)^(i:ℕ) else -(2:ℤ)^(i:ℕ) := by
        linarith [h]
      have hrest : (fun i => s (Fin.castSucc i)) = (fun i => t (Fin.castSucc i)) := ih hsum
      funext i
      exact Fin.lastCases hlast (fun j => congrFun hrest j) i
  have card_eq : ((Finset.univ : Finset (Fin 50 → Bool)).image
      (fun s => ∑ k : Fin 50, if s k then (2:ℤ)^(k:ℕ) else -((2:ℤ)^(k:ℕ)))).card
      = Fintype.card (Fin 50 → Bool) := by
    rw [Finset.card_image_of_injective _ (inj 50)]
    simp [Finset.card_univ]
  rw [card_eq]
  simp

end Native.Competemath.P123

namespace Native.Competemath.P109

/-- competemath.com problem 109. -/
theorem prod_mod_three_count (A B : Finset ℕ) (hA : ∀ a ∈ A, a % 3 = 2) (hB : ∀ b ∈ B, b % 3 = 1) (hAB : Disjoint A B) (hne : A.Nonempty) : ((A ∪ B).powerset.filter (fun S => (∏ p ∈ S, p) % 3 = 1)).card = 2 ^ (A.card - 1) * 2 ^ B.card := by
  have h1 : ((A ∪ B).powerset.filter (fun S => (∏ p ∈ S, p) % 3 = 1)).card = ((A ∪ B).powerset.filter (fun S => (S ∩ A).card % 2 = 0)).card := by
    congr 1
    apply Finset.filter_congr
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hunion : S = (S ∩ A) ∪ (S ∩ B) := by rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]
    have hdisj : Disjoint (S ∩ A) (S ∩ B) := (hAB.mono (Finset.inter_subset_right) (Finset.inter_subset_right))
    conv_lhs => rw [hunion, Finset.prod_union hdisj]
    have hprodA : (∏ x ∈ S ∩ A, x) % 3 = 2 ^ (S ∩ A).card % 3 := by rw [Finset.prod_nat_mod, Finset.prod_congr rfl (fun x hx => hA x (Finset.mem_inter.mp hx).2), Finset.prod_const]
    have hprodB : (∏ x ∈ S ∩ B, x) % 3 = 1 := by rw [Finset.prod_nat_mod, Finset.prod_congr rfl (fun x hx => hB x (Finset.mem_inter.mp hx).2)]; simp
    rw [Nat.mul_mod, hprodA, hprodB]
    rw [mul_one, Nat.mod_mod]
    generalize (S ∩ A).card = k
    rw [show k = 2 * (k / 2) + k % 2 from (Nat.div_add_mod k 2).symm, pow_add, pow_mul]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    case inl => simp [hk, Nat.pow_mod]
    case inr => simp [hk, Nat.mul_mod, Nat.pow_mod]
  have h2 : ((A ∪ B).powerset.filter (fun S => (S ∩ A).card % 2 = 0)).card = (A.powerset.filter (fun T => T.card % 2 = 0)).card * B.powerset.card := by
    rw [← Finset.card_product]
    apply Finset.card_bij' (fun S _ => (S ∩ A, S ∩ B)) (fun p _ => p.1 ∪ p.2)
    case hi =>
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at ha ⊢
      exact ⟨⟨Finset.inter_subset_right, ha.2⟩, Finset.inter_subset_right⟩
    case hj =>
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
      simp only [Finset.mem_filter, Finset.mem_powerset] at ha1 ha2 ⊢
      have hd : Disjoint a.2 A := hAB.symm.mono_left ha2
      have h0 : a.2 ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
      have hEq : (a.1 ∪ a.2) ∩ A = a.1 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha1.1, h0, Finset.union_empty]
      refine ⟨Finset.union_subset_union ha1.1 ha2, ?_⟩
      rw [hEq]
      exact ha1.2
    case left_inv =>
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_powerset] at ha
      show a ∩ A ∪ a ∩ B = a
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr ha.1]
    case right_inv =>
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp ha
      simp only [Finset.mem_filter, Finset.mem_powerset] at ha1 ha2
      have hd1 : Disjoint a.2 A := hAB.symm.mono_left ha2
      have h01 : a.2 ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd1
      have hd2 : Disjoint a.1 B := hAB.mono_left ha1.1
      have h02 : a.1 ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd2
      have hEq1 : (a.1 ∪ a.2) ∩ A = a.1 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha1.1, h01, Finset.union_empty]
      have hEq2 : (a.1 ∪ a.2) ∩ B = a.2 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha2, h02, Finset.empty_union]
      rw [hEq1, hEq2]
  have h3 : (A.powerset.filter (fun T => T.card % 2 = 0)).card = 2 ^ (A.card - 1) := by
    obtain ⟨a, ha⟩ := hne
    have hins : A = insert a (A.erase a) := (Finset.insert_erase ha).symm
    have hnotmem : a ∉ A.erase a := Finset.notMem_erase a A
    rw [hins, Finset.powerset_insert]
    have hcard : (insert a (A.erase a)).card = (A.erase a).card + 1 := Finset.card_insert_of_notMem hnotmem
    rw [hcard]
    rw [Nat.add_sub_cancel]
    rw [Finset.filter_union]
    have hdisj : Disjoint {T ∈ (A.erase a).powerset | T.card % 2 = 0} {T ∈ Finset.image (insert a) (A.erase a).powerset | T.card % 2 = 0} := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro T hT hT2
      rw [Finset.mem_powerset] at hT
      rw [Finset.mem_image] at hT2
      obtain ⟨S, hS, hST⟩ := hT2
      rw [← hST] at hT
      exact hnotmem (hT (Finset.mem_insert_self a S))
    rw [Finset.card_union_of_disjoint hdisj]
    rw [Finset.filter_image]
    have hinj : Set.InjOn (insert a) (↑((A.erase a).powerset) : Set (Finset ℕ)) := by
      intro S hS T hT hST
      simp only [Finset.mem_coe, Finset.mem_powerset] at hS hT
      have haS : a ∉ S := fun h => hnotmem (hS h)
      have haT : a ∉ T := fun h => hnotmem (hT h)
      have h2 := Finset.erase_insert haS
      rw [hST, Finset.erase_insert haT] at h2
      exact h2.symm
    have hsub : {a_1 ∈ (A.erase a).powerset | (insert a a_1).card % 2 = 0} ⊆ (A.erase a).powerset := Finset.filter_subset _ _
    rw [Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr hsub))]
    have hfeq : {a_1 ∈ (A.erase a).powerset | (insert a a_1).card % 2 = 0} = {a_1 ∈ (A.erase a).powerset | a_1.card % 2 = 1} := by
      apply Finset.filter_congr
      intro x hx
      rw [Finset.mem_powerset] at hx
      have hax : a ∉ x := fun h => hnotmem (hx h)
      rw [Finset.card_insert_of_notMem hax]
      omega
    rw [hfeq]
    have hcombine : {T ∈ (A.erase a).powerset | T.card % 2 = 0}.card + {a_1 ∈ (A.erase a).powerset | a_1.card % 2 = 1}.card = (A.erase a).powerset.card := by
      rw [← Finset.card_filter_add_card_filter_not (s := (A.erase a).powerset) (p := fun T => T.card % 2 = 0)]
      have heq2 : {a_1 ∈ (A.erase a).powerset | a_1.card % 2 = 1} = {a ∈ (A.erase a).powerset | ¬a.card % 2 = 0} :=
        Finset.filter_congr (fun x _ => by omega)
      rw [heq2]
    rw [hcombine, Finset.card_powerset]
  rw [h1, h2, h3, Finset.card_powerset]

end Native.Competemath.P109

namespace Native.Competemath.P134

/-- competemath.com problem 134. -/
theorem zeckendorf_digit_sum_T30 (T : ℕ → ℕ)
    (h0 : T 0 = 0) (h1 : T 1 = 1)
    (hrec : ∀ m, T (m + 2) = T (m + 1) + Nat.fib (m + 2) + T m) :
    T 30 = 18394910 := by
  have hA : T 9 = 235 ∧ T 10 = 420 := by
    have e0 := hrec 0
    have e1 := hrec 1
    have e2 := hrec 2
    have e3 := hrec 3
    have e4 := hrec 4
    have e5 := hrec 5
    have e6 := hrec 6
    have e7 := hrec 7
    have e8 := hrec 8
    norm_num [Nat.fib] at e0 e1 e2 e3 e4 e5 e6 e7 e8
    omega
  have hB : T 19 = 59155 ∧ T 20 = 100610 := by
    obtain ⟨hA9, hA10⟩ := hA
    have e11 := hrec 9
    have e12 := hrec 10
    have e13 := hrec 11
    have e14 := hrec 12
    have e15 := hrec 13
    have e16 := hrec 14
    have e17 := hrec 15
    have e18 := hrec 16
    have e19 := hrec 17
    have e20 := hrec 18
    norm_num [Nat.fib] at e11 e12 e13 e14 e15 e16 e17 e18 e19 e20
    omega
  have hC : T 29 = 10996580 ∧ T 30 = 18394910 := by
    obtain ⟨hB19, hB20⟩ := hB
    have e21 := hrec 19
    have e22 := hrec 20
    have e23 := hrec 21
    have e24 := hrec 22
    have e25 := hrec 23
    have e26 := hrec 24
    have e27 := hrec 25
    have e28 := hrec 26
    have e29 := hrec 27
    have e30 := hrec 28
    norm_num at e21 e22 e23 e24 e25 e26 e27 e28 e29 e30
    omega
  exact hC.2

end Native.Competemath.P134

namespace Native.Competemath.P136

open Nat in
/-- competemath.com problem 136. -/
theorem peak_start_sum_dvd_prime (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ ∑ i ∈ Finset.Icc 1 (p - 1), (p - 1)! / i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((∑ i ∈ Finset.Icc 1 (p - 1), (p - 1)! / i : ℕ) : ZMod p)
      = ((p - 1)! : ZMod p) * ∑ i ∈ Finset.Icc 1 (p - 1), (i : ZMod p)⁻¹ := by
        rw [Nat.cast_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_Icc] at hi
        have hdvd : i ∣ (p - 1)! := Nat.dvd_factorial hi.1 hi.2
        have hip : (i : ZMod p) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
          intro hcontra
          have hle := Nat.le_of_dvd (by omega) hcontra
          omega
        rw [Nat.cast_div hdvd hip, div_eq_mul_inv]
  have h2 : ∑ i ∈ Finset.Icc 1 (p - 1), (i : ZMod p)⁻¹ = 0 := by
    apply Finset.sum_involution (fun i _ => p - i)
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
      have hcast : ((p - a : ℕ) : ZMod p) = -(a : ZMod p) := by
        have hale : a ≤ p := le_trans ha2 (Nat.sub_le p 1)
        push_cast [Nat.cast_sub hale]
        simp
      rw [hcast, inv_neg, add_neg_cancel]
    · intro a ha _
      obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
      obtain ⟨k, hk⟩ := (hp.eq_two_or_odd').resolve_left hodd
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; omega
  have key : ((∑ i ∈ Finset.Icc 1 (p - 1), (p - 1)! / i : ℕ) : ZMod p) = 0 := by
    rw [h1, h2, mul_zero]
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp key

end Native.Competemath.P136

namespace Native.Competemath.P184

/-- competemath.com problem 184. -/
theorem order_squared_count :
    (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = orderOf (a ^ 2))).card = 1013 := by
  have h1 : ∀ a : (ZMod 2027)ˣ, orderOf a = orderOf (a ^ 2) ↔ Odd (orderOf a) := by
    intro a
    rw [orderOf_pow]
    have hpos := orderOf_pos a
    rcases Nat.even_or_odd (orderOf a) with he | ho
    · obtain ⟨k, hk⟩ := he
      have h2dvdn : (2:ℕ) ∣ orderOf a := ⟨k, by omega⟩
      have hgcd2 : Nat.gcd (orderOf a) 2 = 2 := by
        have hd1 : (2:ℕ) ∣ Nat.gcd (orderOf a) 2 := Nat.dvd_gcd h2dvdn (dvd_refl 2)
        have hd2 : Nat.gcd (orderOf a) 2 ∣ 2 := Nat.gcd_dvd_right _ _
        exact Nat.dvd_antisymm hd2 hd1
      constructor
      · intro heq
        exfalso
        rw [hgcd2] at heq
        omega
      · intro hodd
        exfalso
        rcases hodd with ⟨m, hm⟩
        omega
    · have hgcd1 : Nat.gcd (orderOf a) 2 = 1 := by
        rcases ho with ⟨m, hm⟩
        have hnd : ¬ (2:ℕ) ∣ orderOf a := by omega
        have hd2 : Nat.gcd (orderOf a) 2 ∣ 2 := Nat.gcd_dvd_right _ _
        have hd1 : Nat.gcd (orderOf a) 2 ∣ orderOf a := Nat.gcd_dvd_left _ _
        rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc1 | hc2
        · exact hc1
        · exfalso; apply hnd; rw [← hc2]; exact hd1
      constructor
      · intro _; exact ho
      · intro _; rw [hgcd1]; simp
  have h2 : (Finset.univ.filter (fun a : (ZMod 2027)ˣ => Odd (orderOf a))).card = 1013 := by
    haveI hp : Fact (Nat.Prime 2027) := ⟨by norm_num⟩
    have hcard : Fintype.card (ZMod 2027)ˣ = 2026 := by
      simp [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : Nat.Prime 2027)]
    have hodd_iff : ∀ d : ℕ, d ∣ 2026 → (Odd d ↔ d ∣ 1013) := by
      intro d hd
      rw [Nat.odd_iff]
      constructor
      · intro hodd
        have h2 : ¬ (2 ∣ d) := by omega
        have hcop : Nat.Coprime d 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2 |>.symm
        have h2026 : (2026:ℕ) = 2 * 1013 := by norm_num
        rw [h2026] at hd
        exact hcop.dvd_of_dvd_mul_left hd
      · intro hdvd
        by_contra hne
        have h2d : (2:ℕ) ∣ d := by omega
        have : (2:ℕ) ∣ 1013 := h2d.trans hdvd
        norm_num at this
    have hset : Finset.univ.filter (fun a : (ZMod 2027)ˣ => Odd (orderOf a))
        = Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1)
          ∪ Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1013) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      have hdvd : orderOf a ∣ 2026 := hcard ▸ orderOf_dvd_card
      rw [hodd_iff (orderOf a) hdvd]
      constructor
      · intro h
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 1013)).mp h with h1 | h2
        · left; exact h1
        · right; exact h2
      · rintro (h1 | h2)
        · rw [h1]; exact one_dvd _
        · rw [h2]
    have hdisj : Disjoint (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1))
        (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1013)) := by
      rw [Finset.disjoint_filter]
      intro a _ ha1 ha1013
      rw [ha1] at ha1013
      norm_num at ha1013
    rw [hset, Finset.card_union_of_disjoint hdisj]
    have hc1 : (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1)).card = Nat.totient 1 :=
      IsCyclic.card_orderOf_eq_totient (one_dvd _)
    have hc2 : (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = 1013)).card = Nat.totient 1013 :=
      IsCyclic.card_orderOf_eq_totient (by rw [hcard]; norm_num)
    rw [hc1, hc2]
    simp [Nat.totient_one, Nat.totient_prime (by norm_num : Nat.Prime 1013)]
  have heq : (Finset.univ.filter (fun a : (ZMod 2027)ˣ => orderOf a = orderOf (a ^ 2)))
      = (Finset.univ.filter (fun a : (ZMod 2027)ˣ => Odd (orderOf a))) :=
    Finset.filter_congr (fun a _ => h1 a)
  rw [heq, h2]

end Native.Competemath.P184

namespace Native.Competemath.P251

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 251. -/
theorem last_token : (∏ k ∈ Finset.Icc (1:ℕ) 7, (k + 1)) - 1 = 40319 :=
  by
    change (∏ k ∈ Finset.Ico 1 8, (k + 1)) - 1 = 40319
    simp only [Finset.prod_Ico_eq_prod_range]
    norm_num

end Native.Competemath.P251

namespace Native.Competemath.P253

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
open Finset

/-- competemath.com problem 253. -/
lemma self_balancing_count_as_sum :
  ((Icc 1 12).powerset.filter (fun S => ∃ m ∈ S, (∀ x ∈ S, x ≤ m) ∧ 2 * m = S.sum id)).card =
    ∑ m ∈ Icc 1 12, {T ∈ (Icc 1 (m-1)).powerset | T.sum id = m}.card :=
  by
    -- Every self-balancing S has a unique maximum m, and the remainder T = S \ {m}
    -- lies in the power set of {1..m-1} and sums to m.
    -- Hence the displayed sum counts exactly the sets that pass the filter.
    rfl

theorem self_balancing_count : ((Finset.Icc 1 12).powerset.filter (fun S => ∃ m ∈ S, (∀ x ∈ S, x ≤ m) ∧ 2 * m = S.sum id)).card = 57 :=
  by
    rw [self_balancing_count_as_sum]
    decide

end Native.Competemath.P253

namespace Native.Competemath.P255

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 255. -/
theorem scribe_factorial_sum : (Finset.range 9).sum (fun k => k * k.factorial) = 362879 :=
  by
    norm_num

end Native.Competemath.P255

namespace Native.Competemath.P262

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-- competemath.com problem 262. -/
lemma sum_recurrence (n : ℕ) :
  ∑ k ∈ Finset.Icc 1 (n+1), (-1 : ℤ) ^ ((n+1) - k : ℕ) * (k : ℤ) ^ (2 : ℕ)
  = - (∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (n - k : ℕ) * (k : ℤ) ^ (2 : ℕ)) + ((n+1 : ℕ) : ℤ) ^ (2 : ℕ) :=
  by
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
    simp only [Nat.sub_self, pow_zero, one_mul]
    have h : ∀ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ ((n + 1) - k) * (k : ℤ) ^ 2 = - ((-1 : ℤ) ^ (n - k) * (k : ℤ) ^ 2) := by
      intro k hk
      have : (n + 1 - k) = n - k + 1 := by
        rw [Finset.mem_Icc] at hk
        omega
      rw [this, pow_add, pow_one]
      ring
    rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]

lemma inductive_step (n : ℕ)
    (h : 2 * (∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (n - k : ℕ) * (k : ℤ) ^ (2 : ℕ)) = (n : ℤ) * (n + 1)) :
    2 * (∑ k ∈ Finset.Icc 1 (n+1), (-1 : ℤ) ^ (((n+1) - k) : ℕ) * (k : ℤ) ^ (2 : ℕ))
    = ((n+1 : ℕ) : ℤ) * ((n+1 : ℕ) + 1) :=
  by
    rw [sum_recurrence]
    rw [mul_add, mul_neg, h]
    ring_nf
    simp [Nat.cast_add, Nat.cast_one]
    ring

lemma base_case :
  2 * (∑ k ∈ Finset.Icc 1 0, (-1 : ℤ) ^ (0 - k : ℕ) * (k : ℤ) ^ (2 : ℕ)) = (0 : ℤ) * (0 + 1) :=
  by
    simp [Finset.Icc_eq_empty]

theorem alt_square_sum_eq (n : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (n - k) * (k : ℤ) ^ 2) = (n : ℤ) * (n + 1) :=
  by
    induction n with
    | zero => exact base_case
    | succ n ih => exact inductive_step n ih

end Native.Competemath.P262

namespace Native.Competemath.P233

/-- competemath.com problem 233. -/
theorem beetle_final_station :
    (∑ i ∈ Finset.Icc 1 50, i) % 12 = 3 := by decide

end Native.Competemath.P233

namespace Native.Competemath.P244

def tileCount3xn : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | (n+2) => 4 * tileCount3xn (n+1) - tileCount3xn n

/-- competemath.com problem 244. -/
theorem tileCount3xn_sixteen : tileCount3xn 8 = 29681 := by decide

end Native.Competemath.P244

namespace Native.Competemath.P95

/-- competemath.com problem 95. -/
theorem merry_go_round : (Finset.Icc 18 60).filter (fun n => n % 2 = 0 ∧ 5 + n / 2 = 17) = {24} := by decide

end Native.Competemath.P95

namespace Native.Competemath.P117

/-- competemath.com problem 117. -/
theorem quadrillion_heaps : ((Finset.Icc 1 (10^15)).filter (fun a => a ^^^ (10^15) < a)).card = 437050046578689 := by
  have h1 : ∀ a ∈ Finset.Icc 1 (10^15 : ℕ), (a ^^^ (10^15) < a) ↔ (2^49 ≤ a) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, ha2⟩ := ha
    have hN50 : (10^15:ℕ) < 2^50 := by norm_num
    have h2 : a < 2^50 := lt_of_le_of_lt ha2 hN50
    have hN49 : (10^15:ℕ).testBit 49 = true := by decide
    have hj2 : ∀ j, 49 < j → a.testBit j = false ∧ (10^15:ℕ).testBit j = false := by
      intro j hj
      have hj50 : 50 ≤ j := by omega
      exact ⟨Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) hj50)), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hN50 (Nat.pow_le_pow_right (by norm_num) hj50))⟩
    constructor
    · intro hlt
      by_contra hcon
      have hcon2 : a < 2^49 := by omega
      have hb : a.testBit 49 = false := Nat.testBit_eq_false_of_lt hcon2
      have hxor49 : (a ^^^ (10^15:ℕ)).testBit 49 = true := by
        rw [Nat.testBit_xor, hb, hN49]; rfl
      have hagree : ∀ j, 49 < j → a.testBit j = (a ^^^ (10^15:ℕ)).testBit j := by
        intro j hj
        rw [Nat.testBit_xor, (hj2 j hj).1, (hj2 j hj).2]; rfl
      have hcontra : a < a ^^^ (10^15:ℕ) := Nat.lt_of_testBit 49 hb hxor49 hagree
      omega
    · intro hge
      have hb : a.testBit 49 = true := by
        rw [Nat.testBit]
        simp [Nat.shiftRight_eq_div_pow]
        omega
      have hxor49 : (a ^^^ (10^15:ℕ)).testBit 49 = false := by
        rw [Nat.testBit_xor, hb, hN49]; rfl
      have hagree : ∀ j, 49 < j → (a ^^^ (10^15:ℕ)).testBit j = a.testBit j := by
        intro j hj
        rw [Nat.testBit_xor, (hj2 j hj).1, (hj2 j hj).2]; rfl
      exact Nat.lt_of_testBit 49 hxor49 hb hagree
  have h2 : (Finset.Icc 1 (10^15 : ℕ)).filter (fun a => a ^^^ (10^15) < a) = Finset.Icc (2^49) (10^15) := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, ha3⟩
      exact ⟨(h1 a (Finset.mem_Icc.mpr ⟨ha1, ha2⟩)).mp ha3, ha2⟩
    · rintro ⟨ha1, ha2⟩
      have ha0 : (1:ℕ) ≤ a := le_trans (by norm_num) ha1
      exact ⟨⟨ha0, ha2⟩, (h1 a (Finset.mem_Icc.mpr ⟨ha0, ha2⟩)).mpr ha1⟩
  rw [h2]
  have h3 : (Finset.Icc (2^49 : ℕ) (10^15)).card = 437050046578689 := by
    rw [Nat.card_Icc]
    norm_num
  exact h3

end Native.Competemath.P117

namespace Native.Competemath.P120

/-- competemath.com problem 120. -/
theorem pirates_piles : (17 % 5 = 2 ∧ 17 % 3 = 2 ∧ 10 < 17) ∧ ∀ n ∈ Finset.range 17, ¬(10 < n ∧ n % 5 = 2 ∧ n % 3 = 2) := by decide

end Native.Competemath.P120

namespace Native.Competemath.P17

/-- competemath.com problem 17. -/
theorem equitable_binary_matrices : (Finset.univ.filter (fun M : Fin 3 → Fin 3 → Fin 2 => ∀ i j : Fin 3, Finset.univ.sum (fun k : Fin 3 => (M i k).val) = Finset.univ.sum (fun k : Fin 3 => (M k j).val))).card = 14 := by decide

end Native.Competemath.P17

namespace Native.Competemath.P29

/-- competemath.com problem 29. -/
theorem level_return : (Finset.univ.filter (fun s : Fin 8 → Bool => s 0 = s 7)).card = 128 := by decide

end Native.Competemath.P29

namespace Native.Competemath.P43

/-- competemath.com problem 43. -/
theorem parity_parallelism :
  (Finset.univ.filter (fun p : Fin 12 × Fin 12 =>
    p.1.val < p.2.val ∧ (p.1.val + p.2.val) % 2 = 1)).card = 36 := by
  decide

end Native.Competemath.P43

namespace Native.Competemath.P48

/-- competemath.com problem 48. -/
theorem cubic_matrix_count :
  (Finset.univ.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod 5) => M ^ 3 = 1)).card = 21 := by
  decide

end Native.Competemath.P48

namespace Native.Competemath.P65

/-- competemath.com problem 65. -/
theorem doubly_balanced_count : (Finset.powersetCard 6 (Finset.Icc 1 12) |>.filter (fun S => S.sum id = 39)).card = 58 := by
  decide

end Native.Competemath.P65

namespace Native.Competemath.P101

/-- competemath.com problem 101. -/
theorem paper_snipper : (Finset.range 30).filter (fun k => 1 + 2 * k = 21) = {10} := by decide

end Native.Competemath.P101

namespace Native.Competemath.P126

/-- competemath.com problem 126. -/
theorem staircase_sums_ten_pow_36 : Nat.card {p : ℕ × ℕ | 0 < p.1 ∧ 2 ≤ p.2 ∧ p.2 * (2 * p.1 + p.2 - 1) = 2 * 10 ^ 36} = 36 := by
  set fA : ℕ → ℕ × ℕ := fun j => ((2 ^ 37 * 5 ^ (36 - j) - 5 ^ j + 1) / 2, 5 ^ j) with hfA
  set fB : ℕ → ℕ × ℕ := fun j => ((5 ^ j - 2 ^ 37 * 5 ^ (36 - j) + 1) / 2, 2 ^ 37 * 5 ^ (36 - j)) with hfB
  set FA : Finset (ℕ × ℕ) := (Finset.Icc 1 25).image fA with hFA
  set FB : Finset (ℕ × ℕ) := (Finset.Icc 26 36).image fB with hFB
  have h1 : ∀ k m : ℕ, k * m = 2 ^ 37 * 5 ^ 36 → (Odd k ∨ Odd m) → ∃ j ≤ 36, (k = 5 ^ j ∧ m = 2 ^ 37 * 5 ^ (36 - j)) ∨ (k = 2 ^ 37 * 5 ^ (36 - j) ∧ m = 5 ^ j) := by
    intro k m hkm hodd
    have hkm' : k * m = 5 ^ 36 * 2 ^ 37 := by rw [hkm]; ring
    obtain ⟨i, j, b, c, hij, hbc, hkb, hmc⟩ := mul_eq_mul_prime_pow Nat.prime_two.prime hkm'
    obtain ⟨i2, j2, b2, c2, hij2, hbc2, hbb2, hcc2⟩ := mul_eq_mul_prime_pow Nat.prime_five.prime (show b * c = 1 * 5 ^ 36 by rw [← hbc, one_mul])
    have hb2 : b2 = 1 := Nat.eq_one_of_mul_eq_one_right hbc2.symm
    have hc2 : c2 = 1 := Nat.eq_one_of_mul_eq_one_left hbc2.symm
    subst hb2; subst hc2; simp only [one_mul] at hbb2 hcc2
    rw [hbb2] at hkb; rw [hcc2] at hmc
    rcases hodd with hoddk | hoddm
    have hi0 : i = 0 := by
      by_contra hi
      have hek : Even k := by
        rw [hkb]
        exact Even.mul_left (Nat.even_pow.mpr ⟨even_two, hi⟩) _
      exact (Nat.not_even_iff_odd.mpr hoddk) hek
    refine ⟨i2, by omega, Or.inl ⟨by rw [hkb, hi0, pow_zero, mul_one], ?_⟩⟩
    have hj37 : j = 37 := by omega
    have hsub : 36 - i2 = j2 := by omega
    rw [hmc, hj37, hsub, mul_comm]
    have hj0 : j = 0 := by
      by_contra hj
      have hem : Even m := by
        rw [hmc]
        exact Even.mul_left (Nat.even_pow.mpr ⟨even_two, hj⟩) _
      exact (Nat.not_even_iff_odd.mpr hoddm) hem
    have hi37 : i = 37 := by omega
    have hsub2 : 36 - j2 = i2 := by omega
    exact ⟨j2, by omega, Or.inr ⟨by rw [hkb, hi37, hsub2, mul_comm], by rw [hmc, hj0, pow_zero, mul_one]⟩⟩
  have h2 : {p : ℕ × ℕ | 0 < p.1 ∧ 2 ≤ p.2 ∧ p.2 * (2 * p.1 + p.2 - 1) = 2 * 10 ^ 36} ⊆ (↑FA ∪ ↑FB : Set (ℕ × ℕ)) := by
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    have hkm : p.2 * (2 * p.1 + p.2 - 1) = 2 ^ 37 * 5 ^ 36 := by
      rw [hp3]; norm_num [show (10:ℕ) = 2 * 5 from rfl, mul_pow]
    have hpar : Odd p.2 ∨ Odd (2 * p.1 + p.2 - 1) := by
      rcases Nat.even_or_odd p.2 with he | ho
      · right
        rw [Nat.odd_iff]
        rw [Nat.even_iff] at he
        omega
      · left
        exact ho
    obtain ⟨j, hj36, hcase⟩ := h1 p.2 (2 * p.1 + p.2 - 1) hkm hpar
    rcases hcase with ⟨hp2eq, hkeq⟩ | ⟨hp2eq, hkeq⟩
    · have hA : (2:ℕ) ^ 37 * 5 ^ 10 < 5 ^ 26 := by norm_num
      have hj25 : j ≤ 25 := by
        by_contra hcon
        have hle1 : (5:ℕ) ^ (36 - j) ≤ 5 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle2 : (5:ℕ) ^ 26 ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle3 : (2:ℕ) ^ 37 * 5 ^ (36 - j) ≤ 2 ^ 37 * 5 ^ 10 := Nat.mul_le_mul_left _ hle1
        omega
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · exfalso
          rw [h0] at hp2eq
          norm_num at hp2eq
          omega
        · exact h0
      have hmem : j ∈ Finset.Icc 1 25 := Finset.mem_Icc.mpr ⟨hj1, hj25⟩
      have hp1eq : p.1 = (2 ^ 37 * 5 ^ (36 - j) - 5 ^ j + 1) / 2 := by omega
      apply Set.mem_union_left
      rw [Finset.mem_coe, hFA]
      refine Finset.mem_image.mpr ⟨j, hmem, ?_⟩
      simp only [hfA]
      rw [← hp1eq, ← hp2eq]
    · have hB : (5:ℕ) ^ 25 < 2 ^ 37 * 5 ^ 11 := by norm_num
      have hj26 : 26 ≤ j := by
        by_contra hcon
        have hle1 : (5:ℕ) ^ 11 ≤ 5 ^ (36 - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle2 : (5:ℕ) ^ j ≤ 5 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hle3 : (2:ℕ) ^ 37 * 5 ^ 11 ≤ 2 ^ 37 * 5 ^ (36 - j) := Nat.mul_le_mul_left _ hle1
        omega
      have hmem : j ∈ Finset.Icc 26 36 := Finset.mem_Icc.mpr ⟨hj26, hj36⟩
      have hp1eq : p.1 = (5 ^ j - 2 ^ 37 * 5 ^ (36 - j) + 1) / 2 := by omega
      apply Set.mem_union_right
      rw [Finset.mem_coe, hFB]
      refine Finset.mem_image.mpr ⟨j, hmem, ?_⟩
      simp only [hfB]
      rw [← hp1eq, ← hp2eq]
  have h3 : (↑FA ∪ ↑FB : Set (ℕ × ℕ)) ⊆ {p : ℕ × ℕ | 0 < p.1 ∧ 2 ≤ p.2 ∧ p.2 * (2 * p.1 + p.2 - 1) = 2 * 10 ^ 36} := by
    intro p hp
    rw [Set.mem_union, Finset.mem_coe, Finset.mem_coe, hFA, hFB, Finset.mem_image, Finset.mem_image] at hp
    rcases hp with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [Finset.mem_Icc] at hj
      obtain ⟨hj1, hj2⟩ := hj
      simp only [hfA]
      interval_cases j <;> norm_num
    · rw [Finset.mem_Icc] at hj
      obtain ⟨hj1, hj2⟩ := hj
      simp only [hfB]
      interval_cases j <;> norm_num
  have h4 : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_image] at hxA hxB
    obtain ⟨j, hj, hjeq⟩ := hxA
    obtain ⟨k, hk, hkeq⟩ := hxB
    have hsecond : (5:ℕ) ^ j = 2 ^ 37 * 5 ^ (36 - k) := by have := congrArg Prod.snd (hjeq.trans hkeq.symm); simpa using this
    have hodd : Odd ((5:ℕ) ^ j) := Odd.pow (by decide)
    rw [hsecond] at hodd
    simp [Nat.odd_mul] at hodd
    exact absurd hodd.1 (by decide)
  have h5 : FA.card = 25 := by
    rw [hFA]
    rw [Finset.card_image_of_injective _ (fun j k h => Nat.pow_right_injective (by norm_num) (congrArg Prod.snd h))]
    simp
  have h6 : FB.card = 11 := by
    rw [hFB, Finset.card_image_of_injOn, Nat.card_Icc]
    intro x hx y hy hxy
    simp only [hfB, Prod.mk.injEq] at hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    have h5 : (5:ℕ) ^ (36 - x) = 5 ^ (36 - y) := Nat.eq_of_mul_eq_mul_left (by positivity) hxy.2
    have h36 : 36 - x = 36 - y := Nat.pow_right_injective (by norm_num) h5
    omega
  have hSet : {p : ℕ × ℕ | 0 < p.1 ∧ 2 ≤ p.2 ∧ p.2 * (2 * p.1 + p.2 - 1) = 2 * 10 ^ 36} = (↑FA ∪ ↑FB : Set (ℕ × ℕ)) :=
    Set.Subset.antisymm h2 h3
  rw [hSet, ← Finset.coe_union]
  simp [Finset.card_union_of_disjoint h4, h5, h6]

end Native.Competemath.P126

namespace Native.Competemath.P68

/-- competemath.com problem 68. -/
theorem perm_pow_fixed_sum (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) : ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i : Fin n => (σ ^ k) i = i)).card = n.factorial * (Nat.divisors k).card := by
  have hn : 0 < n := Nat.lt_of_lt_of_le hk hkn
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  have h1 : ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i : Fin n => (σ ^ k) i = i)).card
      = ∑ i : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i = i)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
  have h2 : ∀ i : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i = i)).card
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i0 = i0)).card := by
        intro i
        set τ : Equiv.Perm (Fin n) := Equiv.swap i0 i with hτdef
        have hττ : τ * τ = 1 := by
          simp [hτdef, Equiv.swap_mul_self]
        have hτinv : τ⁻¹ = τ := by
          rw [eq_comm, eq_inv_iff_mul_eq_one]
          exact hττ
        have hτi0 : τ i0 = i := Equiv.swap_apply_left i0 i
        have hτi : τ i = i0 := Equiv.swap_apply_right i0 i
        have hround : ∀ σ : Equiv.Perm (Fin n), τ * (τ * σ * τ⁻¹) * τ⁻¹ = σ := by
          intro σ
          rw [hτinv]
          have assoc1 : τ * (τ * σ * τ) * τ = τ * τ * σ * (τ * τ) := by simp [mul_assoc]
          rw [assoc1, hττ, one_mul, mul_one]
        apply Finset.card_bij' (fun σ (_ : σ ∈ _) => τ * σ * τ⁻¹) (fun σ (_ : σ ∈ _) => τ * σ * τ⁻¹)
        · intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          rw [conj_pow]
          simp only [Equiv.Perm.mul_apply]
          rw [hτinv, hτi0, hσ, hτi]
        · intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          rw [conj_pow]
          simp only [Equiv.Perm.mul_apply]
          rw [hτinv, hτi, hσ, hτi0]
        · intro σ hσ
          exact hround σ
        · intro σ hσ
          exact hround σ
  have h3 : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i0 = i0)).card
      = (n - 1).factorial * (Nat.divisors k).card := by
    have hpos : ∀ {m:ℕ} (f: Equiv.Perm (Fin m)) (x:Fin m), 0 < Function.minimalPeriod (⇑f) x := by
      intro m f x
      apply Function.minimalPeriod_pos_of_mem_periodicPts
      refine ⟨orderOf f, orderOf_pos f, ?_⟩
      show (⇑f)^[orderOf f] x = x
      rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl
    have hswap_indep : ∀ (m:ℕ) (a b : Fin m) (ℓ:ℕ),
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Function.minimalPeriod (⇑σ) a = ℓ)).card
        = (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Function.minimalPeriod (⇑σ) b = ℓ)).card := by
      intro m a b ℓ
      set τ : Equiv.Perm (Fin m) := Equiv.swap a b with hτdef
      have hττ : τ * τ = 1 := by simp [hτdef, Equiv.swap_mul_self]
      have hτinv : τ⁻¹ = τ := by rw [eq_comm, eq_inv_iff_mul_eq_one]; exact hττ
      have hτa : τ a = b := Equiv.swap_apply_left a b
      have hτb : τ b = a := Equiv.swap_apply_right a b
      have hτinvol : ∀ y : Fin m, τ (τ y) = y := by
        intro y
        have hy : (τ * τ) y = y := by rw [hττ]; rfl
        simpa [Equiv.Perm.mul_apply] using hy
      have hround : ∀ σ : Equiv.Perm (Fin m), τ * (τ * σ * τ⁻¹) * τ⁻¹ = σ := by
        intro σ
        rw [hτinv]
        have assoc1 : τ * (τ * σ * τ) * τ = τ * τ * σ * (τ * τ) := by simp [mul_assoc]
        rw [assoc1, hττ, one_mul, mul_one]
      have hmp_eq : ∀ (σ : Equiv.Perm (Fin m)) (x : Fin m),
          Function.minimalPeriod (⇑σ) x = Function.minimalPeriod (⇑(τ*σ*τ⁻¹)) (τ x) := by
        intro σ x
        have hiter : ∀ j:ℕ, (⇑(τ*σ*τ⁻¹))^[j] (τ x) = τ ((⇑σ)^[j] x) := by
          intro j
          induction j with
          | zero => simp
          | succ j ih =>
              rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
              simp only [Equiv.Perm.mul_apply, hτinv]
              rw [hτinvol]
        have hiff : ∀ j:ℕ, Function.IsPeriodicPt (⇑σ) j x ↔ Function.IsPeriodicPt (⇑(τ*σ*τ⁻¹)) j (τ x) := by
          intro j
          constructor
          · intro hj
            show (⇑(τ*σ*τ⁻¹))^[j] (τ x) = τ x
            rw [hiter, hj]
          · intro hj
            have hj' : (⇑(τ*σ*τ⁻¹))^[j] (τ x) = τ x := hj
            rw [hiter] at hj'
            exact τ.injective hj'
        have hd1 : Function.minimalPeriod (⇑σ) x ∣ Function.minimalPeriod (⇑(τ*σ*τ⁻¹)) (τ x) := by
          have hp := (hiff (Function.minimalPeriod (⇑(τ*σ*τ⁻¹)) (τ x))).2 (Function.isPeriodicPt_minimalPeriod _ _)
          exact hp.minimalPeriod_dvd
        have hd2 : Function.minimalPeriod (⇑(τ*σ*τ⁻¹)) (τ x) ∣ Function.minimalPeriod (⇑σ) x := by
          have hp := (hiff (Function.minimalPeriod (⇑σ) x)).1 (Function.isPeriodicPt_minimalPeriod _ _)
          exact hp.minimalPeriod_dvd
        exact Nat.dvd_antisymm hd1 hd2
      apply Finset.card_bij' (fun σ (_ : σ ∈ _) => τ * σ * τ⁻¹) (fun σ (_ : σ ∈ _) => τ * σ * τ⁻¹)
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        have heq := hmp_eq σ a
        rw [hτa] at heq
        rw [← heq]; exact hσ
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        have heq := hmp_eq σ b
        rw [hτb] at heq
        rw [← heq]; exact hσ
      · intro σ hσ; exact hround σ
      · intro σ hσ; exact hround σ
    have hkey : ∀ (m:ℕ) (e : Equiv.Perm (Fin m)) (q : Fin m),
        Function.minimalPeriod (⇑(Equiv.Perm.decomposeFin.symm (q.succ, e))) (0:Fin (m+1))
        = Function.minimalPeriod (⇑e) q + 1 := by
      intro m e q
      set σ : Equiv.Perm (Fin (m+1)) := Equiv.Perm.decomposeFin.symm (q.succ, e) with hσdef
      set P := Function.minimalPeriod (⇑e) q with hPdef
      have hPpos : 0 < P := hpos e q
      have hstep : ∀ r : ℕ, r < P →
          (⇑σ)^[r+1] (0 : Fin (m+1)) = ((⇑e)^[r] q).succ := by
        intro r
        induction r with
        | zero =>
            intro _
            show σ 0 = q.succ
            rw [hσdef, Equiv.Perm.decomposeFin_symm_apply_zero]
        | succ r ih =>
            intro hr
            have hr' : r < P := by omega
            have step_r := ih hr'
            have hne : (⇑e) ((⇑e)^[r] q) ≠ q := by
              intro hcontra
              have hp : Function.IsPeriodicPt (⇑e) (r+1) q := by
                show (⇑e)^[r+1] q = q
                rw [Function.iterate_succ_apply']
                exact hcontra
              have := hp.minimalPeriod_le (Nat.succ_pos r)
              omega
            rw [Function.iterate_succ_apply', step_r, hσdef, Equiv.Perm.decomposeFin_symm_apply_succ e q.succ ((⇑e)^[r] q)]
            rw [Function.iterate_succ_apply' (⇑e) r q]
            rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_injective m |>.ne hne)]
      have hPeriodic : (⇑σ)^[P+1] (0 : Fin (m+1)) = 0 := by
        have hlast := hstep (P-1) (by omega)
        have hPsucc : P - 1 + 1 = P := by omega
        rw [hPsucc] at hlast
        have hiter : (⇑σ)^[P+1] (0:Fin (m+1)) = (⇑σ) ((⇑σ)^[P] 0) := Function.iterate_succ_apply' _ _ _
        rw [hiter, hlast, hσdef, Equiv.Perm.decomposeFin_symm_apply_succ e q.succ ((⇑e)^[P-1] q)]
        have heq : (⇑e) ((⇑e)^[P-1] q) = (⇑e)^[P] q := by
          conv_rhs => rw [show P = (P - 1) + 1 from by omega]
          rw [Function.iterate_succ_apply']
        have hqfix : (⇑e)^[P] q = q := Function.isPeriodicPt_minimalPeriod (⇑e) q
        rw [heq, hqfix, Equiv.swap_apply_right]
      have hne_before : ∀ j : ℕ, 0 < j → j ≤ P → (⇑σ)^[j] (0 : Fin (m+1)) ≠ 0 := by
        intro j hj0 hjP
        have hj := hstep (j-1) (by omega)
        have hjsucc : j - 1 + 1 = j := by omega
        rw [hjsucc] at hj
        rw [hj]
        exact Fin.succ_ne_zero _
      have hle : Function.minimalPeriod (⇑σ) (0 : Fin (m+1)) ≤ P + 1 :=
        Function.IsPeriodicPt.minimalPeriod_le (by omega) hPeriodic
      have hge : P + 1 ≤ Function.minimalPeriod (⇑σ) (0 : Fin (m+1)) := by
        by_contra hcon
        simp only [not_le] at hcon
        have hσpos : 0 < Function.minimalPeriod (⇑σ) (0 : Fin (m+1)) := hpos σ 0
        have hcontra2 := hne_before (Function.minimalPeriod (⇑σ) (0 : Fin (m+1))) hσpos (by omega)
        exact hcontra2 (Function.isPeriodicPt_minimalPeriod (⇑σ) 0)
      omega
    have hcase1 : ∀ m:ℕ, (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = 1)).card = m.factorial := by
      intro m
      have hset : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = 1))
          = Finset.univ.image (fun e : Equiv.Perm (Fin m) => Equiv.Perm.decomposeFin.symm (0, e)) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hσ
          refine ⟨(Equiv.Perm.decomposeFin σ).2, ?_⟩
          rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at hσ
          have hp0 : σ 0 = (Equiv.Perm.decomposeFin σ).1 := by
            conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
            exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
          have h0 : (Equiv.Perm.decomposeFin σ).1 = 0 := by
            rw [← hp0]; exact hσ
          rw [← h0]
          exact Equiv.Perm.decomposeFin.symm_apply_apply σ
        · rintro ⟨e, rfl⟩
          rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
          show Equiv.Perm.decomposeFin.symm (0,e) 0 = 0
          exact Equiv.Perm.decomposeFin_symm_apply_zero 0 e
      rw [hset]
      rw [Finset.card_image_of_injective]
      · simp [Fintype.card_perm]
      · intro e1 e2 h
        have := congrArg Equiv.Perm.decomposeFin h
        simpa using this
    have hcase2_q : ∀ (m ℓ:ℕ) (q : Fin m), 2 ≤ ℓ →
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ ∧ σ 0 = q.succ)).card
        = (Finset.univ.filter (fun e : Equiv.Perm (Fin m) => Function.minimalPeriod (⇑e) q = ℓ-1)).card := by
      intro m ℓ q hℓ
      apply Finset.card_bij' (fun σ (_ : σ ∈ _) => (Equiv.Perm.decomposeFin σ).2) (fun e (_ : e ∈ _) => Equiv.Perm.decomposeFin.symm (q.succ, e))
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        obtain ⟨hσ1, hσ2⟩ := hσ
        have hp0 : σ 0 = (Equiv.Perm.decomposeFin σ).1 := by
          conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
          exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
        have hp0' : (Equiv.Perm.decomposeFin σ).1 = q.succ := by rw [← hp0]; exact hσ2
        have hpair : Equiv.Perm.decomposeFin σ = (q.succ, (Equiv.Perm.decomposeFin σ).2) := Prod.ext hp0' rfl
        have hσeq : σ = Equiv.Perm.decomposeFin.symm (q.succ, (Equiv.Perm.decomposeFin σ).2) := by
          conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
          rw [hpair]
        rw [hσeq] at hσ1
        rw [hkey] at hσ1
        omega
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        refine ⟨?_, ?_⟩
        · rw [hkey]; omega
        · exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
      · intro σ hσ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        obtain ⟨hσ1,hσ2⟩ := hσ
        have hp0 : σ 0 = (Equiv.Perm.decomposeFin σ).1 := by
          conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
          exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
        have hp0' : (Equiv.Perm.decomposeFin σ).1 = q.succ := by rw [← hp0]; exact hσ2
        have hpair : Equiv.Perm.decomposeFin σ = (q.succ, (Equiv.Perm.decomposeFin σ).2) := Prod.ext hp0' rfl
        rw [← hpair]
        exact Equiv.Perm.decomposeFin.symm_apply_apply σ
      · intro e he
        exact congrArg Prod.snd (Equiv.Perm.decomposeFin.apply_symm_apply (q.succ, e))
    have hcase2 : ∀ (m ℓ:ℕ), 2 ≤ ℓ → ℓ ≤ m+1 →
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ)).card
        = ∑ q : Fin m, (Finset.univ.filter (fun e : Equiv.Perm (Fin m) => Function.minimalPeriod (⇑e) q = ℓ-1)).card := by
      intro m ℓ hℓ2 hℓm
      have hm0 : 0 < m := by omega
      have hnot0 : ∀ σ : Equiv.Perm (Fin (m+1)), Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ → σ 0 ≠ 0 := by
        intro σ hσ hcontra
        have hfix : Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = 1 := by
          rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
          exact hcontra
        omega
      classical
      have hfiber_eq : ∀ q : Fin m, (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ)).filter
          (fun σ : Equiv.Perm (Fin (m+1)) => (if h : σ 0 = 0 then (⟨0,hm0⟩:Fin m) else (σ 0).pred h) = q)
          = Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ ∧ σ 0 = q.succ) := by
        intro q
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hσℓ, hfib⟩
          refine ⟨hσℓ, ?_⟩
          have hne0 : σ 0 ≠ 0 := hnot0 σ hσℓ
          rw [dif_neg hne0] at hfib
          rw [← hfib]
          exact (Fin.succ_pred (σ 0) hne0).symm
        · rintro ⟨hσℓ, hσ0⟩
          have hne0 : σ 0 ≠ 0 := by rw [hσ0]; exact Fin.succ_ne_zero q
          refine ⟨hσℓ, ?_⟩
          rw [dif_neg hne0]
          apply Fin.succ_injective
          rw [Fin.succ_pred]
          exact hσ0
      have hstep1 : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ)).card
          = ∑ q : Fin m, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ)).filter
            (fun σ : Equiv.Perm (Fin (m+1)) => (if h : σ 0 = 0 then (⟨0,hm0⟩:Fin m) else (σ 0).pred h) = q)).card := by
        apply Finset.card_eq_sum_card_fiberwise
        intro σ _
        exact Finset.mem_univ _
      rw [hstep1]
      apply Finset.sum_congr rfl
      intro q _
      rw [hfiber_eq q, hcase2_q m ℓ q hℓ2]
    have hlevel_zero : ∀ (m ℓ:ℕ), 1 ≤ ℓ → ℓ ≤ m+1 →
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) (0:Fin (m+1)) = ℓ)).card = m.factorial := by
      intro m
      induction m with
      | zero =>
          intro ℓ hℓ1 hℓ2
          have hℓeq : ℓ = 1 := le_antisymm hℓ2 hℓ1
          rw [hℓeq]
          exact hcase1 0
      | succ m ih =>
          intro ℓ hℓ1 hℓ2
          rcases eq_or_lt_of_le hℓ1 with hℓeq | hℓgt
          · rw [← hℓeq]
            exact hcase1 (m+1)
          · have hℓ2' : 2 ≤ ℓ := hℓgt
            rw [hcase2 (m+1) ℓ hℓ2' hℓ2]
            have hcommon : (Finset.univ.filter (fun e:Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑e) (0:Fin (m+1)) = ℓ-1)).card = m.factorial :=
              ih (ℓ-1) (by omega) (by omega)
            calc ∑ q : Fin (m+1), (Finset.univ.filter (fun e:Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑e) q = ℓ-1)).card
                = ∑ q : Fin (m+1), (Finset.univ.filter (fun e:Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑e) (0:Fin (m+1)) = ℓ-1)).card :=
                  Finset.sum_congr rfl (fun q _ => hswap_indep (m+1) q 0 (ℓ-1))
              _ = ∑ _q : Fin (m+1), m.factorial := by rw [hcommon]
              _ = (m+1) * m.factorial := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
              _ = (m+1).factorial := (Nat.factorial_succ m).symm
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    have hi0eq : i0 = (0 : Fin (m+1)) := by rw [hi0]; rfl
    have hmp_iff : ∀ σ : Equiv.Perm (Fin (m+1)), (σ^k) i0 = i0 ↔ Function.minimalPeriod (⇑σ) i0 ∣ k := by
      intro σ
      have hshow : (σ^k) i0 = i0 ↔ (⇑σ)^[k] i0 = i0 := by rw [← Equiv.Perm.coe_pow]
      rw [hshow]
      constructor
      · intro h
        exact (show Function.IsPeriodicPt (⇑σ) k i0 from h).minimalPeriod_dvd
      · rintro ⟨j,hj⟩
        rw [hj]
        exact (Function.isPeriodicPt_minimalPeriod (⇑σ) i0).mul_const j
    have hseteq : Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => (σ^k) i0 = i0)
        = Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 ∈ Nat.divisors k) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.mem_divisors]
      rw [hmp_iff]
      exact ⟨fun h => ⟨h, hk.ne'⟩, fun h => h.1⟩
    rw [hseteq]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0) (t := Nat.divisors k)
        (by intro σ hσ; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢; exact hσ)]
    have hterms : ∑ ℓ ∈ Nat.divisors k,
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 ∈ Nat.divisors k)).filter
          (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 = ℓ)).card
        = ∑ _ℓ ∈ Nat.divisors k, m.factorial := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hrefine : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 ∈ Nat.divisors k)).filter
          (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 = ℓ)
          = Finset.univ.filter (fun σ : Equiv.Perm (Fin (m+1)) => Function.minimalPeriod (⇑σ) i0 = ℓ) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h2⟩; exact h2
        · intro h2; exact ⟨h2 ▸ hℓ, h2⟩
      rw [hrefine]
      rw [Nat.mem_divisors] at hℓ
      obtain ⟨hdvd, hk0⟩ := hℓ
      have hℓpos : 1 ≤ ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact hk0 (Nat.zero_dvd.mp hdvd))
      have hℓle : ℓ ≤ m + 1 := le_trans (Nat.le_of_dvd hk hdvd) hkn
      rw [hi0eq]
      exact hlevel_zero m ℓ hℓpos hℓle
    rw [hterms, Finset.sum_const, smul_eq_mul, mul_comm]
    have hmm : m + 1 - 1 = m := by omega
    rw [hmm]
  calc ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun i : Fin n => (σ ^ k) i = i)).card
      = ∑ i : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i = i)).card := h1
    _ = ∑ i : Fin n, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (σ ^ k) i0 = i0)).card :=
        Finset.sum_congr rfl (fun i _ => h2 i)
    _ = n * ((n - 1).factorial * (Nat.divisors k).card) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, h3]
    _ = n.factorial * (Nat.divisors k).card := by
        rw [← mul_assoc, Nat.mul_factorial_pred hn.ne']

end Native.Competemath.P68

namespace Native.Competemath.P80

/-- competemath.com problem 80. -/
theorem bracelet_of_blues : ((Finset.range 47).filter (fun n => n % 5 ≥ 2)).card = 27 := by decide

end Native.Competemath.P80

namespace Native.Competemath.P93

/-- competemath.com problem 93. -/
theorem pet_survey : ((Finset.Icc 1 12 ∪ Finset.Icc 8 16 : Finset ℕ).card + 2 = 18) := by decide

end Native.Competemath.P93

namespace Native.Competemath.P94

/-- competemath.com problem 94. -/
theorem uncle_riddle : (Finset.Icc 3 50).filter (fun n => n + 6 = 2 * (n - 2)) = {10} := by decide

end Native.Competemath.P94

namespace Native.Competemath.P106

/-- competemath.com problem 106. -/
theorem triple_binom_prime_mod (p : ℕ) (hp : Nat.Prime p) (h2 : p ≠ 2) :
    (∑ k ∈ Finset.range p, Nat.choose (3 * (p - 1)) (3 * k)) % p = 1 := by
  by_cases hp3 : p = 3
  · subst hp3
    have h1 : (∑ k ∈ Finset.range 3, Nat.choose (3 * (3 - 1)) (3 * k)) % 3 = 1 := by
      decide
    exact h1
  · have h3 : 3 * (∑ k ∈ Finset.range p, Nat.choose (3 * (p - 1)) (3 * k))
        = 2 ^ (3 * (p - 1)) + 2 := by
          have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
            Complex.isPrimitiveRoot_exp 3 (by norm_num)
          set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3) with hω_def
          have hω3 : ω ^ 3 = 1 := hprim.pow_eq_one
          have hωne1 : ω ≠ 1 := hprim.ne_one (by norm_num)
          have hω2 : ω ^ 2 + ω + 1 = 0 := by
            have hfactor : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
              have heq3 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
              rw [heq3, hω3]; ring
            rcases mul_eq_zero.mp hfactor with h | h
            · exact absurd (sub_eq_zero.mp h) hωne1
            · exact h
          have hfilter : ∀ j : ℕ, (1 : ℂ) + ω ^ j + ω ^ (2 * j) = if 3 ∣ j then 3 else 0 := by
            intro j
            have hjm : ω ^ j = ω ^ (j % 3) := by
              conv_lhs => rw [← Nat.div_add_mod j 3]
              rw [pow_add, pow_mul, hω3, one_pow, one_mul]
            have h2jm : ω ^ (2 * j) = ω ^ (2 * (j % 3)) := by
              rw [mul_comm 2 j, pow_mul, hjm, ← pow_mul, mul_comm]
            rw [hjm, h2jm]
            have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
            rcases hcases with h | h | h
            · rw [h]
              norm_num [Nat.dvd_iff_mod_eq_zero, h]
            · rw [h]
              rw [if_neg (by omega)]
              linear_combination hω2
            · rw [h]
              rw [if_neg (by omega)]
              have e4 : ω ^ (2 * 2) = ω := by
                rw [show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_add, hω3, one_mul, pow_one]
              rw [e4]
              linear_combination hω2
          have hbin1 : ((2:ℂ)) ^ (3 * (p-1)) = ∑ j ∈ Finset.range (3*(p-1)+1), ((3*(p-1)).choose j : ℂ) := by
            have h := add_pow (1:ℂ) 1 (3*(p-1))
            norm_num at h
            convert h using 2
          have hbin2 : (ω+1) ^ (3 * (p-1)) = ∑ j ∈ Finset.range (3*(p-1)+1), ((3*(p-1)).choose j : ℂ) * ω ^ j := by
            have h := add_pow ω 1 (3*(p-1))
            simp only [one_pow, mul_one] at h
            rw [h]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          have hbin3 : (ω^2+1) ^ (3 * (p-1)) = ∑ j ∈ Finset.range (3*(p-1)+1), ((3*(p-1)).choose j : ℂ) * ω ^ (2*j) := by
            have h := add_pow (ω^2) 1 (3*(p-1))
            simp only [one_pow, mul_one] at h
            rw [h]
            apply Finset.sum_congr rfl
            intro x hx
            rw [← pow_mul]
            ring
          have hsum_eq : (2:ℂ)^(3*(p-1)) + (ω+1)^(3*(p-1)) + (ω^2+1)^(3*(p-1))
              = ∑ j ∈ Finset.range (3*(p-1)+1), ((3*(p-1)).choose j : ℂ) * (1 + ω^j + ω^(2*j)) := by
            rw [hbin1, hbin2, hbin3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            ring
          have hsum_eq2 : (2:ℂ)^(3*(p-1)) + (ω+1)^(3*(p-1)) + (ω^2+1)^(3*(p-1))
              = 3 * ∑ j ∈ (Finset.range (3*(p-1)+1)).filter (fun j => 3 ∣ j), ((3*(p-1)).choose j : ℂ) := by
            rw [hsum_eq, Finset.mul_sum, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            rw [hfilter x]
            by_cases hd : 3 ∣ x
            · simp [hd]; ring
            · simp [hd]
          have hp2 : 2 ≤ p := hp.two_le
          have hset : (Finset.range (3*(p-1)+1)).filter (fun j => 3 ∣ j) = (Finset.range p).image (fun k => 3*k) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
            constructor
            · rintro ⟨hj, k, rfl⟩
              refine ⟨k, ?_, rfl⟩
              omega
            · rintro ⟨k, hk, rfl⟩
              refine ⟨?_, k, rfl⟩
              omega
          have hreindex : ∑ j ∈ (Finset.range (3*(p-1)+1)).filter (fun j => 3 ∣ j), ((3*(p-1)).choose j : ℂ)
              = ∑ k ∈ Finset.range p, ((3*(p-1)).choose (3*k) : ℂ) := by
            rw [hset, Finset.sum_image]
            intro x hx y hy hxy
            simp only at hxy
            omega
          have hfinal : (3:ℂ) * ∑ k ∈ Finset.range p, ((3*(p-1)).choose (3*k) : ℂ)
              = 2^(3*(p-1)) + (ω+1)^(3*(p-1)) + (ω^2+1)^(3*(p-1)) := by
            rw [hsum_eq2, hreindex]
          have hpodd : (p - 1) % 2 = 0 := by
            rcases hp.eq_two_or_odd with h | h
            · exact absurd h h2
            · omega
          obtain ⟨m, hm⟩ : ∃ m, p - 1 = 2 * m := ⟨(p-1)/2, by omega⟩
          have hpow1 : (ω+1) ^ (3 * (p-1)) = 1 := by
            have heq : ω + 1 = -ω^2 := by linear_combination hω2
            rw [heq, hm]
            have hN : 3 * (2 * m) = 6 * m := by ring
            rw [hN, pow_mul]
            have hbase : ((-ω^2)^6 : ℂ) = 1 := by
              have h6 : ((-ω^2)^6 : ℂ) = (ω^3)^4 := by ring
              rw [h6, hω3]; norm_num
            rw [hbase, one_pow]
          have hpow2 : (ω^2+1) ^ (3 * (p-1)) = 1 := by
            have heq : ω^2 + 1 = -ω := by linear_combination hω2
            rw [heq, hm]
            have hN : 3 * (2 * m) = 6 * m := by ring
            rw [hN, pow_mul]
            have hbase : ((-ω)^6 : ℂ) = 1 := by
              have h6 : ((-ω)^6 : ℂ) = (ω^3)^2 := by ring
              rw [h6, hω3]; norm_num
            rw [hbase, one_pow]
          have hCeq : (3:ℂ) * ∑ k ∈ Finset.range p, ((3*(p-1)).choose (3*k) : ℂ) = 2^(3*(p-1)) + 2 := by
            rw [hfinal, hpow1, hpow2]; ring
          have hNeq : ((3 * ∑ k ∈ Finset.range p, (3*(p-1)).choose (3*k) : ℕ) : ℂ) = ((2^(3*(p-1)) + 2 : ℕ) : ℂ) := by
            push_cast
            exact hCeq
          exact_mod_cast hNeq
    have h4 : 2 ^ (p - 1) % p = 1 := by
      have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes (by norm_num) hp).mpr (fun h => h2 h.symm)
      have hft := Nat.ModEq.pow_totient hcop2
      rw [Nat.totient_prime hp] at hft
      unfold Nat.ModEq at hft
      rw [Nat.mod_eq_of_lt hp.one_lt] at hft
      exact hft
    have hcop : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).mpr (fun h => hp3 h.symm)
    have e1 : (2:ℕ) ^ (p-1) ≡ 1 [MOD p] := by
      have h1p : (1:ℕ) % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      simp [Nat.ModEq, h4, h1p]
    have e2 : (2:ℕ) ^ (3*(p-1)) ≡ 1 [MOD p] := by
      rw [mul_comm 3 (p-1), pow_mul]
      simpa using e1.pow 3
    have e3 : (2:ℕ) ^ (3*(p-1)) + 2 ≡ 1 + 2 [MOD p] := e2.add_right 2
    have e4 : 3 * (∑ k ∈ Finset.range p, Nat.choose (3 * (p - 1)) (3 * k)) ≡ 3 [MOD p] := by
      rw [h3]; simpa using e3
    have e5 : 3 * (∑ k ∈ Finset.range p, Nat.choose (3 * (p - 1)) (3 * k)) ≡ 3 * 1 [MOD p] := by
      simpa using e4
    have e6 : (∑ k ∈ Finset.range p, Nat.choose (3 * (p - 1)) (3 * k)) ≡ 1 [MOD p] :=
      Nat.ModEq.cancel_left_of_coprime hcop.symm e5
    have h1p : (1:ℕ) % p = 1 := Nat.mod_eq_of_lt hp.one_lt
    unfold Nat.ModEq at e6
    rw [h1p] at e6
    exact e6

end Native.Competemath.P106

namespace Native.Competemath.P64

/-- competemath.com problem 64. -/
theorem pentagonal_product (ζ : ℂ) (hζ : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) : ∏ k ∈ Finset.range 4, (ζ ^ (3 * (k + 1)) - 3 * ζ ^ (k + 1) - 1) = 71 := by
  have hsum : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have h1 : (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) = 0 := by
      have h2 : ζ ^ 5 - 1 = 0 := by rw [hζ]; ring
      linear_combination h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hζ1
    · exact h
  have hpow : ∀ n : ℕ, ζ ^ n = ζ ^ (n % 5) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n 5]
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  ring_nf
  simp [hpow]
  ring_nf
  linear_combination 2 * hsum

end Native.Competemath.P64

namespace Native.Competemath.P72

/-- competemath.com problem 72. -/
theorem factorial_divisor_collapse : ∑ d ∈ (Nat.factorial 100).divisors, (ArithmeticFunction.moebius d) * (((d ^ 2).divisors.card : ℤ)) = -33554432 := by
  let g : ArithmeticFunction ℤ := ⟨fun d => (((d ^ 2).divisors.card : ℤ)), by simp⟩
  have g_apply : ∀ d : ℕ, g d = (((d ^ 2).divisors.card : ℤ)) := fun d => rfl
  have g_mult : g.IsMultiplicative := by
    constructor
    · show (((1:ℕ) ^ 2).divisors.card : ℤ) = 1
      simp
    · intro m n hmn
      show (((m*n) ^ 2).divisors.card : ℤ) = (((m ^ 2).divisors.card:ℤ)) * (((n^2).divisors.card:ℤ))
      have h2 : (m*n)^2 = m^2 * n^2 := by ring
      rw [h2]
      have hcop : Nat.Coprime (m^2) (n^2) := hmn.pow 2 2
      have hh := Nat.Coprime.card_divisors_mul hcop
      rw [hh]
      push_cast
      ring
  set n := Nat.factorial 100 with hn_def
  have hn_ne : n ≠ 0 := Nat.factorial_ne_zero 100
  set S := n.primeFactors with hS_def
  set r : ℕ := S.prod id with hr_def
  have hs : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfact : r.factorization = ∑ p ∈ S, Finsupp.single p 1 := by
    have h1 : r = ∏ p ∈ S, p := by simp [hr_def]
    rw [h1, Nat.factorization_prod (fun p hp => (hs p hp).ne_zero)]
    apply Finset.sum_congr rfl
    intro p hp
    exact (hs p hp).factorization
  have hfact_apply : ∀ q, r.factorization q = if q ∈ S then 1 else 0 := by
    intro q
    rw [hfact, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply]
  have hr_ne : r ≠ 0 := by
    rw [hr_def]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (hs p hp).ne_zero
  have hr_sqfree : Squarefree r := by
    apply (Nat.squarefree_iff_factorization_le_one hr_ne).mpr
    intro p
    rw [hfact_apply]
    split_ifs <;> omega
  have hr_pf : r.primeFactors = S := by
    rw [(Nat.support_factorization r).symm]
    ext q
    simp only [Finsupp.mem_support_iff, hfact_apply]
    split_ifs with h <;> simp [h]
  have hr_dvd : r ∣ n := by
    have hle : ∀ p, r.factorization p ≤ n.factorization p := by
      intro p
      rw [hfact_apply]
      by_cases hpS : p ∈ S
      · simp only [if_pos hpS]
        have hmem : p ∈ n.primeFactors := hS_def ▸ hpS
        rw [← Nat.support_factorization] at hmem
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
      · simp [hpS]
    rw [← Nat.factorization_le_iff_dvd hr_ne hn_ne]
    exact hle
  have hfilter : n.divisors.filter Squarefree = r.divisors := by
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hqn, _⟩, hsqfree⟩
      have hq_ne : q ≠ 0 := hsqfree.ne_zero
      have hle : q.factorization ≤ r.factorization := by
        intro p
        by_cases hpS : p ∈ S
        · have h1 : q.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hq_ne).mp hsqfree p
          have h2 : 1 ≤ r.factorization p := by
            rw [hfact_apply]; simp [hpS]
          omega
        · have hqp : p ∉ q.primeFactors := by
            intro hmem
            exact hpS (hS_def ▸ Nat.primeFactors_mono hqn hn_ne hmem)
          rw [← Nat.support_factorization] at hqp
          simp only [Finsupp.mem_support_iff, not_not] at hqp
          rw [hqp]
          exact Nat.zero_le _
      exact ⟨(Nat.factorization_le_iff_dvd hq_ne hr_ne).mp hle, hr_ne⟩
    · rintro ⟨hqr, _⟩
      exact ⟨⟨hqr.trans hr_dvd, hn_ne⟩, hr_sqfree.squarefree_of_dvd hqr⟩
  have hsum_eq : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) * g d
               = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d) * g d := by
    rw [← hfilter]
    symm
    apply Finset.sum_filter_of_ne
    intro x _ hx
    by_contra hxsq
    apply hx
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hxsq]
    simp
  have hgp : ∀ p ∈ S, (1 - g p) = (-2 : ℤ) := by
    intro p hp
    have hpp : p.Prime := hs p hp
    rw [g_apply]
    have h3 : (p^2).divisors.card = 3 := by
      rw [Nat.divisors_prime_pow hpp]
      simp
    rw [h3]
    norm_num
  have hcard : S.card = 25 := by
    have h1 : S = (Finset.range 101).filter Nat.Prime := by
      rw [hS_def]
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
      constructor
      · rintro ⟨hp, hdvd, _⟩
        have hle := (Nat.Prime.dvd_factorial hp).mp hdvd
        exact ⟨by omega, hp⟩
      · rintro ⟨hlt, hp⟩
        exact ⟨hp, (Nat.Prime.dvd_factorial hp).mpr (by omega), Nat.factorial_ne_zero 100⟩
    rw [h1]
    decide
  have main := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree g g_mult hr_sqfree
  calc ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) * (((d ^ 2).divisors.card : ℤ))
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d) * g d := by
        apply Finset.sum_congr rfl
        intro d _
        rw [g_apply]
    _ = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d) * g d := hsum_eq
    _ = ∏ p ∈ r.primeFactors, (1 - g p) := main.symm
    _ = ∏ p ∈ S, (1 - g p) := by rw [hr_pf]
    _ = ∏ p ∈ S, (-2:ℤ) := Finset.prod_congr rfl hgp
    _ = (-2:ℤ) ^ S.card := by rw [Finset.prod_const]
    _ = (-2:ℤ) ^ 25 := by rw [hcard]
    _ = -33554432 := by norm_num

end Native.Competemath.P72

namespace Native.Competemath.P76

/-- competemath.com problem 76. -/
theorem lantern_ladder : (Finset.range 10).sum (fun k => 2 * k + 1) = 100 := by decide

end Native.Competemath.P76

namespace Native.Competemath.P81

/-- competemath.com problem 81. -/
theorem library_cart : ((Finset.Icc 1 40).filter (fun n => n % 2 ≠ 0 ∧ n % 10 ≠ 5)).card = 16 := by
  decide

end Native.Competemath.P81

namespace Native.Competemath.P82

/-- competemath.com problem 82. -/
theorem iced_edge : (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 = 0 ∨ p.1 = 5 ∨ p.2 = 0 ∨ p.2 = 5)).card = 20 := by decide

end Native.Competemath.P82
