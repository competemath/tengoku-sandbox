/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P86

/-- competemath.com problem 86. -/
theorem garden_ring_posts : ((Finset.Icc 0 8 ×ˢ Finset.Icc 0 8).filter (fun p : ℕ × ℕ => p.1 % 2 = 0 ∧ p.2 % 2 = 0 ∧ (p.1 = 0 ∨ p.1 = 8 ∨ p.2 = 0 ∨ p.2 = 8))).card = 16 := by decide

end Native.Competemath.P86

namespace Native.Competemath.P87

/-- competemath.com problem 87. -/
theorem marble_gift : (Finset.range 21).filter (fun t => t - 3 = (20 - t) + 3) = {13} := by decide

end Native.Competemath.P87

namespace Native.Competemath.P91

/-- competemath.com problem 91. -/
theorem chocolate_grid_squares : ((Finset.range 3 ×ˢ Finset.range 4 ×ˢ Finset.range 3).filter (fun p => p.2.1 + p.1 < 4 ∧ p.2.2 + p.1 < 3)).card = 20 := by decide

end Native.Competemath.P91

namespace Native.Competemath.P26

/-- competemath.com problem 26. -/
theorem acute_9gon_triangles : (Finset.univ.filter (fun t : Fin 9 × Fin 9 × Fin 9 => t.1.val < t.2.1.val ∧ t.2.1.val < t.2.2.val ∧ t.2.1.val - t.1.val ≤ 4 ∧ t.2.2.val - t.2.1.val ≤ 4 ∧ 5 ≤ t.2.2.val - t.1.val)).card = 30 := by decide

end Native.Competemath.P26

namespace Native.Competemath.P27

/-- competemath.com problem 27. -/
theorem hexagon_harmonious_colorings : ((Finset.univ : Finset (Fin 6 → Fin 3)).filter fun f => f 0 ≠ f 1 ∧ f 1 ≠ f 2 ∧ f 2 ≠ f 3 ∧ f 3 ≠ f 4 ∧ f 4 ≠ f 5 ∧ f 5 ≠ f 0 ∧ f 0 ≠ f 3 ∧ f 1 ≠ f 4 ∧ f 2 ≠ f 5).card = 42 := by decide

end Native.Competemath.P27

namespace Native.Competemath.P92

/-- competemath.com problem 92. -/
theorem window_of_windows : ((Finset.range 3 ×ˢ Finset.range 3 ×ˢ Finset.range 3).filter (fun p => p.2.1 + p.1 < 3 ∧ p.2.2 + p.1 < 3)).card = 14 := by decide

end Native.Competemath.P92

namespace Native.Competemath.P97

/-- competemath.com problem 97. -/
theorem toy_shop_wheels : (Finset.range 9).filter (fun t => 3 * t + 2 * (8 - t) = 21) = {5} := by decide

end Native.Competemath.P97

namespace Native.Competemath.P110

/-- competemath.com problem 110. -/
theorem ballot_matrix_det (n : ℕ) : Matrix.det (Matrix.of (fun i j : Fin n ↦ ((i.val + j.val + 2).choose (i.val + 1) : ℤ))) = (n : ℤ) + 1 := by
  set B : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j : Fin n ↦ ((i.val + j.val + 2).choose (i.val + 1) : ℤ)) with hB
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j : Fin n ↦ ((i.val + 1).choose (j.val + 1) : ℤ)) with hM
  set x : Fin n → ℤ := fun i => (-1:ℤ) ^ (i.val) with hx
  have hMdet : M.det = 1 := by
    rw [hM, Matrix.det_of_lowerTriangular]
    · simp
    · intro i j hij
      simp only [Matrix.of_apply]
      have : (i:ℕ) < j := hij
      norm_cast
      exact Nat.choose_eq_zero_of_lt (by omega)
  have hMx : ∀ i : Fin n, (M.mulVec x) i = 1 := by
    intro i
    show ∑ j, M i j * x j = 1
    simp only [hM, hx, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((i.val+1).choose (j+1) : ℤ) * (-1:ℤ)^j) n]
    have hsucc := Finset.sum_range_succ' (fun k => (-1:ℤ)^k * ((i.val+1).choose k : ℤ)) n
    have hilt := i.isLt
    have hext : ∑ k ∈ Finset.range ((i.val+1)+1), (-1:ℤ)^k * ((i.val+1).choose k : ℤ) = ∑ k ∈ Finset.range (n+1), (-1:ℤ)^k * ((i.val+1).choose k : ℤ) := by
      apply Finset.sum_subset
      · intro y hy; simp only [Finset.mem_range] at hy ⊢; omega
      · intro k hk hk'
        simp only [Finset.mem_range, not_lt] at hk hk'
        have hlt2 : i.val + 1 < k := by omega
        simp [Nat.choose_eq_zero_of_lt hlt2]
    have halt := @Int.alternating_sum_range_choose (i.val+1)
    rw [← hext, halt] at hsucc
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero] at hsucc
    have hswap : ∑ k ∈ Finset.range n, (-1:ℤ) ^ k * -1 * ((i.val + 1).choose (k + 1) : ℤ) = - ∑ i_1 ∈ Finset.range n, ((i.val + 1).choose (i_1 + 1) : ℤ) * (-1:ℤ) ^ i_1 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simp only [pow_succ] at hsucc
    rw [hswap] at hsucc
    linarith
  have hBeq : B = M * (1 + Matrix.of (fun i j : Fin n => x i * x j)) * (Matrix.transpose M) := by
    have step1 : ∀ i k : Fin n, (M * (1 + Matrix.of (fun i j : Fin n => x i * x j))) i k = M i k + x k := by
      intro i k
      rw [Matrix.mul_apply]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, mul_add]
      rw [Finset.sum_add_distrib]
      have e1 : (∑ y, M i y * if y = k then (1:ℤ) else 0) = M i k := by simp
      have e2 : (∑ y, M i y * (x y * x k)) = (M.mulVec x) i * x k := by
        show (∑ y, M i y * (x y * x k)) = (∑ y, M i y * x y) * x k
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [e1, e2, hMx i]
      ring
    have step2 : ∀ i j : Fin n, (M * (1 + Matrix.of (fun i j : Fin n => x i * x j)) * (Matrix.transpose M)) i j = (M * Matrix.transpose M) i j + 1 := by
      intro i j
      rw [Matrix.mul_apply]
      simp only [step1, Matrix.transpose_apply]
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply]
      rw [show (∑ x_1, (M i x_1 + x x_1) * M j x_1) = (∑ x_1, M i x_1 * M j x_1) + ∑ x_1, x x_1 * M j x_1 from by rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro y hy; ring]
      have e3 : (∑ y, x y * M j y) = (M.mulVec x) j := by
        show (∑ y, x y * M j y) = ∑ y, M j y * x y
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [e3, hMx j]
    have vandermonde : ∀ (a b : ℕ), ∑ p ∈ Finset.range (a+1), a.choose p * b.choose p = (a+b).choose a := by
      intro a b
      have h := Nat.add_choose_eq a b a
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * b.choose j)] at h
      have hrefl := Finset.sum_range_reflect (fun k => a.choose k * b.choose (a - k)) (a+1)
      rw [h, ← hrefl]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.mem_range] at hy
      have hya : y ≤ a := by omega
      rw [Nat.add_sub_cancel, Nat.sub_sub_self hya, Nat.choose_symm hya]
    have key : ∀ i j : Fin n, (∑ k : Fin n, (i.val+1).choose (k.val+1) * (j.val+1).choose (k.val+1)) + 1 = (i.val+j.val+2).choose (i.val+1) := by
      intro i j
      rw [Fin.sum_univ_eq_sum_range (fun k => (i.val+1).choose (k+1) * (j.val+1).choose (k+1)) n]
      have hv := vandermonde (i.val+1) (j.val+1)
      rw [Finset.sum_range_succ'] at hv
      simp only [Nat.choose_zero_right, mul_one] at hv
      have heq : i.val + 1 + (j.val+1) = i.val + j.val + 2 := by omega
      rw [heq] at hv
      have hext : ∑ k ∈ Finset.range (i.val+1), (i.val+1).choose (k+1) * (j.val+1).choose (k+1) = ∑ k ∈ Finset.range n, (i.val+1).choose (k+1) * (j.val+1).choose (k+1) := by
        apply Finset.sum_subset
        · intro y hy; simp only [Finset.mem_range] at hy ⊢; have := i.isLt; omega
        · intro k hk hk'
          simp only [Finset.mem_range, not_lt] at hk hk'
          simp [Nat.choose_eq_zero_of_lt (show i.val + 1 < k + 1 by omega)]
      rw [hext] at hv
      exact hv
    ext i j
    rw [step2]
    show B i j = (M * Matrix.transpose M) i j + 1
    rw [hB, hM]
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    have hkey := key i j
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hkey
    push_cast at hcast
    linarith [hcast]
  have hN : (1 + Matrix.of (fun i j : Fin n => x i * x j)).det = 1 + ∑ i, x i * x i := by
    have e1 : (Matrix.of fun i j : Fin n => x i * x j) = Matrix.replicateCol Unit x * Matrix.replicateRow Unit x := by ext i j; simp [Matrix.mul_apply]
    rw [e1, Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [Matrix.mul_apply]
  have hsq : ∑ i : Fin n, x i * x i = n := by
    have hone : ∀ i : Fin n, x i * x i = 1 := by
      intro i
      simp only [hx]
      rw [← pow_add]
      exact Even.neg_one_pow ⟨i.val, by ring⟩
    rw [Finset.sum_congr rfl (fun i _ => hone i)]
    simp
  rw [hBeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hMdet, hN, hsq]
  ring

end Native.Competemath.P110

namespace Native.Competemath.P74

/-- competemath.com problem 74. -/
theorem two_three_frog : ((Finset.Icc 1 30).filter (fun n => n % 5 = 1 ∨ n % 5 = 3)).card = 12 := by decide

end Native.Competemath.P74

namespace Native.Competemath.P75

/-- competemath.com problem 75. -/
theorem clap_count : ((Finset.Icc 1 30).filter (fun n => n % 3 = 0 ∨ n % 10 = 3 ∨ n / 10 = 3)).card = 12 := by decide

end Native.Competemath.P75

namespace Native.Competemath.P79

/-- competemath.com problem 79. -/
theorem cuckoo_tally : 2 * (∑ k ∈ Finset.Icc 1 12, k) + 24 = 180 := by decide

end Native.Competemath.P79

namespace Native.Competemath.P112

set_option maxHeartbeats 1000000 in
/-- competemath.com problem 112. -/
theorem invariant_quartets (m : ℕ) (hm : 1 ≤ m) : Nat.card {v : Fin 4 → ℤ // ∑ i, v i ^ 2 = (2 : ℤ) ^ m} = 24 := by
  have h1 : Nat.card {v : Fin 4 → ℤ // ∑ i, v i ^ 2 = (2:ℤ)^1} = 24 := by
    have hmem : ∀ v : Fin 4 → ℤ,
        v ∈ (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-1:ℤ) 1)).filter
          (fun v => ∑ i, v i ^ 2 = (2:ℤ)^1) ↔ (∑ i, v i ^ 2 = (2:ℤ)^1) := by
      intro v
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
      constructor
      · intro h
        exact h.2
      · intro hsum
        refine ⟨?_, hsum⟩
        intro i
        have hi : v i ^ 2 ≤ 2 := by
          have hnn : ∀ j, (0:ℤ) ≤ v j ^ 2 := fun j => sq_nonneg _
          have := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
          simpa [hsum] using this
        constructor <;> nlinarith [sq_nonneg (v i - 1), sq_nonneg (v i + 1)]
    haveI hfin := Fintype.subtype
      ((Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-1:ℤ) 1)).filter
        (fun v => ∑ i, v i ^ 2 = (2:ℤ)^1))
      hmem
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype _ hmem]
    decide
  have h2 : Nat.card {v : Fin 4 → ℤ // ∑ i, v i ^ 2 = (2:ℤ)^2} = 24 := by
    norm_num
    have hbound : ∀ (v : Fin 4 → ℤ), (∑ i, v i ^ 2 = 4) → ∀ i, v i ∈ Finset.Icc (-2:ℤ) 2 := by
      intro v hv i
      have hsq : v i ^ 2 ≤ 4 := by
        have h := Finset.single_le_sum (f := fun j => v j ^ 2) (by intro j _; positivity) (Finset.mem_univ i)
        rw [hv] at h
        exact h
      rw [Finset.mem_Icc]
      constructor <;> nlinarith [sq_nonneg (v i - 2), sq_nonneg (v i + 2)]
    set T : Finset (Fin 4 → ℤ) := (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-2:ℤ) 2).filter (fun v => ∑ i, v i ^ 2 = 4) with hT
    have hiff : ∀ v : Fin 4 → ℤ, (∑ i, v i ^ 2 = 4) ↔ v ∈ T := by
      intro v
      rw [hT, Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · intro hv
        exact ⟨fun i => hbound v hv i, hv⟩
      · intro h
        exact h.2
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  have hstep : ∀ n, 3 ≤ n → Nat.card {v : Fin 4 → ℤ // ∑ i, v i ^ 2 = (2:ℤ)^n} = Nat.card {v : Fin 4 → ℤ // ∑ i, v i ^ 2 = (2:ℤ)^(n-2)} := by
    intro n hn
    have parity : ∀ (v : Fin 4 → ℤ), ∑ i, v i ^ 2 = (2:ℤ)^n → ∀ i, Even (v i) := by
      intro v hv
      have keysq : ∀ m : ZMod 8, 4*m^2+4*m+1 = 1 := by decide
      have hodd : ∀ x : ℤ, Odd x → ((x : ZMod 8))^2 = 1 := by
        intro x h
        obtain ⟨k, hk⟩ := h
        subst hk
        push_cast
        have := keysq (k : ZMod 8)
        linear_combination this
      have hzero : ∀ a b c d : ZMod 8, a^2+b^2+c^2+d^2 = 0 → a^2 ≠ 1 := by decide
      have hcast := congrArg (fun x : ℤ => (x : ZMod 8)) hv
      simp only at hcast
      have h8dvd : (8:ℤ) ∣ (2:ℤ)^n := by
        have : (2:ℤ)^3 ∣ (2:ℤ)^n := pow_dvd_pow 2 hn
        norm_num at this
        exact this
      have hz8 : (8 : ZMod 8) = 0 := by decide
      have hpow0 : (((2:ℤ)^n : ℤ) : ZMod 8) = 0 := by
        obtain ⟨k, hk⟩ := h8dvd
        rw [hk]
        push_cast
        rw [hz8]
        ring
      rw [hpow0] at hcast
      push_cast at hcast
      rw [Fin.sum_univ_four] at hcast
      have e0 : ((v 0 : ℤ) : ZMod 8)^2 ≠ 1 := hzero (v 0) (v 1) (v 2) (v 3) hcast
      have e1 : ((v 1 : ℤ) : ZMod 8)^2 ≠ 1 := hzero (v 1) (v 0) (v 2) (v 3) (by linear_combination hcast)
      have e2 : ((v 2 : ℤ) : ZMod 8)^2 ≠ 1 := hzero (v 2) (v 0) (v 1) (v 3) (by linear_combination hcast)
      have e3 : ((v 3 : ℤ) : ZMod 8)^2 ≠ 1 := hzero (v 3) (v 0) (v 1) (v 2) (by linear_combination hcast)
      intro i
      fin_cases i
      · by_contra hc; rw [Int.not_even_iff_odd] at hc; exact e0 (hodd _ hc)
      · by_contra hc; rw [Int.not_even_iff_odd] at hc; exact e1 (hodd _ hc)
      · by_contra hc; rw [Int.not_even_iff_odd] at hc; exact e2 (hodd _ hc)
      · by_contra hc; rw [Int.not_even_iff_odd] at hc; exact e3 (hodd _ hc)
    have hn2 : n - 2 + 2 = n := by omega
    have hpoweq : (2:ℤ)^n = 4 * (2:ℤ)^(n-2) := by
      have heq : (2:ℤ)^n = (2:ℤ)^(n-2+2) := by rw [hn2]
      rw [heq, pow_add]; ring
    apply Nat.card_congr
    refine ⟨fun v => ⟨fun i => v.1 i / 2, ?_⟩, fun w => ⟨fun i => 2 * w.1 i, ?_⟩, ?_, ?_⟩
    · have key : ∀ i, v.1 i = 2 * (v.1 i / 2) := fun i => by
        obtain ⟨c, hc⟩ := parity v.1 v.2 i
        omega
      have expand : ∑ i, (v.1 i)^2 = 4 * ∑ i, (v.1 i/2)^2 := by
        calc ∑ i, (v.1 i)^2 = ∑ i, (2*(v.1 i/2))^2 := by simp_rw [← key]
        _ = ∑ i, 4*(v.1 i/2)^2 := by
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = 4 * ∑ i, (v.1 i/2)^2 := by rw [Finset.mul_sum]
      have h4 : 4 * ∑ i, (v.1 i/2)^2 = 4 * (2:ℤ)^(n-2) := by
        rw [← expand, v.2, hpoweq]
      exact mul_left_cancel₀ (by norm_num : (4:ℤ) ≠ 0) h4
    · have expand : ∑ i, (2*w.1 i)^2 = 4 * ∑ i, (w.1 i)^2 := by
        calc ∑ i, (2*w.1 i)^2 = ∑ i, 4*(w.1 i)^2 := by
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = 4 * ∑ i, (w.1 i)^2 := by rw [Finset.mul_sum]
      rw [expand, w.2, ← hpoweq]
    · intro v
      apply Subtype.ext
      funext i
      obtain ⟨c, hc⟩ := parity v.1 v.2 i
      simp only
      omega
    · intro w
      apply Subtype.ext
      funext i
      simp only
      omega
  revert hm
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm
    match m, hm with
    | 1, _ => exact h1
    | 2, _ => exact h2
    | (n+3), _ =>
      have hn3 : 3 ≤ n + 3 := by omega
      have heq := hstep (n+3) hn3
      have hlt : n + 3 - 2 < n + 3 := by omega
      have hge1 : 1 ≤ n + 3 - 2 := by omega
      rw [heq]
      exact IH (n+3-2) hlt hge1

end Native.Competemath.P112

namespace Native.Competemath.P115

/-- competemath.com problem 115. -/
theorem summit_of_sums : padicValNat 2 (∑ k ∈ Finset.range 1000000, (k + 1) * Nat.choose 999999 k) = 999998 := by
  have hsplit : ∑ k ∈ Finset.range 1000000, (k + 1) * Nat.choose 999999 k
      = (∑ k ∈ Finset.range 1000000, k * Nat.choose 999999 k) + ∑ k ∈ Finset.range 1000000, Nat.choose 999999 k := by
    have hgen : ∀ n : ℕ, ∑ k ∈ Finset.range n, (k + 1) * Nat.choose 999999 k
        = (∑ k ∈ Finset.range n, k * Nat.choose 999999 k) + ∑ k ∈ Finset.range n, Nat.choose 999999 k := by
      intro n
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact hgen 1000000
  have h1 : ∑ k ∈ Finset.range 1000000, k * Nat.choose 999999 k = 999999 * 2 ^ 999998 := by
    have h := Nat.sum_range_mul_choose 999999
    have e1 : (999999:ℕ) - 1 = 999998 := rfl
    rw [e1] at h
    exact h
  have h2 : ∑ k ∈ Finset.range 1000000, Nat.choose 999999 k = 2 ^ 999999 := by
    exact Nat.sum_range_choose 999999
  have hsum : ∑ k ∈ Finset.range 1000000, (k + 1) * Nat.choose 999999 k = 1000001 * 2 ^ 999998 := by
    rw [hsplit, h1, h2]
    have e2 : (2:ℕ) ^ 999999 = 2 ^ 999998 * 2 := by
      rw [show (999999:ℕ) = 999998 + 1 from rfl, pow_succ]
    rw [e2, mul_comm (2 ^ 999998 : ℕ) 2, ← add_mul]
  have final : padicValNat 2 (1000001 * 2 ^ 999998) = 999998 := by
    have hodd : ¬ (2 ∣ 1000001) := by norm_num
    have hmul : padicValNat 2 (1000001 * 2 ^ 999998) = padicValNat 2 1000001 + padicValNat 2 (2 ^ 999998) :=
      padicValNat.mul (by norm_num) (by positivity)
    have hzero : padicValNat 2 1000001 = 0 := padicValNat.eq_zero_of_not_dvd hodd
    have hpow : ∀ k : ℕ, padicValNat 2 (2 ^ k) = k := fun k => padicValNat_base_pow (by norm_num) k
    have hpk : padicValNat 2 (2 ^ 999998) = 999998 := hpow 999998
    rw [hmul, hzero, hpk]
  rw [hsum]
  exact final

end Native.Competemath.P115

namespace Native.Competemath.P116

set_option exponentiation.threshold 3000

/-- competemath.com problem 116. -/
theorem derangement_dyadic_valuation : padicValNat 2 (numDerangements (2^2025 + 1)) = 2025 := by
  have parity : ∀ n : ℕ, numDerangements n % 2 = (n + 1) % 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => simp [numDerangements_zero]
      | 1, _ => simp [numDerangements_one]
      | (k+2), ih =>
        have h1 : numDerangements k % 2 = (k+1) % 2 := ih k (by omega)
        have h2 : numDerangements (k+1) % 2 = (k+2) % 2 := ih (k+1) (by omega)
        rw [numDerangements_add_two, Nat.mul_mod, Nat.add_mod (numDerangements k), h1, h2]
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk
        · have e1 : (k+1) % 2 = 1 := by omega
          have e2 : (k+2) % 2 = 0 := by omega
          have e3 : (k+2+1) % 2 = 1 := by omega
          rw [e1, e2, e3]
        · have e1 : (k+1) % 2 = 0 := by omega
          have e2 : (k+2) % 2 = 1 := by omega
          have e3 : (k+2+1) % 2 = 0 := by omega
          rw [e1, e2, e3]
  have key : numDerangements (2^2025 + 1) = 2^2025 * (numDerangements (2^2025 - 1) + numDerangements (2^2025)) := by
    have hp : (1:ℕ) ≤ 2^2025 := Nat.one_le_two_pow
    generalize hN : (2:ℕ)^2025 = N at hp ⊢
    have := numDerangements_add_two (N - 1)
    have e1 : N - 1 + 2 = N + 1 := by omega
    have e2 : N - 1 + 1 = N := by omega
    rw [e1, e2] at this
    exact this
  have hodd1 : numDerangements (2^2025 - 1) % 2 = 0 := by
    have hp : (1:ℕ) ≤ 2^2025 := Nat.one_le_two_pow
    have heven : (2:ℕ)^2025 % 2 = 0 := by
      have : (2:ℕ) ∣ 2^2025 := dvd_pow_self 2 (by norm_num)
      omega
    have := parity (2^2025 - 1)
    omega
  have hodd2 : numDerangements (2^2025) % 2 = 1 := by
    have heven : (2:ℕ)^2025 % 2 = 0 := by
      have : (2:ℕ) ∣ 2^2025 := dvd_pow_self 2 (by norm_num)
      omega
    have := parity (2^2025)
    omega
  have hsum_odd : (numDerangements (2^2025 - 1) + numDerangements (2^2025)) % 2 = 1 := by omega
  have hval : padicValNat 2 (numDerangements (2^2025 - 1) + numDerangements (2^2025)) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    omega
  rw [key, padicValNat.mul (by positivity) (by omega)]
  rw [padicValNat_base_pow (by norm_num) 2025]
  omega

end Native.Competemath.P116

namespace Native.Competemath.P121

/-- competemath.com problem 121. -/
theorem plaza_differences : ∑ r ∈ Finset.Icc 1 1000000, ∑ c ∈ Finset.Icc 1 1000000, (max r c - min r c) = 333333333333000000 := by
  have h1 : ∑ r ∈ Finset.Icc 1 1000000, ∑ c ∈ Finset.Icc 1 1000000, (max r c - min r c) = 2 * ∑ r ∈ Finset.Icc 1 1000000, ∑ c ∈ Finset.Icc 1 1000000, (r - c) := by
    have general : ∀ s : Finset ℕ, ∑ r ∈ s, ∑ c ∈ s, (max r c - min r c) = 2 * ∑ r ∈ s, ∑ c ∈ s, (r - c) := by
      intro s
      have key : ∀ r c : ℕ, max r c - min r c = (r - c) + (c - r) := by
        intro r c
        rcases le_total r c with h | h
        · rw [max_eq_right h, min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.zero_add]
        · rw [max_eq_left h, min_eq_right h, Nat.sub_eq_zero_of_le h, Nat.add_zero]
      simp_rw [key, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := s) (t := s) (f := fun r c => c - r), two_mul]
    exact general (Finset.Icc 1 1000000)
  have h2 : ∀ n : ℕ, ∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 n, (r - c) = n * (n + 1) * (n - 1) / 6 := by
    suffices h : ∀ n : ℕ, 6 * (∑ r ∈ Finset.Icc 1 n, ∑ c ∈ Finset.Icc 1 n, (r - c)) = n * (n + 1) * (n - 1) by intro n; have := h n; omega
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      simp only [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega)]
      simp only [Finset.sum_add_distrib]
      have hz : ∑ x ∈ Finset.Icc 1 k, (x - (k + 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_Icc] at hx
        omega
      have hT : ∀ m : ℕ, 2 * (∑ c ∈ Finset.Icc 1 m, (m + 1 - c)) = m * (m + 1) := by
        intro m
        induction m with
        | zero => simp
        | succ j ihj =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
          have e2 : ∀ k ∈ Finset.Icc 1 j, j + 1 + 1 - k = (j + 1 - k) + 1 := by
            intro k hk
            simp only [Finset.mem_Icc] at hk
            omega
          rw [Finset.sum_congr rfl e2, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
          have expand : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
          rw [expand]; omega
      rw [hz]
      have hTk := hT k
      have expand2 : (k + 1) * (k + 1 + 1) * (k + 1 - 1) = k * (k + 1) * (k - 1) + 3 * (k * (k + 1)) := by
        rcases k with _ | k'
        · simp
        · simp only [Nat.succ_sub_one]
          ring
      rw [expand2]; omega
  rw [h1, h2 1000000]

end Native.Competemath.P121

namespace Native.Competemath.P124

/-- competemath.com problem 124. -/
theorem billion_bubble_chime : (∑ i ∈ Finset.range 1000000000, (i : ℕ)) = 499999999500000000 := by
  have h := Finset.sum_range_id_mul_two 1000000000
  have h2 : (1000000000 * (1000000000 - 1) : ℕ) = 499999999500000000 * 2 := by norm_num
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

end Native.Competemath.P124

namespace Native.Competemath.P130

/-- competemath.com problem 130. -/
theorem square_roots_of_one_mod_120120 : Nat.card {x : ZMod 120120 // x ^ 2 = 1} = 128 := by
  have hmul : ∀ a b : ℕ, Nat.Coprime a b →
      Nat.card {x : ZMod (a * b) // x ^ 2 = 1}
        = Nat.card {x : ZMod a // x ^ 2 = 1} * Nat.card {x : ZMod b // x ^ 2 = 1} := by
          intro a b hab
          have e := ZMod.chineseRemainder hab
          rw [← Nat.card_prod]
          apply Nat.card_congr
          refine (e.toEquiv.subtypeEquiv (q := fun y => y ^ 2 = 1) (fun x => ?_)).trans ?_
          simp only [← map_pow, ← map_one e.toRingHom, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
          rw [show (e.toRingHom 1 : ZMod a × ZMod b) = e 1 from rfl, e.injective.eq_iff]
          refine ⟨fun y => (⟨y.1.1, ?_⟩, ⟨y.1.2, ?_⟩), fun pq => ⟨(pq.1.1, pq.2.1), ?_⟩, ?_, ?_⟩
          simpa using congrArg Prod.fst y.2
          simpa using congrArg Prod.snd y.2
          rw [Prod.ext_iff]; simp [Prod.pow_def, pq.1.2, pq.2.2]
          intro y; simp
          intro pq; simp
  have h8 : Nat.card {x : ZMod 8 // x ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h3 : Nat.card {x : ZMod 3 // x ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h5 : Nat.card {x : ZMod 5 // x ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h7 : Nat.card {x : ZMod 7 // x ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h11 : Nat.card {x : ZMod 11 // x ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have h13 : Nat.card {x : ZMod 13 // x ^ 2 = 1} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have e : (120120 : ℕ) = 8 * (3 * (5 * (7 * (11 * 13)))) := by norm_num
  rw [e,
    hmul 8 (3 * (5 * (7 * (11 * 13)))) (by decide),
    hmul 3 (5 * (7 * (11 * 13))) (by decide),
    hmul 5 (7 * (11 * 13)) (by decide),
    hmul 7 (11 * 13) (by decide),
    hmul 11 13 (by decide),
    h8, h3, h5, h7, h11, h13]

end Native.Competemath.P130

namespace Native.Competemath.P138

/-- competemath.com problem 138. -/
theorem squaring_cyclic_count :
    (Finset.univ.filter (fun x : (ZMod 998244353)ˣ => Odd (orderOf x))).card = 119 := by
  have h1 : Nat.Prime 998244353 := by
    norm_num
  haveI : Fact (Nat.Prime 998244353) := ⟨h1⟩
  have h2 : Fintype.card (ZMod 998244353)ˣ = 998244352 := by
    rw [ZMod.card_units_eq_totient]
    rw [Nat.totient_prime h1]
  have h3 : (Finset.univ.filter (fun x : (ZMod 998244353)ˣ => Odd (orderOf x)))
      = (Finset.univ.filter (fun x : (ZMod 998244353)ˣ => orderOf x ∣ 119)) := by
        apply Finset.filter_congr
        intro x _
        have hdvd : orderOf x ∣ 998244352 := h2 ▸ orderOf_dvd_card
        have h119 : (998244352:ℕ) = 2^23 * 119 := by norm_num
        rw [h119] at hdvd
        constructor
        intro hd
        have hcop2 : Nat.Coprime (orderOf x) 2 := hd.coprime_two_right
        have hcop : Nat.Coprime (orderOf x) (2^23) := hcop2.pow_right 23
        exact hcop.dvd_of_dvd_mul_left hdvd
        intro hd119
        obtain ⟨c, hc⟩ := hd119
        have hodd119 : Odd (orderOf x * c) := hc ▸ (by decide : Odd 119)
        exact (Nat.odd_mul.mp hodd119).1
  have h4 : (Finset.univ.filter (fun x : (ZMod 998244353)ˣ => orderOf x ∣ 119)).card = 119 := by
    have hdvd : (119:ℕ) ∣ Fintype.card (ZMod 998244353)ˣ := by rw [h2]; decide
    have hunion : (Finset.univ.filter (fun x : (ZMod 998244353)ˣ => orderOf x ∣ 119)) = (Nat.divisors 119).biUnion (fun d => Finset.univ.filter (fun x : (ZMod 998244353)ˣ => orderOf x = d)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Nat.mem_divisors, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact ⟨orderOf x, ⟨hx, by norm_num⟩, rfl⟩
      · rintro ⟨d, ⟨hd, -⟩, rfl⟩
        exact hd
    rw [hunion, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun u hu => IsCyclic.card_orderOf_eq_totient (dvd_trans (Nat.dvd_of_mem_divisors hu) hdvd))]
      exact Nat.sum_totient 119
    · intro a _ b _ hab
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro y hy hy2
      exact hab (hy ▸ hy2 ▸ rfl)
  rw [h3, h4]

end Native.Competemath.P138

namespace Native.Competemath.P96

/-- competemath.com problem 96. -/
theorem open_storybook : (Finset.range 100).sum (fun n => if n + (n + 1) = 45 then n * (n + 1) else 0) = 506 := by decide

end Native.Competemath.P96

namespace Native.Competemath.P160

/-- competemath.com problem 160. -/
theorem sqrt_excess_mod3_sum :
    (∑ n ∈ Finset.Icc 1 (10^18 - 1 : ℕ),
      (if (n - (Nat.sqrt n)^2) % 3 = 2 then (-1 : ℤ) else 1)) = 333333333999999999 := by
  have h1 : ∀ k : ℕ, (∑ n ∈ Finset.Icc (k^2) ((k+1)^2 - 1),
      (if (n - (Nat.sqrt n)^2) % 3 = 2 then (-1 : ℤ) else 1)) = 2 * (((k+1)/3 : ℕ) : ℤ) + 1 := by
    have hclosed : ∀ k : ℕ, (∑ r ∈ Finset.range (2*k+1), (if r % 3 = 2 then (-1:ℤ) else 1)) = 2 * (((k+1)/3 : ℕ) : ℤ) + 1 := by
      intro k
      induction k with
      | zero => decide
      | succ n ih =>
        rw [show 2*(n+1)+1 = (2*n+1)+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h3 with h3 | h3 | h3 <;> simp only [show (2*n+1)%3 = (2*(n%3)+1)%3 from by omega, show (2*n+2)%3 = (2*(n%3)+2)%3 from by omega, h3] <;> norm_num <;> omega
    intro k
    have hreindex : (∑ n ∈ Finset.Icc (k^2) ((k+1)^2 - 1),
        (if (n - (Nat.sqrt n)^2) % 3 = 2 then (-1 : ℤ) else 1))
        = ∑ r ∈ Finset.range (2*k+1), (if r % 3 = 2 then (-1:ℤ) else 1) := by
      apply Finset.sum_nbij' (fun n => n - k^2) (fun r => k^2 + r)
      intro a ha
      simp only [Finset.mem_Icc] at ha
      simp only [Finset.mem_range]
      have hexp : (k+1)^2 = k^2 + 2*k + 1 := by ring
      omega
      intro a ha
      simp only [Finset.mem_range] at ha
      simp only [Finset.mem_Icc]
      have hexp : (k+1)^2 = k^2 + 2*k + 1 := by ring
      omega
      intro a ha; simp only [Finset.mem_Icc] at ha; omega
      intro a ha; omega
      intro a ha
      simp only [Finset.mem_Icc] at ha
      have hexp : (k+1)^2 = k^2 + 2*k + 1 := by ring
      have hsq : a.sqrt = k := by
        apply le_antisymm
        · rw [← Nat.lt_succ_iff, Nat.sqrt_lt']; simp only [Nat.succ_eq_add_one, hexp]; omega
        · rw [Nat.le_sqrt]; nlinarith [ha.1]
      rw [hsq]
    rw [hreindex, hclosed]
  have h2 : ∀ K : ℕ, (∑ n ∈ Finset.Icc 1 ((K+1)^2 - 1),
      (if (n - (Nat.sqrt n)^2) % 3 = 2 then (-1 : ℤ) else 1))
      = ∑ k ∈ Finset.Icc 1 K, (2 * (((k+1)/3 : ℕ) : ℤ) + 1) := by
    intro K
    induction K with
    | zero => decide
    | succ m ih =>
      have hsplit1 : Finset.Icc 1 ((m+1+1)^2 - 1) = Finset.Icc 1 ((m+1)^2 - 1) ∪ Finset.Icc ((m+1)^2) ((m+1+1)^2 - 1) := by
        have he1 : (m+1)^2 = m^2 + 2*m + 1 := by ring
        have he2 : (m+1+1)^2 = m^2 + 4*m + 4 := by ring
        ext x
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hdisj : Disjoint (Finset.Icc 1 ((m+1)^2 - 1)) (Finset.Icc ((m+1)^2) ((m+1+1)^2 - 1)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Icc] at hx1 hx2
        omega
      rw [hsplit1, Finset.sum_union hdisj, ih, Finset.sum_Icc_succ_top (by omega), h1 (m+1)]
  have h3 : (∑ k ∈ Finset.Icc 1 (10^9 - 1 : ℕ), (2 * (((k+1)/3 : ℕ) : ℤ) + 1)) = 333333333999999999 := by
    have hG : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, (2 * (((k+1)/3 : ℕ) : ℤ) + 1))
        = 3*(((N+1)/3 : ℕ):ℤ)^2 + (((N+1)/3:ℕ):ℤ)*(2*(((N+1)%3:ℕ):ℤ) - 1) + (N:ℤ) := by
      intro N
      induction N with
      | zero => decide
      | succ m ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
        rcases h3 with h3 | h3 | h3
        · obtain ⟨t, ht⟩ : ∃ t, m = 3*t := ⟨m/3, by omega⟩
          have e1 : (m+1)/3 = t := by omega
          have e2 : (m+1)%3 = 1 := by omega
          have e3 : (m+1+1)/3 = t := by omega
          have e4 : (m+1+1)%3 = 2 := by omega
          rw [e1, e2, e3, e4]; push_cast; ring
        · obtain ⟨t, ht⟩ : ∃ t, m = 3*t+1 := ⟨m/3, by omega⟩
          have e1 : (m+1)/3 = t := by omega
          have e2 : (m+1)%3 = 2 := by omega
          have e3 : (m+1+1)/3 = t+1 := by omega
          have e4 : (m+1+1)%3 = 0 := by omega
          rw [e1, e2, e3, e4]; push_cast; ring
        · obtain ⟨t, ht⟩ : ∃ t, m = 3*t+2 := ⟨m/3, by omega⟩
          have e1 : (m+1)/3 = t+1 := by omega
          have e2 : (m+1)%3 = 0 := by omega
          have e3 : (m+1+1)/3 = t+1 := by omega
          have e4 : (m+1+1)%3 = 1 := by omega
          rw [e1, e2, e3, e4]; push_cast; ring
    rw [hG]
    norm_num
  have hK : (10^18 - 1 : ℕ) = ((10^9 - 1 : ℕ) + 1)^2 - 1 := by norm_num
  rw [hK, h2 (10^9 - 1), h3]

end Native.Competemath.P160

namespace Native.Competemath.P162

/-- competemath.com problem 162. -/
theorem cyclic_functional_eq_sum (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, x ≠ 0 → x ≠ 1 → f x + f (1 / (1 - x)) = x)
    (N : ℕ) (hN : 2 ≤ N) :
    2 * (N : ℝ) * (∑ n ∈ Finset.Icc 2 N, f (n : ℝ)) =
      (N : ℝ) * (N + 1) * (N + 2) / 2 - 2 * (N : ℝ) - 1 := by
  have h1 : ∀ n ∈ Finset.Icc 2 N, 2 * f (n:ℝ) = (n:ℝ) + 1 + (1/((n:ℝ)-1) - 1/(n:ℝ)) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    have hx1_0 : (n:ℝ) ≠ 0 := by linarith
    have hx1_1 : (n:ℝ) ≠ 1 := by linarith
    have hn1 : (n:ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hx1_1
    have h1n : (1:ℝ) - (n:ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1_1)
    have hx2_0 : (1:ℝ) / (1 - (n:ℝ)) ≠ 0 := one_div_ne_zero h1n
    have hx2_1 : (1:ℝ) / (1 - (n:ℝ)) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq h1n]
      intro h
      linarith
    have h1x2 : (1:ℝ) - (1 / (1 - (n:ℝ))) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx2_1)
    have hx3_0 : (1:ℝ) / (1 - (1 / (1 - (n:ℝ)))) ≠ 0 := one_div_ne_zero h1x2
    have hx3_1 : (1:ℝ) / (1 - (1 / (1 - (n:ℝ)))) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq h1x2]
      intro h
      apply hx2_0
      linarith
    have h1x3 : (1:ℝ) - (1 / (1 - (1 / (1 - (n:ℝ))))) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx3_1)
    have eq1 := hf (n:ℝ) hx1_0 hx1_1
    have eq2 := hf (1 / (1 - (n:ℝ))) hx2_0 hx2_1
    have eq3 := hf (1 / (1 - (1 / (1 - (n:ℝ))))) hx3_0 hx3_1
    have hx3eq : 1 / (1 - (1 / (1 - (1 / (1 - (n:ℝ)))))) = (n:ℝ) := by
      field_simp [h1n, hx1_0, hx2_0, h1x2, hx3_0, h1x3]
      ring
    rw [hx3eq] at eq3
    have key : 2 * f (n:ℝ) = (n:ℝ) - (1 / (1 - (n:ℝ))) + (1 / (1 - (1 / (1 - (n:ℝ))))) := by
      linarith
    rw [key]
    field_simp [h1n, h1x2, hx1_0, hn1]
    ring
  have h2 : 2 * ∑ n ∈ Finset.Icc 2 N, f (n:ℝ) =
      (∑ n ∈ Finset.Icc 2 N, ((n:ℝ)+1)) + (∑ n ∈ Finset.Icc 2 N, (1/((n:ℝ)-1) - 1/(n:ℝ))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl h1
  have h3 : ∑ n ∈ Finset.Icc 2 N, (1/((n:ℝ)-1) - 1/(n:ℝ)) = 1 - 1/(N:ℝ) := by
    clear h1 h2
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1), ih]
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have h1 : (n:ℝ) ≠ 0 := by linarith
      have h2 : (n:ℝ) + 1 ≠ 0 := by linarith
      have e : (↑(n+1):ℝ) - 1 = (n:ℝ) := by push_cast; ring
      rw [e]
      push_cast
      field_simp
      ring
  have h4 : ∑ n ∈ Finset.Icc 2 N, ((n:ℝ)+1) = (N:ℝ)*((N:ℝ)+3)/2 - 2 := by
    clear h1 h2 h3
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        rw [ih]
        ring
  have hNne : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [h3, h4] at h2
  have key : 2 * (N:ℝ) * (∑ n ∈ Finset.Icc 2 N, f (n:ℝ)) = (N:ℝ) * (2 * ∑ n ∈ Finset.Icc 2 N, f (n:ℝ)) := by ring
  rw [key, h2]
  field_simp
  ring

end Native.Competemath.P162

namespace Native.Competemath.P198

/-- competemath.com problem 198. -/
theorem wilson_telescope (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) : (∑ k ∈ Finset.Icc 1 (p - 2), (k ^ 2 + 1) * Nat.factorial k) % p = 2 := by
  haveI := Fact.mk hp
  have key : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (k ^ 2 + 1) * Nat.factorial k = n * Nat.factorial (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Nat.factorial_succ (n + 1)]
      ring
  have hp2 : (p - 2) + 1 = p - 1 := by omega
  rw [key, hp2]
  have hmod : (p - 2) * Nat.factorial (p - 1) ≡ 2 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]
    rw [ZMod.natCast_self, ZMod.wilsons_lemma p]
    ring
  have h2lt : 2 < p := by omega
  calc (p - 2) * Nat.factorial (p - 1) % p = 2 % p := hmod
    _ = 2 := Nat.mod_eq_of_lt h2lt

end Native.Competemath.P198

namespace Native.Competemath.P199

/-- competemath.com problem 199. -/
theorem avg_gcd_pow_two : ∑ k ∈ Finset.Icc 1 (2^2026), Nat.gcd k (2^2026) = 1014 * 2^2026 := by
  have hstep : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 (2^(n+1)), Nat.gcd k (2^(n+1))
      = 2^n + 2 * ∑ k ∈ Finset.Icc 1 (2^n), Nat.gcd k (2^n) := by
        intro n
        have hpow : (2:ℕ)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
        rw [hpow]
        have hunion : Finset.Icc 1 (2 * 2^n) = (Finset.Icc 1 (2^n)).image (fun j => 2*j - 1) ∪ (Finset.Icc 1 (2^n)).image (fun j => 2*j) := by
          ext k
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
          constructor
          · intro hk
            rcases Nat.even_or_odd k with he | ho
            · right
              obtain ⟨j, hj⟩ := he
              exact ⟨j, by omega, by omega⟩
            · left
              obtain ⟨j, hj⟩ := ho
              exact ⟨j+1, by omega, by omega⟩
          · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
        have hdisj : Disjoint ((Finset.Icc 1 (2^n)).image (fun j => 2*j - 1)) ((Finset.Icc 1 (2^n)).image (fun j => 2*j)) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          simp only [Finset.mem_image, Finset.mem_Icc] at ha hb
          obtain ⟨j, hj, hj2⟩ := ha
          obtain ⟨i, hi, hi2⟩ := hb
          omega
        have hinj1 : ∀ x ∈ Finset.Icc 1 (2^n), ∀ y ∈ Finset.Icc 1 (2^n), 2*x - 1 = 2*y - 1 → x = y := by
          intro x hx y hy hxy
          simp only [Finset.mem_Icc] at hx hy
          omega
        have hinj2 : ∀ x ∈ Finset.Icc 1 (2^n), ∀ y ∈ Finset.Icc 1 (2^n), 2*x = 2*y → x = y := by
          intro x hx y hy hxy
          omega
        rw [hunion, Finset.sum_union hdisj, Finset.sum_image hinj1, Finset.sum_image hinj2]
        have ha : ∑ j ∈ Finset.Icc 1 (2^n), Nat.gcd (2*j - 1) (2*2^n) = 2^n := by
          have ha' : ∀ j ∈ Finset.Icc 1 (2^n), Nat.gcd (2*j - 1) (2*2^n) = 1 := by
            intro j hj
            simp only [Finset.mem_Icc] at hj
            have hodd : Odd (2*j - 1) := ⟨j - 1, by omega⟩
            have h2 : (2:ℕ)*2^n = 2^(n+1) := by rw [pow_succ]; ring
            rw [h2]
            have hc : Nat.Coprime (2*j-1) 2 := by
              rcases hodd with ⟨m, hm⟩
              rw [hm]
              exact?
            exact Nat.Coprime.pow_right (n+1) hc
          rw [Finset.sum_congr rfl ha', Finset.sum_const, Nat.card_Icc]
          simp
        have hb : ∑ j ∈ Finset.Icc 1 (2^n), Nat.gcd (2*j) (2*2^n) = 2 * ∑ k ∈ Finset.Icc 1 (2^n), Nat.gcd k (2^n) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          exact Nat.gcd_mul_left 2 j (2^n)
        rw [ha, hb]
  have hgen : ∀ n : ℕ, 2 * ∑ k ∈ Finset.Icc 1 (2^n), Nat.gcd k (2^n) = 2^n * (n + 2) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have hs := hstep n
        rw [hs, pow_succ]
        nlinarith [ih]
  have h2026 := hgen 2026
  omega

end Native.Competemath.P199

namespace Native.Competemath.P200

/-- competemath.com problem 200. -/
theorem gcd_sum_three_pow : (∑ k ∈ Finset.Icc 1 (3^100), Nat.gcd k (3^100)) = 203 * 3^99 := by
  have hBase : 3 * (∑ k ∈ Finset.Icc 1 (3^0), Nat.gcd k (3^0)) = (2*0+3) * 3^0 := by
    decide
  have hStep : ∀ m : ℕ, 3 * (∑ k ∈ Finset.Icc 1 (3^m), Nat.gcd k (3^m)) = (2*m+3) * 3^m →
      3 * (∑ k ∈ Finset.Icc 1 (3^(m+1)), Nat.gcd k (3^(m+1))) = (2*(m+1)+3) * 3^(m+1) := by
        intro m ih
        have aux : ∀ (N : ℕ) (f : ℕ → ℕ),
            ∑ k ∈ Finset.Icc 1 (3*N), f k = ∑ j ∈ Finset.range N, (f (3*j+1) + f (3*j+2) + f (3*j+3)) := by
          intro N f
          induction N with
          | zero => simp
          | succ N ih =>
            rw [Finset.sum_range_succ, ← ih]
            have h1 : 3 * (N+1) = 3*N + 1 + 1 + 1 := by ring
            rw [h1]
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 3*N+1+1+1)]
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 3*N+1+1)]
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 3*N+1)]
            ring_nf
        have stepEq : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 (3^(m+1)), Nat.gcd k (3^(m+1))
              = 3 * (∑ k ∈ Finset.Icc 1 (3^m), Nat.gcd k (3^m)) + 2 * 3^m := by
          intro m
          have h3 : Nat.Prime 3 := by norm_num
          have hpow : (3:ℕ)^(m+1) = 3 * 3^m := by ring
          rw [hpow, aux (3^m) (fun k => Nat.gcd k (3*3^m))]
          have hterm : ∀ j ∈ Finset.range (3^m),
              Nat.gcd (3*j+1) (3*3^m) + Nat.gcd (3*j+2) (3*3^m) + Nat.gcd (3*j+3) (3*3^m)
                = 2 + 3 * Nat.gcd (j+1) (3^m) := by
            intro j _
            have hc1 : Nat.Coprime (3*j+1) 3 := by
              rw [Nat.coprime_comm, h3.coprime_iff_not_dvd]; omega
            have hc2 : Nat.Coprime (3*j+2) 3 := by
              rw [Nat.coprime_comm, h3.coprime_iff_not_dvd]; omega
            have e1 : Nat.gcd (3*j+1) (3*3^m) = 1 := by
              have h := hc1.pow_right (m+1)
              rw [hpow] at h
              exact h
            have e2 : Nat.gcd (3*j+2) (3*3^m) = 1 := by
              have h := hc2.pow_right (m+1)
              rw [hpow] at h
              exact h
            have e3 : Nat.gcd (3*j+3) (3*3^m) = 3 * Nat.gcd (j+1) (3^m) := by
              have e1' : 3*j+3 = 3*(j+1) := by ring
              rw [e1', Nat.gcd_mul_left]
            rw [e1, e2, e3]
          rw [Finset.sum_congr rfl hterm]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
          have hshift : ∑ j ∈ Finset.range (3^m), Nat.gcd (j+1) (3^m)
              = ∑ k ∈ Finset.Icc 1 (3^m), Nat.gcd k (3^m) := by
            rw [show Finset.Icc 1 (3^m) = Finset.Ico 1 (3^m+1) from by
              ext x; simp [Finset.mem_Icc, Finset.mem_Ico]]
            rw [Finset.sum_Ico_eq_sum_range]
            simp [add_comm]
          rw [hshift]
          ring
        rw [stepEq m]
        have h33 : (3:ℕ)^(m+1) = 3*3^m := by ring
        rw [h33]
        nlinarith [ih]
  have hAll : ∀ m : ℕ, 3 * (∑ k ∈ Finset.Icc 1 (3^m), Nat.gcd k (3^m)) = (2*m+3) * 3^m := by
    intro m
    induction m with
    | zero => exact hBase
    | succ m ih => exact hStep m ih
  have hFinal := hAll 100
  have hEq : (2*100+3) * 3^100 = 3 * (203 * 3^99) := by ring
  rw [hEq] at hFinal
  omega

end Native.Competemath.P200

namespace Native.Competemath.P203

/-- competemath.com problem 203. -/
theorem central_binomial_two_adic_valuation (m : ℕ) : (Nat.choose (2 * m) m).factorization 2 = (Nat.digits 2 m).sum := by
  have hle : m ≤ 2 * m := by omega
  have hkummer := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) hle
  simp only [show 2 * m - m = m by omega] at hkummer
  have hdig : (Nat.digits 2 (2 * m)).sum = (Nat.digits 2 m).sum := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · rw [Nat.digits_def' (by norm_num) (by positivity)]
      simp
  rw [Nat.factorization_def _ Nat.prime_two]
  omega

end Native.Competemath.P203

namespace Native.Competemath.P208

/-- competemath.com problem 208. -/
theorem giant_alternating_sum_eq_one (n : ℕ) :
    ((n + 1 : ℚ) * (Nat.choose (2 * n + 1) n : ℚ)) *
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) / (k + n + 1)) = 1 := by
  have h1 : ∀ (m : ℕ) (x : ℚ), (∀ i ∈ Finset.range (m + 1), x + (i:ℚ) ≠ 0) →
      (∑ k ∈ Finset.range (m + 1), (-1:ℚ) ^ k * (Nat.choose m k : ℚ) / (x + (k:ℚ)))
        * (∏ i ∈ Finset.range (m + 1), (x + (i:ℚ))) = (Nat.factorial m : ℚ) := by
          have hrec : ∀ (m : ℕ) (y : ℚ),
              ∑ k ∈ Finset.range (m+2), (-1:ℚ)^k * (Nat.choose (m+1) k :ℚ)/(y+k)
              = (∑ k ∈ Finset.range (m+1), (-1:ℚ)^k*(Nat.choose m k:ℚ)/(y+k)) - (∑ k ∈ Finset.range (m+1), (-1:ℚ)^k*(Nat.choose m k:ℚ)/(y+1+k)) := by
            intro m y
            rw [Finset.sum_range_succ' (fun k => (-1:ℚ) ^ k * ((m+1).choose k : ℚ) / (y + (k:ℚ))) (m+1)]
            simp only [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, pow_succ, pow_zero, mul_one]
            have expand : ∀ x ∈ Finset.range (m+1), (-1:ℚ)^x * -1 * (↑(m.choose x) + ↑(m.choose x.succ)) / (y + (↑x+1))
             = - ((-1:ℚ)^x * ↑(m.choose x) / (y+1+↑x)) - ((-1:ℚ)^x * ↑(m.choose x.succ) / (y+1+↑x)) := by
              intro x _
              have hxy : y + ((x:ℚ)+1) = y+1+(x:ℚ) := by ring
              rw [hxy]
              ring
            rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib]
            rw [Finset.sum_neg_distrib]
            have hz : (Nat.choose m (m+1) : ℚ) = 0 := by
              have h0 : m.choose (m+1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)
              exact_mod_cast h0
            have step1 := Finset.sum_range_succ' (fun j => (-1:ℚ)^j * (Nat.choose m j:ℚ)/(y+(j:ℚ))) (m+1)
            have step2 := Finset.sum_range_succ (fun k => (-1:ℚ)^k * (Nat.choose m k:ℚ)/(y+(k:ℚ))) (m+1)
            have e := step1.symm.trans step2
            rw [hz] at e
            simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.cast_zero, add_zero, mul_zero, zero_div] at e
            have e2 : ∑ k ∈ Finset.range (m+1), (-1:ℚ)^(k+1) * (Nat.choose m (k+1):ℚ)/(y+((k:ℚ)+1))
                = - ∑ x ∈ Finset.range (m+1), (-1:ℚ)^x * (Nat.choose m x.succ:ℚ)/(y+1+(x:ℚ)) := by
              have term_eq : ∀ k ∈ Finset.range (m+1), (-1:ℚ)^(k+1) * (Nat.choose m (k+1):ℚ)/(y+((k:ℚ)+1))
                  = -((-1:ℚ)^k * (Nat.choose m k.succ:ℚ)/(y+1+(k:ℚ))) := by
                intro k _
                rw [show y + ((k:ℚ)+1) = y+1+(k:ℚ) from by ring]
                ring
              rw [Finset.sum_congr rfl term_eq, Finset.sum_neg_distrib]
            push_cast at e
            rw [e2] at e
            linarith [e]
          intro m
          induction m with
          | zero =>
            intro x hx
            have hx0 : x ≠ 0 := by simpa using hx 0 (by simp)
            simp [hx0]
          | succ m ih =>
            intro x hx
            have hx' : ∀ i ∈ Finset.range (m + 1), x + (i:ℚ) ≠ 0 := by
              intro i hi
              exact hx i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
            have hx1' : ∀ i ∈ Finset.range (m + 1), (x+1) + (i:ℚ) ≠ 0 := by
              intro i hi
              have hi' : i+1 ∈ Finset.range (m+1+1) := by
                have := Finset.mem_range.mp hi
                exact Finset.mem_range.mpr (by omega)
              have hne := hx (i+1) hi'
              intro hcontra
              apply hne
              push_cast
              linarith [hcontra]
            have e1 := ih x hx'
            have e2 := ih (x+1) hx1'
            have hr := hrec m x
            have hp1 : (∏ i ∈ Finset.range (m+1+1), (x+(i:ℚ))) = (∏ i ∈ Finset.range (m+1), (x+(i:ℚ))) * (x+((m:ℚ)+1)) := by
              rw [Finset.prod_range_succ]
              push_cast
              ring
            have hp2 : (∏ i ∈ Finset.range (m+1+1), (x+(i:ℚ))) = x * (∏ i ∈ Finset.range (m+1), ((x+1)+(i:ℚ))) := by
              rw [Finset.prod_range_succ' (fun i => x+(i:ℚ)) (m+1)]
              simp only [Nat.cast_zero, add_zero]
              rw [mul_comm]
              congr 1
              apply Finset.prod_congr rfl
              intro i _
              push_cast
              ring
            have hpp := hp1.symm.trans hp2
            have hfact : ((m+1).factorial:ℚ) = ((m:ℚ)+1) * (m.factorial:ℚ) := by
              exact_mod_cast Nat.factorial_succ m
            show (∑ k ∈ Finset.range (m+1+1), (-1:ℚ)^k * (Nat.choose (m+1) k :ℚ)/(x+k)) * (∏ i ∈ Finset.range (m+1+1), (x+(i:ℚ))) = ((m+1).factorial:ℚ)
            rw [hr, hfact, hp1]
            linear_combination (x+(m:ℚ)+1)*e1 - x*e2 - (∑ k ∈ Finset.range (m + 1), (-1:ℚ) ^ k * (Nat.choose m k : ℚ) / (x + 1 + (k:ℚ))) * hpp
  have h2 : (∏ i ∈ Finset.range (n + 1), ((n:ℚ) + 1 + (i:ℚ))) =
      (Nat.choose (2 * n + 1) n : ℚ) * (Nat.factorial (n + 1) : ℚ) := by
        have hAsc : ∀ (a k : ℕ), Nat.ascFactorial a k = ∏ i ∈ Finset.range k, (a + i) := by
          intro a k
          induction k with
          | zero => simp [Nat.ascFactorial]
          | succ k ih => rw [Nat.ascFactorial_succ, Finset.prod_range_succ, ih, mul_comm]
        have hstep : Nat.ascFactorial (n+1) (n+1) = (n+1).factorial * (2*n+1).choose (n+1) := by
          have := Nat.ascFactorial_eq_factorial_mul_choose n (n+1)
          simpa [show n + (n+1) = 2*n+1 from by ring] using this
        have hsymm : (2*n+1).choose (n+1) = (2*n+1).choose n := by
          have h := Nat.choose_symm (show n+1 ≤ 2*n+1 from by omega)
          simpa [show 2*n+1-(n+1) = n from by omega] using h.symm
        have hNat : (∏ i ∈ Finset.range (n + 1), (n+1+i)) = (2*n+1).choose n * (n+1).factorial := by
          rw [← hAsc (n+1) (n+1), hstep, hsymm, mul_comm]
        have hcast : ((∏ i ∈ Finset.range (n + 1), (n+1+i) : ℕ) : ℚ) = (((2*n+1).choose n * (n+1).factorial : ℕ) : ℚ) := by
          exact_mod_cast hNat
        push_cast at hcast
        convert hcast using 2
  have hx : ∀ i ∈ Finset.range (n + 1), ((n:ℚ) + 1) + (i:ℚ) ≠ 0 := by
    intro i _
    positivity
  have e1 := h1 n ((n:ℚ) + 1) hx
  have hsum_eq : (∑ k ∈ Finset.range (n + 1), (-1:ℚ) ^ k * (Nat.choose n k : ℚ) / (((n:ℚ) + 1) + (k:ℚ)))
      = (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) / ((k:ℚ) + n + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show ((n:ℚ) + 1) + (k:ℚ) = (k:ℚ) + n + 1 from by ring]
  rw [hsum_eq, h2] at e1
  have hFp1 : (Nat.factorial (n+1) : ℚ) = ((n:ℚ) + 1) * (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.factorial_succ n
  have hF0 : (Nat.factorial n : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [hFp1] at e1
  have goal_mul : (((n:ℚ)+1) * (Nat.choose (2*n+1) n : ℚ) *
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) / ((k:ℚ) + n + 1))) * (Nat.factorial n:ℚ)
      = 1 * (Nat.factorial n : ℚ) := by
    rw [one_mul]
    linear_combination e1
  exact mul_right_cancel₀ hF0 goal_mul

end Native.Competemath.P208

namespace Native.Competemath.P99

/-- competemath.com problem 99. -/
theorem stamp_drawer : (Finset.filter (fun p : Fin 11 × Fin 5 => 2 * (p.1 : ℕ) + 5 * (p.2 : ℕ) = 20) Finset.univ).card = 3 := by decide

end Native.Competemath.P99

namespace Native.Competemath.P221

open Classical in
/-- competemath.com problem 221. -/
theorem twin_quadratic_residues_count
    (p : ℕ) (hp : p = 2^127 - 1) (hprime : Nat.Prime p) :
    ((Finset.Icc 1 (p - 2)).filter
      (fun a : ℕ => IsSquare (a : ZMod p) ∧ IsSquare ((a + 1 : ℕ) : ZMod p))).card
      = 2^125 - 1 := by
  set S := (Finset.Icc 1 (p - 2)).filter
      (fun a : ℕ => IsSquare (a : ZMod p) ∧ IsSquare ((a + 1 : ℕ) : ZMod p)) with hS_def
  haveI : Fact (Nat.Prime p) := ⟨hprime⟩
  haveI : NeZero p := ⟨hprime.pos.ne'⟩
  have h1 : p % 4 = 3 := by
    subst hp
    norm_num
  have h2 : quadraticChar (ZMod p) (-1) = -1 := by
    have hne2 : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    rw [quadraticChar_neg_one hne2, ZMod.card p]
    exact_mod_cast ZMod.χ₄_int_three_mod_four (n := (p : ℤ)) (by exact_mod_cast h1)
  have h3 : (∑ x : ZMod p, quadraticChar (ZMod p) x) = 0 := by
    apply quadraticChar_sum_zero
    rw [ZMod.ringChar_zmod_n]
    omega
  have h4 : (∑ x : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1)) = -1 := by
    have key : ∀ x : ZMod p, x ≠ 0 → quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1) = quadraticChar (ZMod p) (1 + x⁻¹) := by
      intro x hx
      have hxeq : x + 1 = x * (1 + x⁻¹) := by
        field_simp
      rw [hxeq, map_mul]
      have hsq : quadraticChar (ZMod p) x * quadraticChar (ZMod p) x = 1 := by
        rcases quadraticChar_dichotomy (F := ZMod p) hx with h | h <;> rw [h] <;> ring
      calc quadraticChar (ZMod p) x * (quadraticChar (ZMod p) x * quadraticChar (ZMod p) (1 + x⁻¹))
          = (quadraticChar (ZMod p) x * quadraticChar (ZMod p) x) * quadraticChar (ZMod p) (1 + x⁻¹) := by ring
        _ = quadraticChar (ZMod p) (1 + x⁻¹) := by rw [hsq]; ring
    have hf0 : quadraticChar (ZMod p) 0 * quadraticChar (ZMod p) (0 + 1) = 0 := by simp
    have split : (∑ x : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1))
        = ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1) := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (0 : ZMod p))]
      rw [hf0]
      ring
    rw [split]
    have main : ∑ x ∈ (Finset.univ.erase (0 : ZMod p)), quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x + 1)
        = ∑ z ∈ (Finset.univ.erase (1 : ZMod p)), quadraticChar (ZMod p) z := by
      apply Finset.sum_nbij' (fun x => 1 + x⁻¹) (fun z => (z - 1)⁻¹)
      · intro x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx ⊢
        intro hcontra
        apply hx
        have : x⁻¹ = 0 := by linear_combination hcontra
        exact inv_eq_zero.mp this
      · intro z hz
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz ⊢
        exact inv_ne_zero (sub_ne_zero.mpr hz)
      · intro x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
        field_simp
        ring
      · intro z hz
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
        field_simp
        ring
      · intro x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
        exact key x hx
    rw [main]
    have hsum1 : ∑ z ∈ (Finset.univ.erase (1 : ZMod p)), quadraticChar (ZMod p) z + quadraticChar (ZMod p) 1
        = ∑ z : ZMod p, quadraticChar (ZMod p) z := Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (1 : ZMod p))
    rw [h3] at hsum1
    have hχ1 : quadraticChar (ZMod p) 1 = 1 := map_one _
    rw [hχ1] at hsum1
    linarith [hsum1]
  have h5 : S.card = (p - 3) / 4 := by
    have s1 : S.card = ((Finset.univ : Finset (ZMod p)).filter
        (fun x => x ≠ 0 ∧ x ≠ -1 ∧ IsSquare x ∧ IsSquare (x + 1))).card := by
          clear hp
          have hS_def2 : S = (Finset.Icc 1 (p - 2)).filter
              (fun a : ℕ => IsSquare (a : ZMod p) ∧ IsSquare ((a + 1 : ℕ) : ZMod p)) :=
            hS_def.trans (Finset.filter_congr_decidable (Finset.Icc 1 (p - 2))
              (fun a : ℕ => IsSquare (a : ZMod p) ∧ IsSquare ((a + 1 : ℕ) : ZMod p)) _)
          rw [hS_def2]
          refine Finset.card_bij (fun (a : ℕ) (_ : a ∈ (Finset.Icc 1 (p - 2)).filter
              (fun a : ℕ => IsSquare (a : ZMod p) ∧ IsSquare ((a + 1 : ℕ) : ZMod p))) => (a : ZMod p)) ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_Icc] at ha
            obtain ⟨⟨ha1, ha2⟩, hsq1, hsq2⟩ := ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hane0 : (a : ZMod p) ≠ 0 := by
              intro hc
              have hv : (a : ZMod p).val = a := ZMod.val_cast_of_lt (by omega)
              rw [hc, ZMod.val_zero] at hv
              omega
            have haneneg1 : (a : ZMod p) ≠ -1 := by
              intro hc
              have heq0 : ((a + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hc]; ring
              have hv : ((a + 1 : ℕ) : ZMod p).val = a + 1 := ZMod.val_cast_of_lt (by omega)
              rw [heq0, ZMod.val_zero] at hv
              omega
            refine ⟨hane0, haneneg1, hsq1, ?_⟩
            have hcast : ((a + 1 : ℕ) : ZMod p) = (a : ZMod p) + 1 := by push_cast; ring
            rwa [hcast] at hsq2
          · intro a1 ha1 a2 ha2 heq
            simp only [Finset.mem_filter, Finset.mem_Icc] at ha1 ha2
            have heq' : (a1 : ZMod p) = (a2 : ZMod p) := heq
            have v1 : (a1 : ZMod p).val = a1 := ZMod.val_cast_of_lt (by omega)
            have v2 : (a2 : ZMod p).val = a2 := ZMod.val_cast_of_lt (by omega)
            rw [heq'] at v1
            omega
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            obtain ⟨hx0, hxneg1, hsq1, hsq2⟩ := hx
            have hri : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse (n := p) x
            have hlt : x.val < p := ZMod.val_lt x
            have hvne0 : x.val ≠ 0 := by
              intro hc
              apply hx0
              rw [hc] at hri
              simpa using hri.symm
            have hvnep1 : x.val ≠ p - 1 := by
              intro hc
              apply hxneg1
              rw [hc] at hri
              rw [← hri]
              have hcast : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
                have heqp : (p - 1) + 1 = p := by
                  have := (Fact.out (p := Nat.Prime p)).two_le
                  omega
                calc ((p - 1 : ℕ) : ZMod p) + 1 = (((p-1)+1 : ℕ) : ZMod p) := by push_cast; ring
                  _ = (p : ZMod p) := by rw [heqp]
                  _ = 0 := ZMod.natCast_self p
              linear_combination hcast
            refine ⟨x.val, ?_, hri⟩
            simp only [Finset.mem_filter, Finset.mem_Icc]
            have hcast2 : ((x.val + 1 : ℕ) : ZMod p) = (x.val : ZMod p) + 1 := by push_cast; ring
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
            · omega
            · omega
            · rw [hri]; exact hsq1
            · rw [hcast2, hri]; exact hsq2
    have s2 : ((Finset.univ : Finset (ZMod p)).filter
        (fun x => x ≠ 0 ∧ x ≠ -1 ∧ IsSquare x ∧ IsSquare (x + 1))).card = (p - 3) / 4 := by
      set χ := quadraticChar (ZMod p) with hχ_def
      set T' := (Finset.univ : Finset (ZMod p)).filter (fun x => x ≠ 0 ∧ x ≠ -1) with hT'_def
      set T := (Finset.univ : Finset (ZMod p)).filter
        (fun x => x ≠ 0 ∧ x ≠ -1 ∧ IsSquare x ∧ IsSquare (x + 1)) with hT_def
      have hne : (-1 : ZMod p) ≠ 0 := by
        intro hc
        have : (1 : ZMod p) = 0 := by linear_combination -hc
        exact one_ne_zero this
      have hT'eq : T' = (Finset.univ.erase (0 : ZMod p)).erase (-1) := by
        rw [hT'_def]
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        tauto
      have hT'card : T'.card = p - 2 := by
        rw [hT'eq]
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)]
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        rw [Finset.card_univ, ZMod.card p]
        have hpge : 2 ≤ p := hprime.two_le
        omega
      have hTfilter : T = T'.filter (fun x => IsSquare x ∧ IsSquare (x + 1)) := by
        rw [hT_def, hT'_def, Finset.filter_filter]
        congr 1
        ext x
        tauto
      have hcond : ∀ x ∈ T', (1 + χ x) * (1 + χ (x + 1)) =
          if IsSquare x ∧ IsSquare (x + 1) then (4:ℤ) else 0 := by
        intro x hx
        rw [hT'_def, Finset.mem_filter] at hx
        obtain ⟨-, hx0, hxm1⟩ := hx
        have hx1 : x + 1 ≠ 0 := by intro hc; apply hxm1; linear_combination hc
        rcases quadraticChar_dichotomy (F := ZMod p) hx0 with h1' | h1' <;>
          rcases quadraticChar_dichotomy (F := ZMod p) hx1 with h2' | h2' <;>
          rw [h1', h2']
        · rw [if_pos ⟨(quadraticChar_one_iff_isSquare hx0).mp h1', (quadraticChar_one_iff_isSquare hx1).mp h2'⟩]
          norm_num
        · rw [if_neg (by
            intro hc
            exact (quadraticChar_neg_one_iff_not_isSquare (a := x + 1)).mp h2' hc.2)]
          norm_num
        · rw [if_neg (by
            intro hc
            exact (quadraticChar_neg_one_iff_not_isSquare (a := x)).mp h1' hc.1)]
          norm_num
        · rw [if_neg (by
            intro hc
            exact (quadraticChar_neg_one_iff_not_isSquare (a := x)).mp h1' hc.1)]
          norm_num
      have hstep1 : ∑ x ∈ T', (1 + χ x) * (1 + χ (x + 1))
          = ∑ x ∈ T', (if IsSquare x ∧ IsSquare (x + 1) then (4:ℤ) else 0) :=
        Finset.sum_congr rfl hcond
      have hstep2 : ∑ x ∈ T', (if IsSquare x ∧ IsSquare (x + 1) then (4:ℤ) else 0)
          = 4 * ∑ x ∈ T', (if IsSquare x ∧ IsSquare (x + 1) then (1:ℤ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      have hstep3 : ∑ x ∈ T', (if IsSquare x ∧ IsSquare (x + 1) then (1:ℤ) else 0)
          = ((T'.filter (fun x => IsSquare x ∧ IsSquare (x + 1))).card : ℤ) :=
        Finset.sum_boole _ _
      have hLHS_eq : ∑ x ∈ T', (1 + χ x) * (1 + χ (x + 1)) = 4 * (T.card : ℤ) := by
        rw [hstep1, hstep2, hstep3, ← hTfilter]
      have herase : ∀ f : ZMod p → ℤ, ∑ x ∈ T', f x = (∑ x : ZMod p, f x) - f 0 - f (-1) := by
        intro f
        rw [hT'eq]
        have e1 : ∑ x ∈ (Finset.univ.erase (0:ZMod p)).erase (-1), f x + f (-1)
            = ∑ x ∈ Finset.univ.erase (0:ZMod p), f x :=
          Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
        have e2 : ∑ x ∈ Finset.univ.erase (0:ZMod p), f x + f 0 = ∑ x : ZMod p, f x :=
          Finset.sum_erase_add _ _ (Finset.mem_univ _)
        linarith [e1, e2]
      have hRHS_expand : ∑ x ∈ T', (1 + χ x) * (1 + χ (x + 1))
          = (T'.card : ℤ) + (∑ x ∈ T', χ x) + (∑ x ∈ T', χ (x + 1)) + (∑ x ∈ T', χ x * χ (x + 1)) := by
        have expand : ∑ x ∈ T', (1 + χ x) * (1 + χ (x + 1))
            = ∑ x ∈ T', ((1:ℤ) + χ x + χ (x+1) + χ x * χ (x+1)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [expand, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      have hsumχ : ∑ x ∈ T', χ x = 1 := by
        rw [herase χ, h3, hχ_def, quadraticChar_zero, h2]
        ring
      have hsumχ1 : ∑ x ∈ T', χ (x + 1) = -1 := by
        rw [herase (fun x => χ (x+1))]
        have hreindex : (∑ x : ZMod p, χ (x + 1)) = ∑ y : ZMod p, χ y := by
          rw [hχ_def]
          apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod p))
          intro x
          simp [Equiv.addRight]
        simp only [hreindex, h3]
        have e1 : (0:ZMod p) + 1 = 1 := by ring
        rw [e1]
        have hχ1 : χ 1 = 1 := by rw [hχ_def]; exact map_one _
        rw [hχ1]
        have hm1 : (-1:ZMod p) + 1 = 0 := by ring
        rw [hm1]
        have hχ0 : χ (0:ZMod p) = 0 := by rw [hχ_def]; exact quadraticChar_zero
        rw [hχ0]
        ring
      have hsumχχ : ∑ x ∈ T', χ x * χ (x + 1) = -1 := by
        rw [herase (fun x => χ x * χ (x+1)), h4]
        have e0 : (0:ZMod p) + 1 = 1 := by ring
        rw [e0]
        have hχ0 : χ (0:ZMod p) = 0 := by rw [hχ_def]; exact quadraticChar_zero
        have hχ1 : χ (1:ZMod p) = 1 := by rw [hχ_def]; exact map_one _
        have hm1 : (-1:ZMod p) + 1 = 0 := by ring
        rw [hm1, hχ0, hχ1]
        ring
      rw [hLHS_eq] at hRHS_expand
      rw [hsumχ, hsumχ1, hsumχχ, hT'card] at hRHS_expand
      have hpge3 : 3 ≤ p := by omega
      have hcast : ((p - 2 : ℕ) : ℤ) = (p:ℤ) - 2 := by
        have h2le : 2 ≤ p := by omega
        push_cast [Nat.cast_sub h2le]
        ring
      rw [hcast] at hRHS_expand
      have hfinal : 4 * (T.card : ℤ) = (p:ℤ) - 3 := by linarith [hRHS_expand]
      have hnat : 4 * T.card = p - 3 := by
        have h3le : 3 ≤ p := hpge3
        omega
      omega
    exact s1.trans s2
  rw [h5, hp]
  norm_num

end Native.Competemath.P221

namespace Native.Competemath.P226

/-- competemath.com problem 226. -/
theorem telescoping_reciprocal_product (m : ℕ) (hm : 0 < m) :
    (∑' n : ℕ, (1:ℝ) / ∏ i ∈ Finset.range (m+1), ((n:ℝ) + 1 + (i:ℝ))) = 1 / ((m : ℝ) * (Nat.factorial m : ℝ)) ∧
    (2025 : ℝ) * (Nat.factorial 2025 : ℝ) * (∑' n : ℕ, (1:ℝ) / ∏ i ∈ Finset.range 2026, ((n:ℝ) + 1 + (i:ℝ))) = 1 := by
  have key : ∀ k : ℕ, 0 < k →
      (∑' n : ℕ, (1:ℝ) / ∏ i ∈ Finset.range (k+1), ((n:ℝ) + 1 + (i:ℝ))) = 1 / ((k : ℝ) * (Nat.factorial k : ℝ)) := by
    intro k hk
    have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    have hQpos : ∀ n : ℕ, 0 < ∏ i ∈ Finset.range k, ((n:ℝ) + 1 + (i:ℝ)) := by
      intro n
      apply Finset.prod_pos
      intro i _
      positivity
    have hfactor1 : ∀ n : ℕ, (∏ i ∈ Finset.range (k+1), ((n:ℝ)+1+(i:ℝ)))
        = (∏ i ∈ Finset.range k, ((n:ℝ) + 1 + (i:ℝ))) * ((n:ℝ)+1+(k:ℝ)) := by
      intro n
      rw [Finset.prod_range_succ]
    have hfactor2 : ∀ n : ℕ, (∏ i ∈ Finset.range (k+1), ((n:ℝ)+1+(i:ℝ)))
        = ((n:ℝ)+1) * (∏ i ∈ Finset.range k, (((n+1 : ℕ):ℝ) + 1 + (i:ℝ))) := by
      intro n
      rw [Finset.prod_range_succ']
      push_cast
      ring_nf
    have hrel : ∀ n : ℕ, (∏ i ∈ Finset.range k, ((n:ℝ) + 1 + (i:ℝ))) * ((n:ℝ)+1+(k:ℝ))
        = ((n:ℝ)+1) * (∏ i ∈ Finset.range k, (((n+1 : ℕ):ℝ) + 1 + (i:ℝ))) := by
      intro n
      rw [← hfactor1 n, ← hfactor2 n]
    have hid : ∀ n : ℕ, (1:ℝ) / (∏ i ∈ Finset.range (k+1), ((n:ℝ)+1+(i:ℝ)))
        = (1/(k:ℝ)) * (1/(∏ i ∈ Finset.range k, ((n:ℝ) + 1 + (i:ℝ))) - 1/(∏ i ∈ Finset.range k, (((n+1 : ℕ):ℝ) + 1 + (i:ℝ)))) := by
      intro n
      rw [hfactor1 n]
      have h1 : (∏ i ∈ Finset.range k, ((n:ℝ) + 1 + (i:ℝ))) ≠ 0 := (hQpos n).ne'
      have h2 : (∏ i ∈ Finset.range k, (((n+1 : ℕ):ℝ) + 1 + (i:ℝ))) ≠ 0 := (hQpos (n+1)).ne'
      have hnk : (n:ℝ)+1+(k:ℝ) ≠ 0 := by positivity
      field_simp
      linear_combination hrel n
    have hfact : ∀ j : ℕ, (∏ i ∈ Finset.range j, ((i:ℝ)+1)) = (Nat.factorial j : ℝ) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring
    have hQ0 : (∏ i ∈ Finset.range k, (((0:ℕ):ℝ) + 1 + (i:ℝ))) = (Nat.factorial k : ℝ) := by
      have heq : (∏ i ∈ Finset.range k, (((0:ℕ):ℝ) + 1 + (i:ℝ))) = ∏ i ∈ Finset.range k, ((i:ℝ)+1) := by
        apply Finset.prod_congr rfl; intro i _; push_cast; ring
      rw [heq, hfact k]
    have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1:ℝ)/(∏ j ∈ Finset.range (k+1), ((i:ℝ)+1+(j:ℝ)))
        = (1/(k:ℝ)) * ((1/(∏ j ∈ Finset.range k, (((0:ℕ):ℝ)+1+(j:ℝ)))) - (1/(∏ j ∈ Finset.range k, ((N:ℝ)+1+(j:ℝ))))) := by
      intro N
      have step : ∑ i ∈ Finset.range N, (1:ℝ)/(∏ j ∈ Finset.range (k+1), ((i:ℝ)+1+(j:ℝ)))
          = ∑ i ∈ Finset.range N, ((fun m : ℕ => (1/(k:ℝ)) * (1/(∏ j ∈ Finset.range k, ((m:ℝ)+1+(j:ℝ)))))
              i - (fun m : ℕ => (1/(k:ℝ)) * (1/(∏ j ∈ Finset.range k, ((m:ℝ)+1+(j:ℝ))))) (i+1)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only
        rw [hid i]
        ring
      rw [step]
      rw [Finset.sum_range_sub' (fun m : ℕ => (1/(k:ℝ)) * (1/(∏ j ∈ Finset.range k, ((m:ℝ)+1+(j:ℝ)))))]
      push_cast
      ring
    have hfnonneg : ∀ n : ℕ, 0 ≤ (1:ℝ)/(∏ i ∈ Finset.range (k+1), ((n:ℝ)+1+(i:ℝ))) := by
      intro n
      apply le_of_lt
      apply div_pos one_pos
      apply Finset.prod_pos
      intro i _
      positivity
    have hbound : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1:ℝ)/(∏ j ∈ Finset.range (k+1), ((i:ℝ)+1+(j:ℝ)))
        ≤ (1/(k:ℝ)) * (1/(∏ j ∈ Finset.range k, (((0:ℕ):ℝ)+1+(j:ℝ)))) := by
      intro N
      rw [hpartial N]
      have hgN : 0 ≤ 1/(∏ j ∈ Finset.range k, ((N:ℝ)+1+(j:ℝ))) := by
        apply le_of_lt; apply div_pos one_pos (hQpos N)
      have hkpos' : (0:ℝ) ≤ 1/(k:ℝ) := le_of_lt (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left (sub_le_self (1/(∏ j ∈ Finset.range k, (((0:ℕ):ℝ)+1+(j:ℝ)))) hgN) hkpos']
    have hSummable : Summable (fun n : ℕ => (1:ℝ)/(∏ i ∈ Finset.range (k+1), ((n:ℝ)+1+(i:ℝ)))) :=
      summable_of_sum_range_le hfnonneg hbound
    have hHasSum := hSummable.hasSum
    have htendsto1 : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, (1:ℝ)/(∏ j ∈ Finset.range (k+1), ((i:ℝ)+1+(j:ℝ)))) Filter.atTop
        (nhds (∑' n : ℕ, (1:ℝ) / ∏ i ∈ Finset.range (k+1), ((n:ℝ) + 1 + (i:ℝ)))) := hHasSum.tendsto_sum_nat
    have hQge : ∀ N : ℕ, ((N:ℝ)+1) ≤ ∏ i ∈ Finset.range k, ((N:ℝ) + 1 + (i:ℝ)) := by
      intro N
      have h1 : (∏ i ∈ Finset.range k, ((N:ℝ)+1)) ≤ ∏ i ∈ Finset.range k, ((N:ℝ) + 1 + (i:ℝ)) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; have : (0:ℝ) ≤ i := Nat.cast_nonneg i; linarith
      rw [Finset.prod_const] at h1
      have h2 : ((N:ℝ)+1)^1 ≤ ((N:ℝ)+1)^k := by
        apply pow_le_pow_right₀ (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith) hk
      simp only [pow_one] at h2
      rw [Finset.card_range] at h1
      linarith
    have hgtendsto : Filter.Tendsto (fun N : ℕ => 1/(∏ j ∈ Finset.range k, ((N:ℝ)+1+(j:ℝ)))) Filter.atTop (nhds 0) := by
      have hle : ∀ N : ℕ, (1:ℝ)/(∏ j ∈ Finset.range k, ((N:ℝ)+1+(j:ℝ))) ≤ 1/((N:ℝ)+1) := by
        intro N
        have h0 : (0:ℝ) < (N:ℝ)+1 := by positivity
        exact one_div_le_one_div_of_le h0 (hQge N)
      have hge : ∀ N : ℕ, (0:ℝ) ≤ 1/(∏ j ∈ Finset.range k, ((N:ℝ)+1+(j:ℝ))) := by
        intro N
        exact le_of_lt (div_pos one_pos (hQpos N))
      exact squeeze_zero hge hle tendsto_one_div_add_atTop_nhds_zero_nat
    have htendsto2 : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, (1:ℝ)/(∏ j ∈ Finset.range (k+1), ((i:ℝ)+1+(j:ℝ)))) Filter.atTop
        (nhds ((1/(k:ℝ)) * ((1/(∏ j ∈ Finset.range k, (((0:ℕ):ℝ)+1+(j:ℝ)))) - 0))) := by
      apply Filter.Tendsto.congr (fun N => (hpartial N).symm)
      apply Filter.Tendsto.const_mul
      apply Filter.Tendsto.const_sub
      exact hgtendsto
    have hfinal := tendsto_nhds_unique htendsto1 htendsto2
    rw [hfinal, hQ0]
    have hfacne : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    field_simp
    ring
  refine ⟨key m hm, ?_⟩
  have e : (2026:ℕ) = 2025 + 1 := by norm_num
  rw [e, key 2025 (by norm_num)]
  have hfac_pos : (Nat.factorial 2025 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos 2025).ne'
  field_simp
  norm_num

end Native.Competemath.P226

namespace Native.Competemath.P236

/-- competemath.com problem 236. -/
theorem chip_pass_count (N : ℕ) : (∑ k ∈ Finset.range (N + 1), N.choose k * Nat.choose 30 15 ^ k) = (Nat.choose 30 15 + 1) ^ N := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Nat.cast_id, mul_comm]

end Native.Competemath.P236

namespace Native.Competemath.P61

/-- competemath.com problem 61. -/
theorem gcd_sum_prime_power (p n : ℕ) (hp : Nat.Prime p) (hn : 1 ≤ n) : (∑ k ∈ Finset.Icc 1 (p ^ n), Nat.gcd k (p ^ n)) = p ^ (n - 1) * (n * (p - 1) + p) := by
  have hp0 : 0 < p := hp.pos
  have base0 : (∑ k ∈ Finset.Icc 1 (p ^ 0), Nat.gcd k (p ^ 0)) = 1 := by simp
  have step : ∀ j : ℕ, (∑ k ∈ Finset.Icc 1 (p ^ (j+1)), Nat.gcd k (p ^ (j+1)))
      = p ^ j * (p - 1) + p * (∑ k ∈ Finset.Icc 1 (p ^ j), Nat.gcd k (p ^ j)) := by
    intro j
    set Q := p ^ j with hQ
    have hP : p ^ (j+1) = p * Q := by rw [hQ]; ring
    rw [hP]
    have hA : (Finset.Icc 1 (p*Q)).filter (fun k => p ∣ k) = (Finset.Icc 1 Q).image (fun m => p * m) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, m, hm⟩
        exact ⟨m, ⟨by nlinarith, by nlinarith⟩, hm.symm⟩
      · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
        exact ⟨⟨by nlinarith, by nlinarith⟩, m, rfl⟩
    have hAsum : ∑ k ∈ (Finset.Icc 1 (p*Q)).filter (fun k => p ∣ k), Nat.gcd k (p*Q)
        = p * ∑ m ∈ Finset.Icc 1 Q, Nat.gcd m Q := by
      rw [hA, Finset.sum_image]
      · simp_rw [Nat.gcd_mul_left]
        rw [← Finset.mul_sum]
      · intro a _ b _ hab
        exact Nat.eq_of_mul_eq_mul_left hp0 hab
    have hBval : ∀ k ∈ (Finset.Icc 1 (p*Q)).filter (fun k => ¬ p ∣ k), Nat.gcd k (p*Q) = 1 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hkdvd⟩ := hk
      have hcop : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).mpr hkdvd).symm
      have hcop2 : Nat.Coprime k Q := by
        rw [hQ]; exact hcop.pow_right j
      exact hcop.mul_right hcop2
    have hAcard : ((Finset.Icc 1 (p*Q)).filter (fun k => p ∣ k)).card = Q := by
      rw [hA, Finset.card_image_of_injective]
      · simp
      · intro a b hab
        exact Nat.eq_of_mul_eq_mul_left hp0 hab
    have htot : (Finset.Icc 1 (p*Q)).card = p * Q := by simp
    have hcardsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 (p*Q)) (p := fun k => p ∣ k)
    have hBcard : ((Finset.Icc 1 (p*Q)).filter (fun k => ¬ p ∣ k)).card = p * Q - Q := by omega
    have hBsum : ∑ k ∈ (Finset.Icc 1 (p*Q)).filter (fun k => ¬ p ∣ k), Nat.gcd k (p*Q)
        = p * Q - Q := by
      rw [Finset.sum_congr rfl hBval]
      simp [hBcard]
    have hsplitsum := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p*Q)) (fun k => p ∣ k)
        (fun k => Nat.gcd k (p*Q))
    rw [← hsplitsum, hAsum, hBsum]
    have hqp : p * Q - Q = Q * (p - 1) := by
      cases' Nat.exists_eq_add_of_le hp0 with c hc
      nlinarith [Nat.sub_add_cancel hp0]
    omega
  have key : ∀ j : ℕ, (∑ k ∈ Finset.Icc 1 (p ^ (j+1)), Nat.gcd k (p ^ (j+1)))
      = p ^ j * ((j+1) * (p - 1) + p) := by
    intro j
    induction j with
    | zero =>
      have h0 := step 0
      rw [base0] at h0
      rw [h0]
      ring
    | succ j ih =>
      have hs := step (j+1)
      rw [ih] at hs
      rw [hs]
      have hpow : (p:ℕ) ^ (j+1) = p * p ^ j := by ring
      rw [hpow]
      ring
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : j + 1 - 1 = j := by omega
  rw [hj]
  exact key j

end Native.Competemath.P61
