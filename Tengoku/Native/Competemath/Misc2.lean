/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P209

/-- competemath.com problem 209. -/
theorem book_graph_return_time :
    (∀ n : ℕ, 0 < n → 2 * (1 + 2 * n) / 2 = 2 * n + 1) ∧
    2 * (1 + 2 * 2026) / 2 = 4053 := by
  constructor
  · intro n hn; omega
  · norm_num

end Native.Competemath.P209

namespace Native.Competemath.P103

/-- competemath.com problem 103. -/
theorem knockout_cup (n : ℕ) (h : 1 ≤ n) : n - 1 = 29 ↔ n = 30 := by omega

end Native.Competemath.P103

namespace Native.Competemath.P216

set_option linter.unusedVariables false in
/-- competemath.com problem 216. -/
theorem windmill_return_time (n : ℕ) (hn : 0 < n) :
    2 * (3 * n) / 2 = 3 * n ∧ 3 * 2026 = 6078 := by
  constructor
  · omega
  · norm_num

end Native.Competemath.P216

namespace Native.Competemath.P225

/-- competemath.com problem 225. -/
theorem sum_two_squares_5_2026 : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 5 ^ 2026}.ncard = 8108 := by
  let π : GaussianInt := ⟨2, 1⟩
  let πbar : GaussianInt := ⟨2, -1⟩
  let U : Set GaussianInt := {1, -1, (⟨0, 1⟩ : GaussianInt), -(⟨0, 1⟩ : GaussianInt)}
  let f : ℕ × GaussianInt → GaussianInt := fun au => au.2 * π ^ au.1 * πbar ^ (2026 - au.1)
  have h1 : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 5 ^ 2026}.ncard
      = {z : GaussianInt | z.re ^ 2 + z.im ^ 2 = 5 ^ 2026}.ncard := by
        apply Set.ncard_congr (fun (p : ℤ × ℤ) _ => (⟨p.1, p.2⟩ : GaussianInt))
        · intro a ha
          exact ha
        · intro a b ha hb hab
          have h1 : a.1 = b.1 := congrArg (fun z : GaussianInt => z.re) hab
          have h2 : a.2 = b.2 := congrArg (fun z : GaussianInt => z.im) hab
          exact Prod.ext h1 h2
        · intro b hb
          exact ⟨(b.re, b.im), hb, rfl⟩
  have h2 : {z : GaussianInt | z.re ^ 2 + z.im ^ 2 = 5 ^ 2026}
      = f '' (Set.Icc (0 : ℕ) 2026 ×ˢ U) := by
        have s1 : Irreducible π := by
          constructor
          · intro h
            rw [← Zsqrtd.norm_eq_one_iff] at h
            revert h
            decide
          · intro a b hab
            have hnorm : Zsqrtd.norm a * Zsqrtd.norm b = 5 := by
              rw [← Zsqrtd.norm_mul, ← hab]
              decide
            have h5 : (5:ℕ).Prime := by norm_num
            have hnat : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
              have := congrArg Int.natAbs hnorm
              simpa [Int.natAbs_mul] using this
            rcases (h5.eq_one_or_self_of_dvd (Zsqrtd.norm a).natAbs ⟨(Zsqrtd.norm b).natAbs, hnat.symm⟩) with h | h
            · left
              exact Zsqrtd.norm_eq_one_iff.mp h
            · right
              have hb1 : (Zsqrtd.norm b).natAbs = 1 := by
                rw [h] at hnat
                omega
              exact Zsqrtd.norm_eq_one_iff.mp hb1
        have s2 : ¬ Associated π πbar := by
          rintro ⟨u, hu⟩
          simp only [π, πbar] at hu
          have hre : (2:ℤ) * (u:GaussianInt).re + (-1) * (1:ℤ) * (u:GaussianInt).im = 2 := by
            have := congrArg Zsqrtd.re hu
            simpa [Zsqrtd.re_mul] using this
          have him : (2:ℤ) * (u:GaussianInt).im + (1:ℤ) * (u:GaussianInt).re = -1 := by
            have := congrArg Zsqrtd.im hu
            simpa [Zsqrtd.im_mul] using this
          omega
        have s3 : ∀ z : GaussianInt, z.re ^ 2 + z.im ^ 2 = 5 ^ 2026 →
            ∃ a ∈ Set.Icc (0:ℕ) 2026, ∃ u ∈ U, z = f (a, u) := by
              have hunit : ∀ z : GaussianInt, z.re ^ 2 + z.im ^ 2 = 1 → z ∈ U := by
                intro z h
                have hre2 : z.re^2 ≤ 1 := by nlinarith [sq_nonneg z.im]
                have him2 : z.im^2 ≤ 1 := by nlinarith [sq_nonneg z.re]
                have hre1 : -1 ≤ z.re := by nlinarith [sq_nonneg (z.re+1)]
                have hre3 : z.re ≤ 1 := by nlinarith [sq_nonneg (z.re-1)]
                have him1 : -1 ≤ z.im := by nlinarith [sq_nonneg (z.im+1)]
                have him3 : z.im ≤ 1 := by nlinarith [sq_nonneg (z.im-1)]
                have hz : z = ⟨z.re, z.im⟩ := by ext <;> simp
                simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff]
                interval_cases z.re <;> interval_cases z.im <;> subst hz <;> revert h <;> decide
              have key : ∀ n : ℕ, ∀ z : GaussianInt, z.re ^ 2 + z.im ^ 2 = 5 ^ n →
                  ∃ a ∈ Set.Icc (0:ℕ) n, ∃ u ∈ U, z = u * π ^ a * πbar ^ (n - a) := by
                intro n
                induction n with
                | zero =>
                  intro z hz
                  refine ⟨0, ?_, z, ?_, ?_⟩
                  · simp
                  · exact hunit z (by simpa using hz)
                  · simp
                | succ n ih =>
                  intro z hz
                  have hstarπ : star π = πbar := by decide
                  have hprod : π * πbar = 5 := by decide
                  have hnormz : (Zsqrtd.norm z : ℤ) = 5 ^ (n+1) := by
                    rw [Zsqrtd.norm]; ring_nf; ring_nf at hz; linarith
                  have hzstar : (Zsqrtd.norm z : GaussianInt) = z * star z := Zsqrtd.norm_eq_mul_conj z
                  have hcast : (Zsqrtd.norm z : GaussianInt) = 5 * (5:GaussianInt)^n := by
                    have h2 : ((5 ^ (n+1) : ℤ) : GaussianInt) = 5 * (5:GaussianInt)^n := by push_cast; ring
                    rw [hnormz]; exact h2
                  have hdvd5 : (5:GaussianInt) ∣ z * star z := by
                    rw [← hzstar, hcast]; exact ⟨(5:GaussianInt)^n, rfl⟩
                  have hdvdπ : π ∣ z * star z := by
                    rw [← hprod] at hdvd5
                    exact dvd_trans ⟨πbar, rfl⟩ hdvd5
                  have hprime : Prime π := s1.prime
                  have hdichot : π ∣ z ∨ π ∣ star z := hprime.dvd_mul.mp hdvdπ
                  have hfinal : π ∣ z ∨ πbar ∣ z := by
                    rcases hdichot with h | h
                    · left; exact h
                    · right
                      obtain ⟨c, hc⟩ := h
                      refine ⟨star c, ?_⟩
                      have heq : star (star z) = star (π * c) := congrArg star hc
                      simpa [hstarπ, mul_comm] using heq
                  have hnormπ : (Zsqrtd.norm π : ℤ) = 5 := by decide
                  have hnormπbar : (Zsqrtd.norm πbar : ℤ) = 5 := by decide
                  rcases hfinal with ⟨w, hw⟩ | ⟨w, hw⟩
                  · have hwnorm : (Zsqrtd.norm w : ℤ) = 5 ^ n := by
                      have hm := Zsqrtd.norm_mul π w
                      rw [← hw, hnormz, hnormπ] at hm
                      have h5pos : (5:ℤ) ≠ 0 := by norm_num
                      have heq2 : (5:ℤ) * 5^n = 5 * Zsqrtd.norm w := by rw [← hm]; ring
                      exact (mul_left_cancel₀ h5pos heq2).symm
                    have hwre : w.re ^ 2 + w.im ^ 2 = 5 ^ n := by
                      have hn := hwnorm
                      rw [Zsqrtd.norm] at hn
                      ring_nf at hn ⊢
                      linarith
                    obtain ⟨a, ha, u, hu, heq⟩ := ih w hwre
                    have hale : a ≤ n := (Set.mem_Icc.mp ha).2
                    refine ⟨a+1, ?_, u, hu, ?_⟩
                    · simp only [Set.mem_Icc]; omega
                    · rw [hw, heq]
                      have hna : n + 1 - (a+1) = n - a := by omega
                      rw [hna]
                      ring
                  · have hwnorm : (Zsqrtd.norm w : ℤ) = 5 ^ n := by
                      have hm := Zsqrtd.norm_mul πbar w
                      rw [← hw, hnormz, hnormπbar] at hm
                      have h5pos : (5:ℤ) ≠ 0 := by norm_num
                      have heq2 : (5:ℤ) * 5^n = 5 * Zsqrtd.norm w := by rw [← hm]; ring
                      exact (mul_left_cancel₀ h5pos heq2).symm
                    have hwre : w.re ^ 2 + w.im ^ 2 = 5 ^ n := by
                      have hn := hwnorm
                      rw [Zsqrtd.norm] at hn
                      ring_nf at hn ⊢
                      linarith
                    obtain ⟨a, ha, u, hu, heq⟩ := ih w hwre
                    have hale : a ≤ n := (Set.mem_Icc.mp ha).2
                    refine ⟨a, ?_, u, hu, ?_⟩
                    · simp only [Set.mem_Icc]; omega
                    · rw [hw, heq]
                      have hna : n + 1 - a = (n - a) + 1 := by omega
                      rw [hna, pow_succ]
                      ring
              intro z hz
              obtain ⟨a, ha, u, hu, heq⟩ := key 2026 z hz
              exact ⟨a, ha, u, hu, heq⟩
        have s4 : ∀ a ∈ Set.Icc (0:ℕ) 2026, ∀ u ∈ U, (f (a,u)).re ^ 2 + (f (a,u)).im ^ 2 = 5 ^ 2026 := by
          have hnormpow : ∀ (x : GaussianInt) (n : ℕ), (Zsqrtd.norm (x^n) : ℤ) = (Zsqrtd.norm x)^n := by
            intro x n
            induction n with
            | zero => simp
            | succ n ih => rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]
          intro a ha u hu
          have hnormπ : (Zsqrtd.norm π : ℤ) = 5 := by decide
          have hnormπbar : (Zsqrtd.norm πbar : ℤ) = 5 := by decide
          have hnormu : (Zsqrtd.norm u : ℤ) = 1 := by
            simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
            rcases hu with h|h|h|h <;> subst h <;> decide
          have hale : a ≤ 2026 := (Set.mem_Icc.mp ha).2
          have hnormf : (Zsqrtd.norm (f (a,u)) : ℤ) = 5 ^ 2026 := by
            show (Zsqrtd.norm (u * π ^ a * πbar ^ (2026 - a)) : ℤ) = 5 ^ 2026
            rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, hnormpow, hnormpow, hnormu, hnormπ, hnormπbar]
            rw [one_mul, ← pow_add]
            congr 1
            omega
          have hre : (f (a,u)).re ^ 2 + (f (a,u)).im ^ 2 = Zsqrtd.norm (f (a,u)) := by
            rw [Zsqrtd.norm]; ring
          rw [hre, hnormf]
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
        constructor
        · intro hz
          obtain ⟨a, ha, u, hu, heq⟩ := s3 z hz
          exact ⟨(a, u), ⟨ha, hu⟩, heq.symm⟩
        · rintro ⟨⟨a, u⟩, ⟨ha, hu⟩, heq⟩
          rw [← heq]
          exact s4 a ha u hu
  have h3 : (f '' (Set.Icc (0 : ℕ) 2026 ×ˢ U)).ncard = 8108 := by
    have hinj : Set.InjOn f (Set.Icc (0:ℕ) 2026 ×ˢ U) := by
      have hπne : π ≠ 0 := by decide
      have hπbarne : πbar ≠ 0 := by decide
      have s1 : Irreducible π := by
        constructor
        · intro h
          rw [← Zsqrtd.norm_eq_one_iff] at h
          revert h
          decide
        · intro a b hab
          have hnorm : Zsqrtd.norm a * Zsqrtd.norm b = 5 := by
            rw [← Zsqrtd.norm_mul, ← hab]
            decide
          have h5 : (5:ℕ).Prime := by norm_num
          have hnat : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 5 := by
            have := congrArg Int.natAbs hnorm
            simpa [Int.natAbs_mul] using this
          rcases (h5.eq_one_or_self_of_dvd (Zsqrtd.norm a).natAbs ⟨(Zsqrtd.norm b).natAbs, hnat.symm⟩) with h | h
          · left
            exact Zsqrtd.norm_eq_one_iff.mp h
          · right
            have hb1 : (Zsqrtd.norm b).natAbs = 1 := by
              rw [h] at hnat
              omega
            exact Zsqrtd.norm_eq_one_iff.mp hb1
      have hprime : Prime π := s1.prime
      have s2 : ¬ Associated π πbar := by
        rintro ⟨u, hu⟩
        simp only [π, πbar] at hu
        have hre : (2:ℤ) * (u:GaussianInt).re + (-1) * (1:ℤ) * (u:GaussianInt).im = 2 := by
          have := congrArg Zsqrtd.re hu
          simpa [Zsqrtd.re_mul] using this
        have him : (2:ℤ) * (u:GaussianInt).im + (1:ℤ) * (u:GaussianInt).re = -1 := by
          have := congrArg Zsqrtd.im hu
          simpa [Zsqrtd.im_mul] using this
        omega
      have hndvd : ¬ π ∣ πbar := by
        intro h
        obtain ⟨c, hc⟩ := h
        have hnc : Zsqrtd.norm π * Zsqrtd.norm c = Zsqrtd.norm πbar := by
          rw [hc, Zsqrtd.norm_mul]
        have hnπ : Zsqrtd.norm π = 5 := by decide
        have hnπbar : Zsqrtd.norm πbar = 5 := by decide
        rw [hnπ, hnπbar] at hnc
        have hnc1 : Zsqrtd.norm c = 1 := by omega
        have hnc1' : (Zsqrtd.norm c).natAbs = 1 := by omega
        have hcu : IsUnit c := Zsqrtd.norm_eq_one_iff.mp hnc1'
        exact s2 ⟨hcu.unit, by rw [hc]; simp⟩
      have hUunit : ∀ u : GaussianInt, u ∈ U → IsUnit u := by
        intro u hu
        simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with h|h|h|h <;> subst h <;> rw [← Zsqrtd.norm_eq_one_iff] <;> decide
      have main : ∀ a1 a2 : ℕ, a1 ≤ a2 → a2 ≤ 2026 → ∀ u1 u2 : GaussianInt, IsUnit u1 → IsUnit u2 →
          u1 * π ^ a1 * πbar ^ (2026 - a1) = u2 * π ^ a2 * πbar ^ (2026 - a2) → a1 = a2 := by
        intro a1 a2 hle hle2026 u1 u2 hu1 hu2 heq
        by_contra hne
        have hlt : a1 < a2 := lt_of_le_of_ne hle hne
        have e1 : u1 * π ^ a1 * πbar ^ (2026 - a1) = (u1 * πbar ^ (2026 - a1)) * π ^ a1 := by ring
        have e2 : u2 * π ^ a2 * πbar ^ (2026 - a2) = (u2 * π ^ (a2 - a1) * πbar ^ (2026 - a2)) * π ^ a1 := by
          have hp : π ^ a2 = π ^ (a2 - a1) * π ^ a1 := by
            rw [← pow_add]
            congr 1
            omega
          rw [hp]; ring
        have hcancel1 : (u1 * πbar ^ (2026 - a1)) * π ^ a1 = (u2 * π ^ (a2 - a1) * πbar ^ (2026 - a2)) * π ^ a1 := by
          rw [← e1, ← e2, heq]
        have hpow1ne : (π:GaussianInt) ^ a1 ≠ 0 := pow_ne_zero a1 hπne
        have hcancel1' : u1 * πbar ^ (2026 - a1) = u2 * π ^ (a2 - a1) * πbar ^ (2026 - a2) :=
          mul_right_cancel₀ hpow1ne hcancel1
        have e3 : u1 * πbar ^ (2026 - a1) = (u1 * πbar ^ (a2 - a1)) * πbar ^ (2026 - a2) := by
          have hp : πbar ^ (2026 - a1) = πbar ^ (a2 - a1) * πbar ^ (2026 - a2) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hp]; ring
        have e4 : u2 * π ^ (a2 - a1) * πbar ^ (2026 - a2) = (u2 * π ^ (a2 - a1)) * πbar ^ (2026 - a2) := by ring
        have hcancel2 : (u1 * πbar ^ (a2 - a1)) * πbar ^ (2026 - a2) = (u2 * π ^ (a2 - a1)) * πbar ^ (2026 - a2) := by
          rw [← e3, ← e4, hcancel1']
        have hpow2ne : (πbar:GaussianInt) ^ (2026 - a2) ≠ 0 := pow_ne_zero _ hπbarne
        have hfinal : u1 * πbar ^ (a2 - a1) = u2 * π ^ (a2 - a1) :=
          mul_right_cancel₀ hpow2ne hcancel2
        have hpdvd : π ∣ u1 * πbar ^ (a2 - a1) := by
          rw [hfinal]
          have hdvdpow : π ∣ π ^ (a2 - a1) := dvd_pow_self π (by omega)
          exact hdvdpow.mul_left u2
        have hpdvd2 : π ∣ πbar ^ (a2 - a1) := by
          rcases hprime.dvd_mul.mp hpdvd with h | h
          · exact absurd (isUnit_of_dvd_unit h hu1) hprime.not_unit
          · exact h
        have hpdvdπbar : π ∣ πbar := hprime.dvd_of_dvd_pow hpdvd2
        exact hndvd hpdvdπbar
      rintro ⟨a1, u1⟩ h1mem ⟨a2, u2⟩ h2mem heq
      simp only [Set.mem_prod, Set.mem_Icc] at h1mem h2mem
      obtain ⟨⟨_, ha1⟩, hu1mem⟩ := h1mem
      obtain ⟨⟨_, ha2⟩, hu2mem⟩ := h2mem
      have hu1 : IsUnit u1 := hUunit u1 hu1mem
      have hu2 : IsUnit u2 := hUunit u2 hu2mem
      simp only [f] at heq
      have haeq : a1 = a2 := by
        rcases le_total a1 a2 with h | h
        · exact main a1 a2 h ha2 u1 u2 hu1 hu2 heq
        · exact (main a2 a1 h ha1 u2 u1 hu2 hu1 heq.symm).symm
      subst haeq
      have hpne : (π:GaussianInt) ^ a1 ≠ 0 := pow_ne_zero a1 hπne
      have hbne : (πbar:GaussianInt) ^ (2026 - a1) ≠ 0 := pow_ne_zero _ hπbarne
      have h1 : u1 * π ^ a1 = u2 * π ^ a1 := by
        have e1 : u1 * π ^ a1 * πbar ^ (2026-a1) = (u1 * π^a1) * πbar^(2026-a1) := by ring
        have e2 : u2 * π ^ a1 * πbar ^ (2026-a1) = (u2 * π^a1) * πbar^(2026-a1) := by ring
        rw [e1, e2] at heq
        exact mul_right_cancel₀ hbne heq
      have hueq : u1 = u2 := mul_right_cancel₀ hpne h1
      exact Prod.ext rfl hueq
    have hcard : (Set.Icc (0:ℕ) 2026 ×ˢ U).ncard = 8108 := by
      rw [Set.ncard_prod]
      have h1 : (Set.Icc (0:ℕ) 2026).ncard = 2027 := by
        rw [show (Set.Icc (0:ℕ) 2026) = ↑(Finset.Icc 0 2026) from (Finset.coe_Icc 0 2026).symm, Set.ncard_coe_finset, Nat.card_Icc]
      have h2 : U.ncard = 4 := by
        show ({1, -1, (⟨0, 1⟩ : GaussianInt), -(⟨0, 1⟩ : GaussianInt)} : Set GaussianInt).ncard = 4
        rw [show ({1, -1, (⟨0, 1⟩ : GaussianInt), -(⟨0, 1⟩ : GaussianInt)} : Set GaussianInt)
            = (↑({1, -1, ⟨0,1⟩, -⟨0,1⟩} : Finset GaussianInt) : Set GaussianInt) by simp,
          Set.ncard_coe_finset]
        decide
      rw [h1, h2]
    rw [hinj.ncard_image]
    exact hcard
  rw [h1, h2]
  exact h3

end Native.Competemath.P225

namespace Native.Competemath.P229

open Finset Nat

/-- competemath.com problem 229. -/
lemma even_iff_two_mul (n : ℕ) : Even n ↔ ∃ k, n = 2 * k :=
  by
    constructor
    · rintro ⟨k, rfl⟩
      use k
      rw [two_mul]
    · rintro ⟨k, rfl⟩
      use k
      rw [← two_mul]

lemma evens_Icc_eq_image :
  Finset.filter (fun n => Even n) (Finset.Icc 1 2026)
  = Finset.image (fun x => 2 * x) (Finset.Icc 1 1013) :=
  by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, even_iff_two_mul]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      use k
      constructor
      · constructor
        · exact Nat.succ_le_iff.mp (by linarith : 1 ≤ k)
        · exact Nat.le_of_mul_le_mul_left h2 (by decide)
      · rfl
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨k, rfl⟩⟩

lemma card_Icc_1_1013 : (Finset.Icc 1 1013).card = 1013 :=
  by
    rw [Nat.card_Icc]

theorem divisor_duel_winning_count :
  (Finset.filter (fun n => Even n) (Finset.Icc 1 2026)).card = 1013 :=
  by
    rw [evens_Icc_eq_image, Finset.card_image_of_injective]
    · rw [card_Icc_1_1013]
    · intro a b h
      exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) h

end Native.Competemath.P229

namespace Native.Competemath.P245

noncomputable def shelf_sequence : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | (n + 4) => shelf_sequence (n + 3) + shelf_sequence n

/-- competemath.com problem 245. -/
lemma shelf_sequence_zero : shelf_sequence 0 = 1 :=
  by rfl

lemma shelf_sequence_one : shelf_sequence 1 = 1 :=
  by
    rfl

lemma shelf_sequence_two : shelf_sequence 2 = 1 :=
  by rfl

lemma shelf_sequence_three : shelf_sequence 3 = 1 :=
  by
    rfl

lemma shelf_sequence_recurrence (n : ℕ) : shelf_sequence (n + 4) = shelf_sequence (n + 3) + shelf_sequence n :=
  by
    cases n with | zero => rfl | succ n =>
    cases n with | zero => rfl | succ n =>
    cases n with | zero => rfl | succ n =>
    cases n with | zero => rfl | succ n =>
    simp [shelf_sequence]

lemma shelf_sequence_20 : shelf_sequence 20 = 345 :=
  by
    have h4 : shelf_sequence 4 = 2 := by rw [shelf_sequence_recurrence, shelf_sequence_three, shelf_sequence_zero]
    have h5 : shelf_sequence 5 = 3 := by rw [shelf_sequence_recurrence, h4, shelf_sequence_one]
    have h6 : shelf_sequence 6 = 4 := by rw [shelf_sequence_recurrence, h5, shelf_sequence_two]
    have h7 : shelf_sequence 7 = 5 := by rw [shelf_sequence_recurrence, h6, shelf_sequence_three]
    have h8 : shelf_sequence 8 = 7 := by rw [shelf_sequence_recurrence, h7, h4]
    have h9 : shelf_sequence 9 = 10 := by rw [shelf_sequence_recurrence, h8, h5]
    have h10 : shelf_sequence 10 = 14 := by rw [shelf_sequence_recurrence, h9, h6]
    have h11 : shelf_sequence 11 = 19 := by rw [shelf_sequence_recurrence, h10, h7]
    have h12 : shelf_sequence 12 = 26 := by rw [shelf_sequence_recurrence, h11, h8]
    have h13 : shelf_sequence 13 = 36 := by rw [shelf_sequence_recurrence, h12, h9]
    have h14 : shelf_sequence 14 = 50 := by rw [shelf_sequence_recurrence, h13, h10]
    have h15 : shelf_sequence 15 = 69 := by rw [shelf_sequence_recurrence, h14, h11]
    have h16 : shelf_sequence 16 = 95 := by rw [shelf_sequence_recurrence, h15, h12]
    have h17 : shelf_sequence 17 = 131 := by rw [shelf_sequence_recurrence, h16, h13]
    have h18 : shelf_sequence 18 = 181 := by rw [shelf_sequence_recurrence, h17, h14]
    have h19 : shelf_sequence 19 = 250 := by rw [shelf_sequence_recurrence, h18, h15]
    rw [shelf_sequence_recurrence, h19, h16]

theorem shelf_tilings_20 :
  ∃ f : ℕ → ℕ, f 0 = 1 ∧ f 1 = 1 ∧ f 2 = 1 ∧ f 3 = 1 ∧
    (∀ n, f (n + 4) = f (n + 3) + f n) ∧ f 20 = 345 :=
  by
    use shelf_sequence
    exact ⟨shelf_sequence_zero, shelf_sequence_one, shelf_sequence_two, shelf_sequence_three, shelf_sequence_recurrence, shelf_sequence_20⟩

end Native.Competemath.P245
