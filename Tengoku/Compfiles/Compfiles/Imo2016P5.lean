/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Kimi K3
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2016, Problem 5

The equation

  (x - 1)(x - 2) ... (x - 2016) = (x - 1)(x - 2) ... (x - 2016)

is written on the board. What is the least possible value of k
for which it is possible to erase exactly k of these 4032 factors
such that at least one factor remains on each side and the resulting
equation has no real solutions?
-/

namespace Imo2016P5

lemma lemma1 {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Finset.card (s \ s.filter p) + Finset.card (s.filter p) = Finset.card s :=
  Finset.card_sdiff_add_card_eq_card (Finset.filter_subset p s)

lemma u_neg_iff {x : ℝ} (j : ℕ) :
    (x - (4 * (j : ℝ) + 1)) * (x - (4 * (j : ℝ) + 4)) < 0 ↔
      4 * (j : ℝ) + 1 < x ∧ x < 4 * (j : ℝ) + 4 := by
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by linarith, by linarith⟩
    · exfalso; linarith
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨by linarith, by linarith⟩

lemma v_neg_iff {x : ℝ} (j : ℕ) :
    (x - (4 * (j : ℝ) + 2)) * (x - (4 * (j : ℝ) + 3)) < 0 ↔
      4 * (j : ℝ) + 2 < x ∧ x < 4 * (j : ℝ) + 3 := by
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by linarith, by linarith⟩
    · exfalso; linarith
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨by linarith, by linarith⟩

lemma prod_P_fst (x : ℝ) :
    ∏ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 1))
      = (x - 1) * ∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 5)) := by
  have h : (504 : ℕ) = 503 + 1 := rfl
  rw [h, Finset.prod_range_succ']
  have e1 : x - (4 * ((0 : ℕ) : ℝ) + 1) = x - 1 := by norm_num
  have e2 : (∏ k ∈ Finset.range 503, (x - (4 * ((k + 1 : ℕ) : ℝ) + 1)))
      = ∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 5)) :=
    Finset.prod_congr rfl (fun k _ ↦ by push_cast; ring)
  rw [e1, e2, mul_comm]

lemma prod_P_snd (x : ℝ) :
    ∏ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 4))
      = (∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 4))) * (x - 2016) := by
  have h : (504 : ℕ) = 503 + 1 := rfl
  rw [h, Finset.prod_range_succ]
  congr 1
  norm_num

lemma prod_Q_fst (x : ℝ) :
    ∏ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 2))
      = (x - 2) * ∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 6)) := by
  have h : (504 : ℕ) = 503 + 1 := rfl
  rw [h, Finset.prod_range_succ']
  have e1 : x - (4 * ((0 : ℕ) : ℝ) + 2) = x - 2 := by norm_num
  have e2 : (∏ k ∈ Finset.range 503, (x - (4 * ((k + 1 : ℕ) : ℝ) + 2)))
      = ∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 6)) :=
    Finset.prod_congr rfl (fun k _ ↦ by push_cast; ring)
  rw [e1, e2, mul_comm]

lemma prod_Q_snd (x : ℝ) :
    ∏ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 3))
      = (∏ k ∈ Finset.range 503, (x - (4 * (k : ℝ) + 3))) * (x - 2015) := by
  have h : (504 : ℕ) = 503 + 1 := rfl
  rw [h, Finset.prod_range_succ]
  congr 1
  norm_num

/-- Re-pairing of the left-hand product: isolate `1` and `2016`, and group the
remaining factors into pairs `(4j+4, 4j+5)`. -/
lemma prod_repair_P (x : ℝ) :
    (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))))
      = (x - 1) * (x - 2016)
        * ∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5))) := by
  have e : ∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5)))
      = (∏ j ∈ Finset.range 503, (x - (4 * (j : ℝ) + 4)))
        * (∏ j ∈ Finset.range 503, (x - (4 * (j : ℝ) + 5))) :=
    Finset.prod_mul_distrib
  rw [Finset.prod_mul_distrib, prod_P_fst, prod_P_snd, e]
  ring

/-- Re-pairing of the right-hand product: isolate `2` and `2015`, and group the
remaining factors into pairs `(4j+3, 4j+6)`. -/
lemma prod_repair_Q (x : ℝ) :
    (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))))
      = (x - 2) * (x - 2015)
        * ∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6))) := by
  have e : ∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6)))
      = (∏ j ∈ Finset.range 503, (x - (4 * (j : ℝ) + 3)))
        * (∏ j ∈ Finset.range 503, (x - (4 * (j : ℝ) + 6))) :=
    Finset.prod_mul_distrib
  rw [Finset.prod_mul_distrib, prod_Q_fst, prod_Q_snd, e]
  ring

/-- The two products remaining on the board never take the same real value:
the left one is always strictly smaller than the right one. -/
lemma key (x : ℝ) :
    (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)))) ≠
    (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3)))) := by
  have huv : ∀ k : ℕ, (x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))
      = (x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)) + 2 := fun k ↦ by ring
  by_cases hz : (∃ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)) = 0)
              ∨ (∃ k ∈ Finset.range 504, (x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3)) = 0)
  · -- Some factor vanishes; then exactly one of the two products is zero.
    rcases hz with ⟨k, hk, h0⟩ | ⟨k, hk, h0⟩
    · have hP0 : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)))) = 0 :=
        Finset.prod_eq_zero hk h0
      have hQ0 : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3)))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j hj hQj
        rw [mul_eq_zero] at h0 hQj
        have e1 : x = 4 * (k : ℝ) + 1 ∨ x = 4 * (k : ℝ) + 4 := by
          rcases h0 with h | h
          · left; linarith
          · right; linarith
        have e2 : x = 4 * (j : ℝ) + 2 ∨ x = 4 * (j : ℝ) + 3 := by
          rcases hQj with h | h
          · left; linarith
          · right; linarith
        rcases e1 with rfl | rfl <;> rcases e2 with e2 | e2
        · have e' : 4 * k + 1 = 4 * j + 2 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 1 = 4 * j + 3 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 4 = 4 * j + 2 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 4 = 4 * j + 3 := by exact_mod_cast e2
          lia
      intro h
      rw [hP0] at h
      exact hQ0 h.symm
    · have hQ0 : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3)))) = 0 :=
        Finset.prod_eq_zero hk h0
      have hP0 : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j hj hPj
        rw [mul_eq_zero] at h0 hPj
        have e1 : x = 4 * (k : ℝ) + 2 ∨ x = 4 * (k : ℝ) + 3 := by
          rcases h0 with h | h
          · left; linarith
          · right; linarith
        have e2 : x = 4 * (j : ℝ) + 1 ∨ x = 4 * (j : ℝ) + 4 := by
          rcases hPj with h | h
          · left; linarith
          · right; linarith
        rcases e1 with rfl | rfl <;> rcases e2 with e2 | e2
        · have e' : 4 * k + 2 = 4 * j + 1 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 2 = 4 * j + 4 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 3 = 4 * j + 1 := by exact_mod_cast e2
          lia
        · have e' : 4 * k + 3 = 4 * j + 4 := by exact_mod_cast e2
          lia
      intro h
      rw [hQ0] at h
      exact hP0 h
  · push Not at hz
    obtain ⟨hzu, hzv⟩ := hz
    by_cases hneg : ∃ m ∈ Finset.range 504, (x - (4 * (m : ℝ) + 1)) * (x - (4 * (m : ℝ) + 4)) < 0
    · obtain ⟨m, hm, hmul⟩ := hneg
      have hmem : m < 504 := Finset.mem_range.mp hm
      have hx1 : 4 * (m : ℝ) + 1 < x := ((u_neg_iff m).mp hmul).1
      have hx2 : x < 4 * (m : ℝ) + 4 := ((u_neg_iff m).mp hmul).2
      rcases lt_trichotomy x (4 * (m : ℝ) + 2) with hC | hC0 | hCg
      · -- Case `x ∈ (4m+1, 4m+2)`: the left product is negative, the right one positive.
        have hPneg : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)))) < 0 := by
          rw [← Finset.mul_prod_erase _ _ hm]
          have hpos : 0 < ∏ k ∈ (Finset.range 504).erase m,
              ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))) := by
            apply Finset.prod_pos
            intro j hj
            obtain ⟨hjm, hj504⟩ := Finset.mem_erase.mp hj
            have hn : ¬ (x - (4 * (j : ℝ) + 1)) * (x - (4 * (j : ℝ) + 4)) < 0 := by
              intro h
              obtain ⟨hy1, hy2⟩ := (u_neg_iff j).mp h
              have e1 : (4 : ℝ) * j + 1 < 4 * m + 2 := by linarith
              have e2 : (4 : ℝ) * m + 1 < 4 * j + 4 := by linarith
              have e1' : 4 * j + 1 < 4 * m + 2 := by exact_mod_cast e1
              have e2' : 4 * m + 1 < 4 * j + 4 := by exact_mod_cast e2
              exact hjm (by lia)
            exact lt_of_le_of_ne' (not_lt.mp hn) (hzu j hj504)
          exact mul_neg_of_neg_of_pos hmul hpos
        have hQpos : 0 < ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))) := by
          apply Finset.prod_pos
          intro j hj
          have hn : ¬ (x - (4 * (j : ℝ) + 2)) * (x - (4 * (j : ℝ) + 3)) < 0 := by
            intro h
            obtain ⟨hy1, hy2⟩ := (v_neg_iff j).mp h
            have e1 : (4 : ℝ) * j + 2 < 4 * m + 2 := by linarith
            have e2 : (4 : ℝ) * m + 1 < 4 * j + 3 := by linarith
            have e1' : 4 * j + 2 < 4 * m + 2 := by exact_mod_cast e1
            have e2' : 4 * m + 1 < 4 * j + 3 := by exact_mod_cast e2
            lia
          exact lt_of_le_of_ne' (not_lt.mp hn) (hzv j hj)
        exact ne_of_lt (lt_trans hPneg hQpos)
      · -- Case `x = 4m+2`: a right-hand factor vanishes, contradicting `hzv`.
        exfalso
        exact hzv m hm (by rw [hC0]; ring)
      · rcases lt_trichotomy x (4 * (m : ℝ) + 3) with hE | hE0 | hD
        · -- Case `x ∈ (4m+2, 4m+3)`: both products are negative; compare them
          -- using the re-pairings `prod_repair_P` and `prod_repair_Q`.
          have hB : (x - 2) * (x - 2015) < 0 := by
            have g1 : 0 < x - 2 := by
              have h2le : (2 : ℝ) ≤ 4 * (m : ℝ) + 2 := by
                have hh : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
                linarith
              linarith
            have g2 : x - 2015 < 0 := by
              have h3le : (4 : ℝ) * m + 3 ≤ 2015 := by
                have hh : 4 * m + 3 ≤ 2015 := by lia
                exact_mod_cast hh
              linarith
            exact mul_neg_of_pos_of_neg g1 g2
          have hab2 : ∀ j : ℕ, (x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5))
              = (x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6)) + 2 := fun j ↦ by ring
          have hb : ∀ j ∈ Finset.range 503,
              0 < (x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6)) := by
            intro j _
            rw [mul_pos_iff]
            rcases le_or_gt (4 * (j : ℝ) + 3) x with h | h
            · left
              have hjm : j < m := by
                have e : (4 : ℝ) * j + 3 < 4 * m + 3 := by linarith
                have e' : 4 * j + 3 < 4 * m + 3 := by exact_mod_cast e
                lia
              have hx6 : 4 * (j : ℝ) + 6 < x := by
                have e : 4 * j + 6 ≤ 4 * m + 2 := by lia
                have e' : (4 : ℝ) * j + 6 ≤ 4 * m + 2 := by exact_mod_cast e
                linarith
              constructor <;> linarith
            · right
              constructor <;> linarith
          have ha : ∀ j ∈ Finset.range 503,
              0 < (x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5)) := by
            intro j hj
            rw [hab2 j]
            linarith [hb j hj]
          have hba : (∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6))))
              < ∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5))) := by
            apply Finset.prod_lt_prod
            · exact hb
            · intro j hj
              rw [hab2 j]
              linarith [hb j hj]
            · exact ⟨0, Finset.mem_range.mpr (by norm_num), by
                rw [hab2 0]
                linarith [hb 0 (Finset.mem_range.mpr (by norm_num))]⟩
          have hFin : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))))
              < ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))) := by
            rw [prod_repair_P, prod_repair_Q]
            have hAB : (x - 1) * (x - 2016) = (x - 2) * (x - 2015) - 2014 := by ring
            rw [hAB]
            have h1 : 0 < (x - 2) * (x - 2015)
                * ((∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 3)) * (x - (4 * (j : ℝ) + 6))))
                  - (∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5))))) :=
              mul_pos_of_neg_of_neg hB (sub_neg_of_lt hba)
            have h2 : 0 < 2014
                * (∏ j ∈ Finset.range 503, ((x - (4 * (j : ℝ) + 4)) * (x - (4 * (j : ℝ) + 5)))) :=
              mul_pos (show (0 : ℝ) < 2014 by norm_num) (Finset.prod_pos ha)
            linarith
          exact ne_of_lt hFin
        · -- Case `x = 4m+3`: a right-hand factor vanishes, contradicting `hzv`.
          exfalso
          exact hzv m hm (by rw [hE0]; ring)
        · -- Case `x ∈ (4m+3, 4m+4)`: the left product is negative, the right one positive.
          have hPneg : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)))) < 0 := by
            rw [← Finset.mul_prod_erase _ _ hm]
            have hpos : 0 < ∏ k ∈ (Finset.range 504).erase m,
                ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))) := by
              apply Finset.prod_pos
              intro j hj
              obtain ⟨hjm, hj504⟩ := Finset.mem_erase.mp hj
              have hn : ¬ (x - (4 * (j : ℝ) + 1)) * (x - (4 * (j : ℝ) + 4)) < 0 := by
                intro h
                obtain ⟨hy1, hy2⟩ := (u_neg_iff j).mp h
                have e1 : (4 : ℝ) * j + 1 < 4 * m + 4 := by linarith
                have e2 : (4 : ℝ) * m + 3 < 4 * j + 4 := by linarith
                have e1' : 4 * j + 1 < 4 * m + 4 := by exact_mod_cast e1
                have e2' : 4 * m + 3 < 4 * j + 4 := by exact_mod_cast e2
                exact hjm (by lia)
              exact lt_of_le_of_ne' (not_lt.mp hn) (hzu j hj504)
            exact mul_neg_of_neg_of_pos hmul hpos
          have hQpos : 0 < ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))) := by
            apply Finset.prod_pos
            intro j hj
            have hn : ¬ (x - (4 * (j : ℝ) + 2)) * (x - (4 * (j : ℝ) + 3)) < 0 := by
              intro h
              obtain ⟨hy1, hy2⟩ := (v_neg_iff j).mp h
              have e1 : (4 : ℝ) * j + 2 < 4 * m + 4 := by linarith
              have e2 : (4 : ℝ) * m + 3 < 4 * j + 3 := by linarith
              have e1' : 4 * j + 2 < 4 * m + 4 := by exact_mod_cast e1
              have e2' : 4 * m + 3 < 4 * j + 3 := by exact_mod_cast e2
              lia
            exact lt_of_le_of_ne' (not_lt.mp hn) (hzv j hj)
          exact ne_of_lt (lt_trans hPneg hQpos)
    · -- Every pair on the left is positive, hence smaller than the corresponding
      -- pair on the right.
      push Not at hneg
      have hu_pos : ∀ k ∈ Finset.range 504,
          0 < (x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4)) := by
        intro k hk
        exact lt_of_le_of_ne' (hneg k hk) (hzu k hk)
      have hlt : (∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))))
          < ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))) := by
        apply Finset.prod_lt_prod
        · exact hu_pos
        · intro k hk
          rw [huv k]
          linarith
        · exact ⟨0, Finset.mem_range.mpr (by norm_num), by rw [huv 0]; linarith⟩
      exact ne_of_lt hlt

lemma setL : Finset.Icc 1 2016 \ ((Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3))
    = ((Finset.range 504).image (fun k ↦ 4 * k + 1))
      ∪ ((Finset.range 504).image (fun k ↦ 4 * k + 4)) := by
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : n % 4 = 0 ∨ n % 4 = 1 := by lia
    rcases h4 with h | h
    · right
      exact ⟨n / 4 - 1, by lia⟩
    · left
      exact ⟨n / 4, by lia⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨⟨by lia, by lia⟩, by lia⟩
    · exact ⟨⟨by lia, by lia⟩, by lia⟩

lemma setR : Finset.Icc 1 2016 \ ((Finset.Icc 1 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1))
    = ((Finset.range 504).image (fun k ↦ 4 * k + 2))
      ∪ ((Finset.range 504).image (fun k ↦ 4 * k + 3)) := by
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : n % 4 = 2 ∨ n % 4 = 3 := by lia
    rcases h4 with h | h
    · left
      exact ⟨n / 4, by lia⟩
    · right
      exact ⟨n / 4, by lia⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact ⟨⟨by lia, by lia⟩, by lia⟩
    · exact ⟨⟨by lia, by lia⟩, by lia⟩

lemma disjL : Disjoint ((Finset.range 504).image (fun k ↦ 4 * k + 1))
    ((Finset.range 504).image (fun k ↦ 4 * k + 4)) := by
  rw [Finset.disjoint_left]
  rintro m hm1 hm2
  simp only [Finset.mem_image, Finset.mem_range] at hm1 hm2
  obtain ⟨a, -, ha⟩ := hm1
  obtain ⟨b, -, hb⟩ := hm2
  lia

lemma disjR : Disjoint ((Finset.range 504).image (fun k ↦ 4 * k + 2))
    ((Finset.range 504).image (fun k ↦ 4 * k + 3)) := by
  rw [Finset.disjoint_left]
  rintro m hm1 hm2
  simp only [Finset.mem_image, Finset.mem_range] at hm1 hm2
  obtain ⟨a, -, ha⟩ := hm1
  obtain ⟨b, -, hb⟩ := hm2
  lia

/-- After erasing the factors indexed by `n % 4 = 2, 3` on the left and by
`n % 4 = 0, 1` on the right, the resulting equation has no real solution. -/
lemma prod_erase_aux (x : ℝ) :
    (∏ i ∈ Finset.Icc (1 : ℕ) 2016 \ ((Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3)),
        (x - (i : ℝ))) ≠
    (∏ i ∈ Finset.Icc (1 : ℕ) 2016 \ ((Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1)),
        (x - (i : ℝ))) := by
  have hPfull : (∏ i ∈ Finset.Icc (1 : ℕ) 2016 \ ((Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 2 ∨ n % 4 = 3)),
        (x - (i : ℝ)))
      = ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 1)) * (x - (4 * (k : ℝ) + 4))) := by
    rw [setL, Finset.prod_union disjL,
      Finset.prod_image (fun a _ b _ h ↦ by lia),
      Finset.prod_image (fun a _ b _ h ↦ by lia),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ ↦ by push_cast; ring)
  have hQfull : (∏ i ∈ Finset.Icc (1 : ℕ) 2016 \ ((Finset.Icc (1 : ℕ) 2016).filter (fun n ↦ n % 4 = 0 ∨ n % 4 = 1)),
        (x - (i : ℝ)))
      = ∏ k ∈ Finset.range 504, ((x - (4 * (k : ℝ) + 2)) * (x - (4 * (k : ℝ) + 3))) := by
    rw [setR, Finset.prod_union disjR,
      Finset.prod_image (fun a _ b _ h ↦ by lia),
      Finset.prod_image (fun a _ b _ h ↦ by lia),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ ↦ by push_cast; ring)
  rw [hPfull, hQfull]
  exact key x

abbrev solution_value : ℕ := 2016

end Imo2016P5
