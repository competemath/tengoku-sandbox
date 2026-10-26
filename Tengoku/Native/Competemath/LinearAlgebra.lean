/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P211

/-- competemath.com problem 211. -/
theorem secret_rank_two_matrix
    (A : Matrix (Fin 2026) (Fin 2026) ℝ)
    (hA : ∀ i j : Fin 2026, A i j = 1 + (i.val + 1 : ℝ) * (j.val + 1 : ℝ)) :
    (Matrix.trace A) ^ 2 - Matrix.trace (A * A) = 2808060160050 := by
  have h1 : Matrix.trace A = 2774079227 := by
    unfold Matrix.trace Matrix.diag
    simp only [hA]
    rw [Fin.sum_univ_eq_sum_range (fun k => (1 + ((k:ℝ)+1)*((k:ℝ)+1)))]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsq : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((i:ℝ)+1)*((i:ℝ)+1)) = (n:ℝ)*(n+1)*(2*n+1)/6 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
    rw [hsq 2026]; norm_num
  have h2 : Matrix.trace (A * A) = 7695512749612757479 := by
    unfold Matrix.trace Matrix.diag
    set_option maxRecDepth 4000 in simp only [Matrix.mul_apply]
    set_option maxRecDepth 4000 in simp only [hA]
    rw [Fin.sum_univ_eq_sum_range (fun x => ∑ x_1 : Fin 2026, (1 + ((x:ℝ) + 1) * (↑↑x_1 + 1)) * (1 + (↑↑x_1 + 1) * ((x:ℝ) + 1)))]
    rw [show (∑ i ∈ Finset.range 2026, ∑ x_1 : Fin 2026, (1 + ((i:ℝ) + 1) * (↑↑x_1 + 1)) * (1 + (↑↑x_1 + 1) * ((i:ℝ) + 1))) = ∑ i ∈ Finset.range 2026, ∑ k ∈ Finset.range 2026, (1 + ((i:ℝ) + 1) * ((k:ℝ) + 1)) * (1 + ((k:ℝ) + 1) * ((i:ℝ) + 1)) from Finset.sum_congr rfl (fun i _ => Fin.sum_univ_eq_sum_range (fun k => (1 + ((i:ℝ) + 1) * ((k:ℝ) + 1)) * (1 + ((k:ℝ) + 1) * ((i:ℝ) + 1))) 2026)]
    have hexp : ∀ i k : ℕ, (1 + ((i:ℝ) + 1) * ((k:ℝ) + 1)) * (1 + ((k:ℝ) + 1) * ((i:ℝ) + 1)) = 1 + 2*((i:ℝ)+1)*((k:ℝ)+1) + ((i:ℝ)+1)^2*((k:ℝ)+1)^2 := by intro i k; ring
    simp only [hexp]
    simp only [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [← Finset.mul_sum]
    simp only [← Finset.sum_mul]
    simp only [← Finset.mul_sum]
    have hS1 : (∑ i ∈ Finset.range 2026, ((i:ℝ)+1)) = 2053351 := by
      have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((i:ℝ)+1)) = (n:ℝ)*(n+1)/2 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      rw [key 2026]; norm_num
    have hS2 : (∑ i ∈ Finset.range 2026, ((i:ℝ)+1)^2) = 2774077201 := by
      have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((i:ℝ)+1)^2) = (n:ℝ)*(n+1)*(2*n+1)/6 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      rw [key 2026]; norm_num
    rw [hS1, hS2]
    norm_num
  rw [h1, h2]
  norm_num

end Native.Competemath.P211
