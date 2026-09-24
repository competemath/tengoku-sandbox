theorem vac_lt_zero (n : Nat) (h : n < 0) : n = 5 := by omega
theorem vac_two_bounds (n : Nat) (h₁ : 5 < n) (h₂ : n < 3) : n * n = 7 := by omega
theorem vac_self (p : Prop) (h : p) (h' : ¬ p) : 1 = 2 := absurd h h'
theorem fine_pos (n : Nat) (h : 0 < n) : n ≠ 0 := by omega
theorem negation_not_flagged (n : Nat) : ¬ n < 0 := by omega
theorem ne_not_flagged (n : Nat) (h : 0 < n) : n ≠ 0 := Nat.pos_iff_ne_zero.mp h
