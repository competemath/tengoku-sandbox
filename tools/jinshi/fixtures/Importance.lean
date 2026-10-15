-- jinshi: only importance
namespace JinshiFixtures

theorem base_fact (n : Nat) : n + 0 = n := Nat.add_zero n
theorem user1 (n : Nat) : n + 0 + 0 = n := Eq.trans (base_fact (n + 0)) (base_fact n)
theorem user2 (n : Nat) : (n + 0) * 1 = n := by rw [base_fact, Nat.mul_one]
theorem leaf (n : Nat) : n * 0 = 0 := Nat.mul_zero n

end JinshiFixtures
