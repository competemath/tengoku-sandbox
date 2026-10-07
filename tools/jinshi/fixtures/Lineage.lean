-- jinshi: only lineage
namespace JinshiFixtures

-- the same proof term twice, under different names and binder names: a copy within the library (info)
theorem copyA (a b : Nat) : a + b + 0 = b + a := by rw [Nat.add_zero, Nat.add_comm]
theorem copyB (x y : Nat) : x + y + 0 = y + x := by rw [Nat.add_zero, Nat.add_comm]
-- a different proof of the same statement: quiet under lineage (duplicate's business)
theorem otherProof (a b : Nat) : a + b + 0 = b + a := by omega
-- a seed theorem's proof, copied: the fixture restates Nat.succ_ne_zero with its exact proof term
theorem seedCopy (n : Nat) : n.succ ≠ 0 := fun h => Nat.noConfusion h

end JinshiFixtures
