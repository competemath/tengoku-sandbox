-- jinshi: only duplicate
/-
Jinshi fixture for `duplicate`: the same statement proved twice (docs/jinshi.md), compiled against Lean's own library with
`--seed Init`, so a statement Init already proves is a duplicate of the seed. Duplicate.expected.tsv names what must be found.
-/
namespace JinshiFixtures

-- a library theorem that proves again what the seed has (`Nat.add_zero (n : Nat) : n + 0 = n`, Init.Core)
theorem dupOfSeed (n : Nat) : n + 0 = n := Nat.add_zero n

-- two theorems of one library with one statement under different binder names (redundancy within the library)
theorem twinA (a : Nat) : a + a + 0 = a + a := Nat.add_zero (a + a)
theorem twinB (b : Nat) : b + b + 0 = b + b := Nat.add_zero (b + b)

-- quiet: a statement proved once in the whole environment
theorem uniqueClaim (n : Nat) : n + n + n + 0 = n + n + n := Nat.add_zero (n + n + n)

end JinshiFixtures
