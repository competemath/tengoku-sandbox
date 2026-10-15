-- jinshi: only entailed
/-
Jinshi fixture for `entailed` (docs/jinshi.md): theorems that are one-step consequences of Lean's own library (the self-test's
seed is `Init`), and one that is not, against Lean's own library. Entailed.expected.tsv names what must be found; the rest must
stay quiet.
-/
namespace JinshiFixtures

-- entailed by the seed: a restatement of Nat.add_comm, and a statement Nat.add_zero proves
theorem restated (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem restated2 (n : Nat) : n + 0 = n := by simp

-- quiet: a claim about a definition of this module, which no theorem of Init proves in one step
def tri (n : Nat) : Nat := n * (n + 1) / 2
theorem tri_two : tri 2 = 3 := by decide
theorem tri_le (n : Nat) : tri n ≤ n * (n + 1) := Nat.div_le_self _ _

end JinshiFixtures
