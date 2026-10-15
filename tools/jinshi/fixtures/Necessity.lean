-- jinshi: only necessity
/-
Jinshi fixture for `necessity` (docs/jinshi.md): theorems whose hypotheses are, or are not, justified by a counterexample in
the small domain, against Lean's own library. Necessity.expected.tsv names what must be found; the rest must stay quiet.
-/
namespace JinshiFixtures

-- `h` is justified: at n = 0 the conclusion fails (0 - 1 + 1 = 0 is false)
theorem sub_add (n : Nat) (h : n > 0) : n - 1 + 1 = n := by omega

-- `h` is neither used by the proof nor justified: n + 0 = n holds for every n
theorem over_hyp (n : Nat) (h : n > 5) : n + 0 = n := Nat.add_zero n

-- both justified (a = 0, b = 1 and a = 1, b = 0): the badge
theorem two_hyps (a b : Nat) (ha : a > 0) (hb : b > 0) : a * b > 0 := Nat.mul_pos ha hb

-- `h` is justified by b = false
theorem bool_case (b : Bool) (h : b = true) : (b && true) = true := by subst h; rfl

-- quiet: no hypothesis
theorem no_hyp (n : Nat) : n + 0 = n := Nat.add_zero n

end JinshiFixtures
