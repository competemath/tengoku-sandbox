-- jinshi: only forensics
/-
Jinshi fixture for `forensics` (docs/jinshi.md): proof terms that stress or trust the kernel's own machinery, compiled against Lean's
own library. Forensics.expected.tsv names what must be found; the honest theorems at the end must stay quiet.
-/
namespace JinshiFixtures

-- a numeral ≥ 2^64 in the statement: the kernel's bignum arithmetic
theorem big : (18446744073709551616 : Nat) = 18446744073709551616 := rfl

-- decide on a proposition of a few hundred nodes: the kernel ran the decision procedure
theorem dec : (List.range 30).map (fun k => k * k % 7) =
    [0, 1, 4, 2, 2, 4, 1, 0, 1, 4, 2, 2, 4, 1, 0, 1, 4, 2, 2, 4, 1, 0, 1, 4, 2, 2, 4, 1, 0, 1] := by decide

-- a cast chain of depth 60: kernel reduction carries the goal through every Eq.mpr
theorem casts : (0 : Nat) = 0 := by
  iterate 60 refine Eq.mpr (Eq.refl _) ?_
  rfl

-- a proof of hundreds of nodes for a statement of one node: the ratio
theorem ratio : True := by
  have _ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
    61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90,
    91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
  trivial

-- nearly trivial: `rfl` on a statement of more than 30 nodes, the kernel's definitional unfolding is the whole proof
theorem triv (a b c d e f : Nat) : a + b + c + d + e + f = a + b + c + d + e + f := rfl

-- a proof that mentions a constant with `implemented_by`: the kernel checked `checkedId`'s Lean definition, `compiledId` is what runs
def compiledId (n : Nat) : Nat := n
@[implemented_by compiledId] def checkedId (n : Nat) : Nat := n
theorem via_compiled : checkedId 3 = 3 := rfl

-- quiet: honest theorems, by a seed lemma and by automation
theorem honest (n : Nat) : n + 0 = n := Nat.add_zero n
theorem honest_sub (a b : Nat) : a - b + b = a ∨ a < b := by omega
theorem honest_dec : (List.range 10).foldl (· + ·) 0 = 45 := by decide

end JinshiFixtures
