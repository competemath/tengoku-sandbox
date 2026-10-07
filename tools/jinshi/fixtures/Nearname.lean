-- jinshi: only nearname
/-
Jinshi fixture for `nearname`: names that are almost a name the seed already has, compiled against Lean's own library (the "seed"
of the self-test is `Init`). Nearname.expected.tsv names what must be found; every other declaration here must stay quiet.
-/
namespace JinshiFixtures

-- homoglyph: `Nаt` with a Cyrillic а (U+0430) reads as `Nat`; `zero​width` holds a zero-width space (U+200B)
def «Nаt».succ' (n : Nat) : Nat := n + 1
def «zero​width» (n : Nat) : Nat := n

-- near `Nat.add_comm` (Init): one letter short, a capital, a trailing digit; near `List.length`: two letters swapped
theorem Nat.add_com (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem Nat.Add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem Nat.add_comm1 (a b : Nat) : a + b = b + a := Nat.add_comm a b
def List.lenght (l : List Nat) : Nat := l.length

-- theorems whose statements use a near name
theorem succ'_pos (n : Nat) : 0 < «Nаt».succ' n := Nat.succ_pos n
theorem lenght_nil : List.lenght [] = 0 := rfl

-- quiet: honest names, Greek letters and subscripts, a seed name used as the seed's
theorem Nat.myLemma (n : Nat) : n + 0 = n := Nat.add_zero n
def swapTypes (α β : Type) : Type := β × α
theorem αβ_refl (α : Type) (x : α) : x = x := rfl
def Nat.myLemma₁ (n : Nat) : Nat := n + 1
theorem uses_seed (a b : Nat) : a + b = b + a := Nat.add_comm a b

end JinshiFixtures
