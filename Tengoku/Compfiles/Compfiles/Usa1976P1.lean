/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1976, Problem 1

The squares of a 4 x 7 chess board are colored red or blue. Show that however
the coloring is done, we can find a rectangle with four distinct corner
squares all the same color. Find a counter-example to show that this is not
true for a 4 x 6 board.
-/

namespace Usa1976P1

/-- A coloring (true = red, false = blue) of an `m × n` board has a
monochromatic rectangle if there are two distinct rows and two distinct
columns whose four intersection squares all have the same color. -/
def HasMonoRectangle {m n : ℕ} (c : Fin m → Fin n → Bool) : Prop :=
  ∃ r1 r2 : Fin m, ∃ j1 j2 : Fin n, ∃ b : Bool,
    r1 ≠ r2 ∧ j1 ≠ j2 ∧
    c r1 j1 = b ∧ c r2 j1 = b ∧ c r1 j2 = b ∧ c r2 j2 = b

/-- A 4 x 6 coloring with no monochromatic rectangle. Written row by row,
with `true` = red:
```
R B R B R B
R B B R B R
B R R B B R
B R B R R B
```
Every column has two red and two blue squares, and no two columns have their
red squares in the same two rows or their blue squares in the same two rows,
so there can be no monochromatic rectangle. -/
abbrev counterexample : Fin 4 → Fin 6 → Bool :=
  ![![true,  false, true,  false, true,  false],
    ![true,  false, false, true,  false, true ],
    ![false, true,  true,  false, false, true ],
    ![false, true,  false, true,  true,  false]]

/-- The monochromatic pairs of rows in column `j`, tagged with their color:
`(r1, r2, b)` means `r1 < r2` and both squares `(r1, j)` and `(r2, j)` have
color `b`. -/
def monoTriples (c : Fin 4 → Fin 7 → Bool) (j : Fin 7) :
    Finset (Fin 4 × Fin 4 × Bool) :=
  Finset.univ.filter fun t ↦ t.1 < t.2.1 ∧ c t.1 j = t.2.2 ∧ c t.2.1 j = t.2.2

/-- In any column of 4 squares colored with 2 colors, if `k` squares are red
then `4 - k` are blue, so the number of monochromatic pairs of squares is
`k.choose 2 + (4 - k).choose 2 ≥ 1 + 1 = 2`. There are only 16 possible
columns, so we check them all. -/
lemma two_le_card_monoTriples (c : Fin 4 → Fin 7 → Bool) (j : Fin 7) :
    2 ≤ (monoTriples c j).card := by
  have h : ∀ d : Fin 4 → Bool,
      2 ≤ (Finset.univ.filter fun t : Fin 4 × Fin 4 × Bool ↦
        t.1 < t.2.1 ∧ d t.1 = t.2.2 ∧ d t.2.1 = t.2.2).card := by
    decide
  exact h (fun r ↦ c r j)

/-- There are `6` pairs of distinct rows and `2` colors, hence `12` colored
pairs of rows. -/
lemma card_colored_rowPairs :
    (Finset.univ.filter fun t : Fin 4 × Fin 4 × Bool ↦ t.1 < t.2.1).card = 12 := by
  decide

end Usa1976P1
