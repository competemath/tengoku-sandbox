/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2010, Problem 5

Each of the six boxes $B_1, B_2, B_3, B_4, B_5, B_6$ initially contains one coin.
The following two types of operations are allowed:

1. Choose a non-empty box $B_j, 1 ≤ j ≤ 5$, remove one coin from $B_j$ and
add two coins to $B_{j+1}$;
2. Choose a non-empty box $B_k, 1 ≤ k ≤ 4$, remove one coin from $B_k$ and swap
the contents (possibly empty) of the boxes $B_{k+1}$ and $B_{k+2}$.

Determine if there exists a finite sequence of operations of the allowed types, such
that the five boxes $B_1, B_2, B_3, B_4, B_5$ become empty, while box $B_6$ contains exactly
$2010^{2010^{2010}}$ coins.
-/

open Pi Equiv Function

namespace Imo2010P5

/-- The predicate defining states of boxes reachable by the given moves. -/
inductive Reachable : (Fin 6 → ℕ) → Prop
  /-- The starting position with one coin in each box -/
  | base : Reachable 1
  /-- Remove a coin from $B_j$ and add two coins to $B_{j+1}$ -/
  | move1 {B i} (rB : Reachable B) (hi : i < 5) (pB : 0 < B i) :
      Reachable (B - single i 1 + single (i + 1) 2)
  /-- Remove a coin from $B_k$ and swap $B_{k+1}$ and $B_{k+2}$ -/
  | move2 {B i} (rB : Reachable B) (hi : i < 4) (pB : 0 < B i) :
      Reachable (B ∘ swap (i + 1) (i + 2) - single i 1)

/-
# Solution

We follow the solution from https://web.evanchen.cc/exams/IMO-2010-notes.pdf.

From the initial state we can reach `(0, 0, 5, 11, 0, 0)`; we now ignore the first two boxes.
On any three adjacent boxes reading `(n, 0, 0)` with `n > 0` we can change them to `(0, 2^n, 0)`:
```
(n, 0, 0) →(move 1) (n-1, 2, 0)
          →(2× move 1) (n-1, 0, 4) →(move 2) (n-2, 4, 0)
          →(4× move 1) (n-2, 0, 8) →(move 2) (n-3, 8, 0)
          → ...
          →(2^(n-1)× move 1) (1, 0, 2^n) →(move 2) (0, 2^n, 0)
```
Thus we can get more than enough coins, all in box 4, as follows:
```
(5, 11, 0, 0) → (5, 0, 2^11, 0) →(move 2) (4, 2^11, 0, 0)
              → (4, 0, 2^2^11, 0) →(move 2) (3, 2^2^11, 0, 0)
              → ...
              → (1, 0, 2^2^2^2^2^11, 0) →(move 2) (0, 2^2^2^2^2^11, 0, 0)
```
We now ignore the third box. Let `T = 2010^2010^2010` be the target number of coins;
since `T < 2^2^2^2^2^11` and `T` is divisible by 4 we can drop coins from box 4 by using move 2
to swap the empty boxes 5 and 6 until we have `(T/4, 0, 0)`. Then we can repeatedly use move 1
to get `(0, T/2, 0)` and finally `(0, 0, T)`.
-/

lemma single_succ {k : ℕ} {i : Fin 6} : (single (i + 1) k : Fin 6 → ℕ) i = 0 := by simp

lemma single_succ' {k : ℕ} {i : Fin 6} : (single i k : Fin 6 → ℕ) (i + 1) = 0 := by simp

lemma single_add_two {k : ℕ} {i : Fin 6} : (single (i + 2) k : Fin 6 → ℕ) i = 0 := by simp

namespace Reachable

/-- The key power tower inequality in the solution. -/
lemma tower_inequality {m n : ℕ} (hm : m = 2010) (hn : n = 11) :
    2010 ^ 2010 ^ m ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ n := by
  calc
    _ ≤ 2 ^ (11 * 2010 ^ m) := by rw [pow_mul]; gcongr <;> lia
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two ?_
  calc
    _ ≤ 2 ^ (4 + 11 * m) := by rw [pow_add, pow_mul]; gcongr <;> lia
    _ ≤ _ := Nat.pow_le_pow_right Nat.zero_lt_two ?_
  calc
    _ ≤ 2 ^ 2 ^ 2 ^ 2 := by rw [hm]; lia
    _ ≤ _ := by
      iterate 3 apply Nat.pow_le_pow_right Nat.zero_lt_two
      lia

end Reachable

abbrev solution : Bool := true

end Imo2010P5
