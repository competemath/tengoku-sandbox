/-
Copyright (c) 2026 lean-tom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-tom (with assistance from Gemini)
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1968, Problem 6

For every natural number n, evaluate the sum
∑_{k=0}^{∞} [(n + 2^k) / 2^(k+1)]
where [x] denotes the greatest integer less than or equal to x.
-/

namespace Imo1968P6

-- Lemma for the telescoping term structure
lemma term_telescope (n k : ℕ) :
    (n + 2^k) / 2^(k+1) = n / 2^k - n / 2^(k+1) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have h_pos : 0 < 2^k := pow_pos (by norm_num) k
  rw [Nat.add_div_right n h_pos]
  -- Use the identity (a + 1) / 2 = a - a / 2
  have identity (a : ℕ) : (a + 1) / 2 = a - a / 2 := by lia
  rw [identity]
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

/--
The answer is n. We pull this into a `determine` statement as required.
-/
abbrev n_ans (n : ℕ) : ℕ := n

end Imo1968P6
