/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# International Mathematical Olympiad 1977, Problem 6

Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.
Prove that `f(n) = n` for all `n`.
-/

namespace Imo1977P6

/-
We first prove the problem statement for `f : ℕ → ℕ`
then we use it to prove the statement for positive naturals.
-/

theorem imo1977_p6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n := by
  have h' : ∀ k n : ℕ, k ≤ n → k ≤ f n := by
    intro k
    induction k with
    | zero => intros; exact Nat.zero_le _
    | succ k h_ind =>
      intro n hk
      apply Nat.succ_le_of_lt
      calc
        k ≤ f (f (n - 1)) := h_ind _ (h_ind (n - 1) (le_tsub_of_add_le_right hk))
        _ < f n := tsub_add_cancel_of_le (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hk) ▸ h _
  have hf : ∀ n, n ≤ f n := fun n => h' n n rfl.le
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ fun _ => lt_of_le_of_lt (hf _) (h _)
  intro
  exact Nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))

end Imo1977P6
