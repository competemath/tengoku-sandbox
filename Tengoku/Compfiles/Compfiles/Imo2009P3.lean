/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hillosanation
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2009, Problem 3

Suppose that $s_1, s_2, s_3, \ldots$ is a strictly increasing sequence of
positive integers such that the subsequences
$$s_{s_1}, s_{s_2}, s_{s_3}, \ldots \quad\text{and}\quad s_{s_1+1}, s_{s_2+1}, s_{s_3+1}, \ldots$$
are both arithmetic progressions. Prove that the sequence
$s_1, s_2, s_3, \ldots$ is itself an arithmetic progression.
-/

namespace Imo2009P3

/-- A sequence `f : ℕ → ℕ` is an arithmetic progression. -/
def IsArithProg (f : ℕ → ℕ) : Prop := ∃ d : ℕ, ∀ n, f (n + 1) = f n + d

-- Adapted from the solution by Alex Zhai presented by Evan Chen.
-- Note the writeup uses A as the upper bound, when the correct upper bound is D.
-- The requirement that $s_i$ is positive can be removed.

lemma IsArithProg_iff {f: ℕ → ℕ} : IsArithProg f ↔ ∃ d r : ℕ, ∀ n, f n = d * n + r := by
  refine ⟨fun ⟨d, h⟩ => ⟨d, f 0, fun n => ?_⟩, fun ⟨d, r, h⟩ => ⟨d, fun n => by simp [h]; ring_nf⟩⟩
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih]; ring_nf

lemma strictMono_add_right_le {s : ℕ → ℕ} (hs: StrictMono s) {a b : ℕ} : s a + b ≤ s (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp_rw [← add_assoc]
    rw [Nat.add_one_le_iff]
    exact ih.trans_lt <| hs <| lt_add_one _

end Imo2009P3
