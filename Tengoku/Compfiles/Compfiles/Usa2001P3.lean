/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2001, Problem 3

Let a,b,c ≥ 0 be real numbers satsifying

        a² + b² + c² + abc = 4.

Show that

        0 ≤ ab + bc + ca - abc ≤ 2.
-/

namespace Usa2001P3

@[reducible]
noncomputable def f (a b c : ℝ) : ℝ := a^2 + b^2 + c^2 + a * b * c
@[reducible]
def g (a b c : ℝ) : ℝ := a * b + b * c + c * a - a * b * c

theorem feq (a b c : ℝ) : f a b c = a^2 + b^2 + c^2 + a * b * c := rfl
theorem geq (a b c : ℝ) : g a b c = a * b + b * c + c * a - a * b * c := rfl

lemma usa2001_p3_lemma (a b c : ℝ) (ha : 0 ≤ a)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4)
    (hbc : (b - 1) * (c - 1) ≥ 0) :
    a * b + b * c + c * a - a * b * c ≤ 2 := by
  have eq1 := calc
    (2 + a) * (2 - a) = 4 - a ^ 2 := by ring_nf
    _ = a ^ 2 + b ^ 2 + c ^ 2 + a * b * c - a ^ 2 := by rw [h]
    _ = (b ^ 2 + c ^ 2) + a * b * c := by ring_nf
    _ ≥ 2 * b * c + a * b * c := by rel [two_mul_le_add_sq b c]
    _ = (2 + a) * (b * c) := by ring_nf
  have a2gt0 : 2 + a > 0 := by linarith
  have bc := (mul_le_mul_iff_right₀ a2gt0).mp eq1
  calc
    a * b + b * c + c * a - a * b * c = a * b + b * c + a * c * (1 - b) := by ring_nf
    _ ≤ a * b + (2 - a) + a * c * (1 - b) := by gcongr
    _ = 2 - a * ((b - 1) * (c - 1)) := by ring_nf
    _ ≤ 2 - 0 := by gcongr; positivity
    _ = 2 := by norm_num

end Usa2001P3
