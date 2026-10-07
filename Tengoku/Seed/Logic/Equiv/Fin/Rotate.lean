/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Lawrence Wu, Jeremy Tan
-/
module

public import Tengoku.Seed.Algebra.Group.Fin.Basic
public import Tengoku.Seed.Logic.Equiv.Fin.Basic

/-!
# Cyclic permutations on `Fin n`

This file defines
* `finRotate`, which corresponds to the cycle `(1, ..., n)` on `Fin n`
* `finCycle`, the permutation that adds a fixed number to each element of `Fin n`
and proves various lemmas about them.
-/

@[expose] public section

open Nat

variable {n : ℕ}

/-- Rotate `Fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))

/--
@isnad1 id=eq.0h0v.s4.0ce2cd402063 from=seed src=0 shape=1bddbd7e vocab=d0b9e3bf
-/
@[simp] lemma finRotate_zero : finRotate 0 = Equiv.refl _ := rfl

/--
@isnad1 id=eq.0h1v.s6.3d244e50a0c1 from=seed src=0 shape=c8b705f5 vocab=2f62e85f
-/
lemma finRotate_succ (n : ℕ) :
    finRotate (n + 1) = finAddFlip.trans (finCongr (Nat.add_comm 1 n)) := rfl

/--
@isnad1 id=eq.1h2v.s7.57e1718d854f from=seed src=0 shape=15a7a2d7 vocab=396bcafa
-/
theorem finRotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]

/--
@isnad1 id=eq.0h1v.s7.63f0c644f98c from=seed src=0 shape=5aeb60c8 vocab=9b048e94
-/
theorem finRotate_last' : finRotate (n + 1) ⟨n, by lia⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp

/--
@isnad1 id=eq.0h1v.s7.1f21c4c1d40f from=seed src=0 shape=37f2e891 vocab=c6fe6d45
-/
theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'

/--
@isnad1 id=eq.0h4v.s7.75b6110a039c from=seed src=0 shape=0d756b28 vocab=6e9f4527
-/
theorem Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dite_eq_left h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last', Fin.snoc, Fin.cons, dite_eq_right (lt_irrefl _)]
    rfl

/--
@isnad1 id=eq.0h0v.s4.a489955f697a from=seed src=0 shape=1bddbd7e vocab=d0b9e3bf
-/
@[simp]
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _

/--
@isnad1 id=eq.0h2v.s5.a39a67cd8d23 from=seed src=0 shape=be869774 vocab=1c16de7b
-/
@[simp]
theorem finRotate_apply (i : Fin n) : haveI := i.neZero; finRotate n i = i + 1 := by
  match n with
  | 0 => exact i.elim0
  | 1 => exact @Subsingleton.elim (Fin 1) _ _ _
  | n + 2 =>
    obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
    · simp [finRotate_last]
    · cases i
      simp only [Fin.lt_def, Fin.val_last] at h
      simp [finRotate_of_lt h, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]

/--
@isnad1 id=eq.0h2v.s8.36f98f7fbbd8 from=seed src=0 shape=bc26a126 vocab=eb83c56c
-/
@[deprecated finRotate_apply (since := "2026-03-29")]
theorem finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := by
  simp

/--
@isnad1 id=eq.0h1v.s5.8792bcce36d0 from=seed src=0 shape=422bbfd3 vocab=d2d386b7
-/
theorem finRotate_apply_zero : finRotate n.succ 0 = 1 := by
  simp

/--
@isnad1 id=eq.1h2v.s7.e2559a79441a from=seed src=0 shape=058c73f6 vocab=73cccc6d
-/
theorem coe_finRotate_of_ne_last {i : Fin n.succ} (h : i ≠ Fin.last n) :
    (finRotate (n + 1) i : ℕ) = i + 1 := by
  rw [finRotate_apply]
  have : (i : ℕ) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this

/--
@isnad1 id=eq.0h2v.s6.37a8f318c3b8 from=seed src=0 shape=5acccc0d vocab=ed9a640c
-/
theorem coe_finRotate (i : Fin n.succ) :
    (finRotate n.succ i : ℕ) = if i = Fin.last n then (0 : ℕ) else i + 1 := by
  rw [finRotate_apply, Fin.val_add_one i]

/--
@isnad1 id=iff.0h2v.s7.6cdf9b0ea865 from=seed src=0 shape=03a5ec6a vocab=93a48adc
-/
theorem lt_finRotate_iff_ne_last (i : Fin (n + 1)) :
    i < finRotate _ i ↔ i ≠ Fin.last n := by
  simpa using Fin.lt_last_iff_ne_last

/--
@isnad1 id=iff.0h2v.s6.74cac23814b2 from=seed src=0 shape=cbe90ee6 vocab=f99abf23
-/
theorem lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) :
    i < finRotate _ i ↔ i ≠ -1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last, ne_eq, not_iff_not, ← Fin.neg_last, neg_neg]

/--
@isnad1 id=eq.0h2v.s6.fc4a039cd613 from=seed src=0 shape=b23a27b2 vocab=c832a2c4
-/
@[simp]
lemma finRotate_symm_apply (i : Fin n) : haveI := i.neZero; (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero i.pos.ne'
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_apply, sub_add_cancel]

/--
@isnad1 id=eq.0h2v.s6.f363f43f753e from=seed src=0 shape=0b02e5bb vocab=92833e4b
-/
@[deprecated finRotate_symm_apply (since := "2026-03-29")]
lemma finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = i - 1 := by
  simp

/--
@isnad1 id=eq.1h2v.s6.adeaa4080514 from=seed src=0 shape=7250c75b vocab=624b1529
-/
lemma coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    ((finRotate _).symm i : ℕ) = i - 1 := by
  rwa [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]

/--
@isnad1 id=iff.0h2v.s6.2f462d8cb241 from=seed src=0 shape=23cd7f72 vocab=8b4829c9
-/
theorem finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) :
    (finRotate _).symm i < i ↔ i ≠ 0 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨ne_zero_of_lt, fun hi ↦ ?_⟩
  rw [Fin.lt_def, coe_finRotate_symm_of_ne_zero hi]
  exact sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) zero_lt_one

/-- The permutation on `Fin n` that adds `k` to each number. -/
@[simps]
def finCycle (k : Fin n) : Equiv.Perm (Fin n) where
  toFun i := i + k
  invFun i := i - k
  left_inv i := by have := NeZero.of_pos k.pos; simp
  right_inv i := by have := NeZero.of_pos k.pos; simp

/--
@isnad1 id=eq.0h2v.s6.097ce418d39e from=seed src=0 shape=c0749eb7 vocab=15690ef0
-/
lemma finCycle_eq_finRotate_iterate {k : Fin n} : finCycle k = (finRotate n)^[k.1] := by
  match n with
  | 0 => exact k.elim0
  | n + 1 =>
    ext i; induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      rw [Fin.val_eq_val, Fin.val_castSucc] at ih
      rw [Fin.val_succ, Function.iterate_succ', Function.comp_apply, ← ih, finRotate_apply,
        finCycle_apply, finCycle_apply, add_assoc, Fin.coeSucc_eq_succ]
