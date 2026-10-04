-- Tengoku.EquationalTheories.Equations.LawsComplete: verified translations of equational_theories/Equations/LawsComplete.lean (8 theorems)
import Tengoku
import Lean.ToExpr
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Lean
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.Seed.Std.Data.Array.Lemmas
import Tengoku.Seed.Tactic.Cases
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

@[simp] theorem _root_.Ordering.then_swap_self (o : Ordering) : o.then o.swap = o
:= by cases o <;> rfl

def _root_.List.cmp {α} [Ord α] : List α → List α → Ordering
  | [], [] => .eq
  | [], _::_ => .lt
  | _::_, [] => .gt
  | a::as, b::bs => (compare a b).then (List.cmp as bs)

theorem _root_.List.cmp_eq_eq {α} [LinearOrder α] {l1 l2 : List α} :
    l1.cmp l2 = .eq ↔ l1 = l2
:= by
  induction l1 generalizing l2 <;> cases l2 <;>
    simp [List.cmp, Ordering.then_eq_eq, *]

theorem _root_.List.cmp_swap_aux {α} [LinearOrder α] (a b : α) :
    (compare a b).swap = compare b a := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_gt_iff_gt.2 h]; rfl
  · subst h; rw [compare_eq_iff_eq.2 rfl]; rfl
  · rw [compare_gt_iff_gt.2 h, compare_lt_iff_lt.2 h]; rfl

theorem _root_.List.cmp_swap {α} [LinearOrder α] (l1 l2 : List α) :
    (l1.cmp l2).swap = l2.cmp l1
:= by
  rw [List.cmp.eq_def, List.cmp.eq_def]
  split <;> first | rfl | rw [Ordering.swap_then, List.cmp_swap_aux, List.cmp_swap]

def TestNat (n : Nat) (P : Nat → Prop) : Prop := ∀ i < n, P i

theorem TestNat.zero {P} : TestNat 0 P
:= by simp [TestNat]

theorem TestNat.succ {n P} (h1 : TestNat n P) (h2 : P n) : TestNat (n+1) P
:= by
  simpa only [TestNat, Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq, and_true, h2]

def TestAllSplits' (i j : Nat) (P : Nat → Nat → Prop) : Prop :=
  ∀ i' < i, P i' (j + (i - i'))

theorem TestAllSplits'.zero {n : Nat} {P : Nat → Nat → Prop} : TestAllSplits' 0 n P
:= by
  simp [TestAllSplits', *]

def TestAllSplits (n : Nat) (P : Nat → Nat → Prop) : Prop := ∀ i j, i + j = n → P i j

theorem TestAllSplits.start {n P} (h1 : TestAllSplits' n 0 P) (h2 : P n 0) : TestAllSplits n P
:= by
  have : ∀ i ≤ n, P i (n - i) := by
    simpa [TestAllSplits', Nat.le_iff_lt_or_eq, or_imp, forall_and, h2] using h1
  intro i j eq
  cases Nat.eq_sub_of_add_eq' eq
  exact this _ (by omega)

theorem TestAllSplits'.succ {i j P}
    (h1 : TestAllSplits' i (j+1) P) (h2 : P i (j+1)) : TestAllSplits' (i+1) j P
:= by
  simp only [TestAllSplits', Nat.lt_succ_iff_lt_or_eq, or_imp, forall_and, forall_eq,
    Nat.add_sub_cancel_left] at *
  exact ⟨fun i' h => by convert h1 i' h using 1; omega, h2⟩

end EquationalTheories
