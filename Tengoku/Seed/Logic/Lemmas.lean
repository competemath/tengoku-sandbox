/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku.Seed.Logic.Basic
public import Tengoku.Seed.Tactic.Convert
public import Tengoku.Seed.Tactic.SplitIfs
public import Tengoku.Seed.Tactic.Tauto

/-!
# More basic logic properties

A few more logic lemmas. These are in their own file, rather than `Logic.Basic`, because it is
convenient to be able to use the `tauto` or `split_ifs` tactics.

## Implementation notes
We spell those lemmas out with `dite` and `ite` rather than the `if then else` notation because this
would result in less delta-reduced statements.
-/

public section

/--
@isnad1 id=iff.0h3v.s4.aaf9e3e7f150 from=seed src=0 shape=f998172a vocab=e3b0c442
-/
theorem iff_assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c)) := by tauto
/--
@isnad1 id=iff.0h3v.s4.6db781a28db3 from=seed src=0 shape=c8be3529 vocab=e3b0c442
-/
theorem iff_left_comm {a b c : Prop} : (a ↔ (b ↔ c)) ↔ (b ↔ (a ↔ c)) := by tauto
/--
@isnad1 id=iff.0h3v.s4.b09301482c07 from=seed src=0 shape=2cc1a8fd vocab=e3b0c442
-/
theorem iff_right_comm {a b c : Prop} : ((a ↔ b) ↔ c) ↔ ((a ↔ c) ↔ b) := by tauto

protected alias ⟨HEq.eq, Eq.heq⟩ := heq_iff_eq

variable {α : Sort*} {p q : Prop} [Decidable p] [Decidable q] {a b c : α}

/--
@isnad1 id=eq.0h6v.s6.a58c0e3f9f32 from=seed src=0 shape=8e222ae9 vocab=b35639d5
-/
theorem dite_dite_distrib_left {a : p → α} {b : ¬p → q → α} {c : ¬p → ¬q → α} :
    (dite p a fun hp ↦ dite q (b hp) (c hp)) =
      dite q (fun hq ↦ (dite p a) fun hp ↦ b hp hq) fun hq ↦ (dite p a) fun hp ↦ c hp hq := by
  split_ifs <;> rfl

/--
@isnad1 id=eq.0h6v.s6.10693bf10568 from=seed src=0 shape=1335eb6f vocab=b35639d5
-/
theorem dite_dite_distrib_right {a : p → q → α} {b : p → ¬q → α} {c : ¬p → α} :
    dite p (fun hp ↦ dite q (a hp) (b hp)) c =
      dite q (fun hq ↦ dite p (fun hp ↦ a hp hq) c) fun hq ↦ dite p (fun hp ↦ b hp hq) c := by
  split_ifs <;> rfl

/--
@isnad1 id=eq.0h6v.s5.1ac9a0577012 from=seed src=0 shape=5db105d4 vocab=84c97b84
-/
theorem ite_dite_distrib_left {a : α} {b : q → α} {c : ¬q → α} :
    ite p a (dite q b c) = dite q (fun hq ↦ ite p a <| b hq) fun hq ↦ ite p a <| c hq :=
  dite_dite_distrib_left

/--
@isnad1 id=eq.0h6v.s5.5eca40687f3a from=seed src=0 shape=bd994d8b vocab=84c97b84
-/
theorem ite_dite_distrib_right {a : q → α} {b : ¬q → α} {c : α} :
    ite p (dite q a b) c = dite q (fun hq ↦ ite p (a hq) c) fun hq ↦ ite p (b hq) c :=
  dite_dite_distrib_right

/--
@isnad1 id=eq.0h6v.s5.b82c160821ca from=seed src=0 shape=f6bc047d vocab=84c97b84
-/
theorem dite_ite_distrib_left {a : p → α} {b : ¬p → α} {c : ¬p → α} :
    (dite p a fun hp ↦ ite q (b hp) (c hp)) = ite q (dite p a b) (dite p a c) :=
  dite_dite_distrib_left

/--
@isnad1 id=eq.0h6v.s5.5c6054564791 from=seed src=0 shape=c03629d8 vocab=84c97b84
-/
theorem dite_ite_distrib_right {a : p → α} {b : p → α} {c : ¬p → α} :
    dite p (fun hp ↦ ite q (a hp) (b hp)) c = ite q (dite p a c) (dite p b c) :=
  dite_dite_distrib_right

/--
@isnad1 id=eq.0h6v.s5.43f1861c47a6 from=seed src=0 shape=c765ca47 vocab=af84458f
-/
theorem ite_ite_distrib_left : ite p a (ite q b c) = ite q (ite p a b) (ite p a c) :=
  dite_dite_distrib_left

/--
@isnad1 id=eq.0h6v.s5.65c0d0cee96f from=seed src=0 shape=d23df98f vocab=af84458f
-/
theorem ite_ite_distrib_right : ite p (ite q a b) c = ite q (ite p a c) (ite p b c) :=
  dite_dite_distrib_right

/--
@isnad1 id=iff.0h1v.s4.9e9ef6e55130 from=seed src=0 shape=cc7895d2 vocab=e3b0c442
-/
lemma Prop.forall {f : Prop → Prop} : (∀ p, f p) ↔ f True ∧ f False :=
  ⟨fun h ↦ ⟨h _, h _⟩, by rintro ⟨h₁, h₀⟩ p; by_cases hp : p <;> simp only [hp] <;> assumption⟩

/--
@isnad1 id=iff.0h1v.s4.df58c41d53f0 from=seed src=0 shape=39538981 vocab=e3b0c442
-/
lemma Prop.exists {f : Prop → Prop} : (∃ p, f p) ↔ f True ∨ f False :=
  ⟨fun ⟨p, h⟩ ↦ by refine (em p).imp ?_ ?_ <;> intro H <;> convert! h <;> simp [H],
    by rintro (h | h) <;> exact ⟨_, h⟩⟩
