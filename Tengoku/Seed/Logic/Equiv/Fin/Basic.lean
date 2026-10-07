/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Tengoku.Seed.Data.Fin.VecNotation
public import Tengoku.Seed.Logic.Embedding.Set
public import Tengoku.Seed.Logic.Equiv.Option
public import Tengoku.Seed.Data.Int.Init
public import Tengoku.Seed.Std.Data.Fin.Lemmas

/-!
# Equivalences for `Fin n`
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

variable {m n : ℕ}

/-!
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/

/--
@isnad1 id=eq.0h3v.s8.ed085f61365e from=seed src=0 shape=1f0a2d21 vocab=d30d89ce
-/
theorem Fin.preimage_apply_01_prod {α : Fin 2 → Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : ∀ i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]

/--
@isnad1 id=eq.0h3v.s7.621c2fe60808 from=seed src=0 shape=159485bf vocab=a96eef00
-/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 → α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t

/-- A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`. -/
@[simps! -fullyApplied]
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ ∀ i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

/-- The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoEquiv` and
`prodEquivPiFinTwo`. -/
@[simps -fullyApplied]
def finTwoArrowEquiv (α : Type*) : (Fin 2 → α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `Fin.predAbove` that produces `Option (Fin n)` instead of
mapping both `i.castSucc` and `i.succ` to `i`. -/
def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

/--
@isnad1 id=eq.0h2v.s7.ca4836f7f0fe from=seed src=0 shape=62270976 vocab=978a984e
-/
@[simp]
theorem finSuccEquiv'_at (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']

/--
@isnad1 id=eq.0h3v.s7.5003821b1e7b from=seed src=0 shape=845f29a7 vocab=30ff46f2
-/
@[simp]
theorem finSuccEquiv'_succAbove (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _

/--
@isnad1 id=eq.1h3v.s7.93820af63272 from=seed src=0 shape=8667830f vocab=1da47e2c
-/
theorem finSuccEquiv'_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i) (Fin.castSucc m) = m := by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h, finSuccEquiv'_succAbove]

/--
@isnad1 id=eq.1h3v.s7.e666c4becc7b from=seed src=0 shape=8c0e6894 vocab=37fadd46
-/
theorem finSuccEquiv'_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_of_le_castSucc _ _ h, finSuccEquiv'_succAbove]

/--
@isnad1 id=eq.0h2v.s7.809dd3f80099 from=seed src=0 shape=44d8fc85 vocab=f94cbdc9
-/
@[simp]
theorem finSuccEquiv'_symm_none (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.e087cfd5ef78 from=seed src=0 shape=c7b5ddb4 vocab=f61d5435
-/
@[simp]
theorem finSuccEquiv'_symm_some (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl

/--
@isnad1 id=iff.0h4v.s7.d4decffa2a5b from=seed src=0 shape=551e50e9 vocab=30ff46f2
-/
@[simp]
theorem finSuccEquiv'_eq_some {i j : Fin (n + 1)} {k : Fin n} :
    finSuccEquiv' i j = k ↔ j = i.succAbove k :=
  (finSuccEquiv' i).eq_symm_apply.symm

/--
@isnad1 id=iff.0h3v.s7.c2ef644b5f02 from=seed src=0 shape=b7f4cf13 vocab=978a984e
-/
@[simp]
theorem finSuccEquiv'_eq_none {i j : Fin (n + 1)} : finSuccEquiv' i j = none ↔ i = j :=
  (finSuccEquiv' i).eq_symm_apply.symm.trans eq_comm

/--
@isnad1 id=eq.1h3v.s7.d42662d4a069 from=seed src=0 shape=f0be8776 vocab=17e68c36
-/
theorem finSuccEquiv'_symm_some_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm (some m) = Fin.castSucc m :=
  Fin.succAbove_of_castSucc_lt i m h

/--
@isnad1 id=eq.1h3v.s7.fd93284d1ee3 from=seed src=0 shape=2ec4de6f vocab=a9af5239
-/
theorem finSuccEquiv'_symm_some_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_of_le_castSucc i m h

/--
@isnad1 id=eq.1h3v.s7.d42662d4a069 from=seed src=0 shape=f0be8776 vocab=17e68c36
-/
theorem finSuccEquiv'_symm_coe_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm m = Fin.castSucc m :=
  finSuccEquiv'_symm_some_below h

/--
@isnad1 id=eq.1h3v.s7.fd93284d1ee3 from=seed src=0 shape=2ec4de6f vocab=a9af5239
-/
theorem finSuccEquiv'_symm_coe_above {i : Fin (n + 1)} {m : Fin n} (h : i ≤ Fin.castSucc m) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h

/-- Equivalence between `Fin (n + 1)` and `Option (Fin n)`.
This is a version of `Fin.pred` that produces `Option (Fin n)` instead of
requiring a proof that the input is not `0`. -/
def finSuccEquiv (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0

/--
@isnad1 id=eq.0h1v.s7.97511f085856 from=seed src=0 shape=23dbe886 vocab=2dd2664b
-/
@[simp]
theorem finSuccEquiv_zero : (finSuccEquiv n) 0 = none :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.32b88ba62915 from=seed src=0 shape=c4385551 vocab=a114ada6
-/
@[simp]
theorem finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)

/--
@isnad1 id=eq.0h1v.s8.d422bf9c753a from=seed src=0 shape=5739494c vocab=3506d050
-/
@[simp]
theorem finSuccEquiv_last (n : ℕ) : finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n := rfl

/--
@isnad1 id=eq.0h1v.s7.a4b3f002cf1d from=seed src=0 shape=e91f6d19 vocab=e8b81b42
-/
@[simp]
theorem finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _

/--
@isnad1 id=eq.0h2v.s7.30306a61e3dd from=seed src=0 shape=bd6e3ac2 vocab=fc58b11b
-/
@[simp]
theorem finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m

/--
@isnad1 id=iff.0h3v.s7.dcc546b030dc from=seed src=0 shape=644ac6d5 vocab=a114ada6
-/
@[simp]
theorem finSuccEquiv_eq_some {i : Fin (n + 1)} {j : Fin n} :
    finSuccEquiv n i = j ↔ i = j.succ :=
  (finSuccEquiv n).eq_symm_apply.symm

/--
@isnad1 id=iff.0h2v.s7.3d843505e259 from=seed src=0 shape=ed87c117 vocab=2dd2664b
-/
@[simp]
theorem finSuccEquiv_eq_none {i : Fin (n + 1)} : finSuccEquiv n i = none ↔ i = 0 :=
  (finSuccEquiv n).eq_symm_apply.symm

/-- The equiv version of `Fin.predAbove_zero`.
@isnad1 id=eq.0h1v.s5.f18b356ecdbe from=seed src=0 shape=ff1e5581 vocab=4b57ed19
-/
theorem finSuccEquiv'_zero : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.396efbb8c5bd from=seed src=0 shape=1abddd5a vocab=d2dd50fd
-/
theorem finSuccEquiv'_last_apply_castSucc (i : Fin n) :
    finSuccEquiv' (Fin.last n) (Fin.castSucc i) = i := by
  rw [← Fin.succAbove_last, finSuccEquiv'_succAbove]

/--
@isnad1 id=eq.1h2v.s7.857287e0c41a from=seed src=0 shape=d8ca627f vocab=0dfff9f7
-/
theorem finSuccEquiv'_last_apply {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    finSuccEquiv' (Fin.last n) i = Fin.castLT i (Fin.val_lt_last h) := by
  simp

/--
@isnad1 id=eq.2h3v.s7.1efb1f0a8091 from=seed src=0 shape=51e3036a vocab=6a07a6d3
-/
theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i ≠ Fin.last n) (hj : j ≠ i) :
    finSuccEquiv' i j = (i.castLT (Fin.val_lt_last hi)).predAbove j := by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp

/-- `Fin.succAbove` as a bijection between `Fin n` and `{x : Fin (n + 1) // x ≠ p}`. -/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃ { x : Fin (n + 1) // x ≠ p } :=
  .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩

/--
@isnad1 id=eq.0h3v.s8.f1998359bce9 from=seed src=0 shape=d38776b5 vocab=53e836cc
-/
theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succAbove_ne i⟩ :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.90b23c0ce309 from=seed src=0 shape=c6ca3e0e vocab=d97c1fd2
-/
theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x ≠ Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]

/--
@isnad1 id=eq.1h3v.s8.d3ba7b7cf87f from=seed src=0 shape=c2a55e9f vocab=f1053cab
-/
theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p ≠ Fin.last n)
    (x : { x : Fin (n + 1) // x ≠ p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

/-- `Equiv` between `Fin (n + 1)` and `Option (Fin n)` sending `Fin.last n` to `none` -/
def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)

/--
@isnad1 id=eq.0h2v.s6.72b841834afd from=seed src=0 shape=c4385551 vocab=9b7ddb84
-/
@[simp]
theorem finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) = some i :=
  finSuccEquiv'_below i.2

/--
@isnad1 id=eq.0h1v.s6.84bf8fc48dce from=seed src=0 shape=e0860a9c vocab=8ceb7692
-/
@[simp]
theorem finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]

/--
@isnad1 id=eq.0h2v.s7.f532b0678ff8 from=seed src=0 shape=bd6e3ac2 vocab=70270c39
-/
@[simp]
theorem finSuccEquivLast_symm_some (i : Fin n) :
    finSuccEquivLast.symm (some i) = Fin.castSucc i :=
  finSuccEquiv'_symm_some_below i.2

/--
@isnad1 id=eq.0h1v.s7.f5d253d10fe7 from=seed src=0 shape=d6bb73ff vocab=a2247806
-/
@[simp] theorem finSuccEquivLast_symm_none : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _

/-- An embedding `e : Fin (n+1) ↪ ι` corresponds to an embedding `f : Fin n ↪ ι` (corresponding
the last `n` coordinates of `e`) together with a value not taken by `f` (corresponding to `e 0`). -/
def Equiv.embeddingFinSucc (n : ℕ) (ι : Type*) :
    (Fin (n + 1) ↪ ι) ≃ (Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :=
  ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

/--
@isnad1 id=eq.0h3v.s8.8afd24a6d034 from=seed src=0 shape=8379706b vocab=03749cc5
-/
@[simp] lemma Equiv.embeddingFinSucc_fst {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).1 : Fin n → ι) = e ∘ Fin.succ := rfl

/--
@isnad1 id=eq.0h3v.s9.5ac7bd5ebffe from=seed src=0 shape=9f0ffbb4 vocab=dce894e5
-/
@[simp] lemma Equiv.embeddingFinSucc_snd {n : ℕ} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0 := rfl

/--
@isnad1 id=eq.0h3v.s9.2645ecbaf98d from=seed src=0 shape=094ce13d vocab=2510d094
-/
@[simp] lemma Equiv.coe_embeddingFinSucc_symm {n : ℕ} {ι : Type*}
    (f : Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :
    ((Equiv.embeddingFinSucc n ι).symm f : Fin (n + 1) → ι) = Fin.cons f.2.1 f.1 := by
  ext i
  exact Fin.cases rfl (fun j ↦ rfl) i

/-- Equivalence between `Fin m ⊕ Fin n` and `Fin (m + n)` -/
def finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

/--
@isnad1 id=eq.0h3v.s6.2fc8c632a146 from=seed src=0 shape=526a544c vocab=96a4bb85
-/
@[simp]
theorem finSumFinEquiv_apply_left (i : Fin m) :
    (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.e19e94777642 from=seed src=0 shape=049043cf vocab=a72e7ab0
-/
@[simp]
theorem finSumFinEquiv_apply_right (i : Fin n) :
    (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.e57ce94ed84f from=seed src=0 shape=cb2c863f vocab=86f7ea34
-/
@[simp]
theorem finSumFinEquiv_symm_apply_castAdd (x : Fin m) :
    finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

/--
@isnad1 id=eq.0h2v.s7.75b0806b7f33 from=seed src=0 shape=e54db16d vocab=bdc5cf32
-/
@[simp]
theorem finSumFinEquiv_symm_apply_castSucc (x : Fin m) :
    finSumFinEquiv.symm (Fin.castSucc x) = Sum.inl x :=
  finSumFinEquiv_symm_apply_castAdd x

/--
@isnad1 id=eq.0h3v.s7.5259ad098004 from=seed src=0 shape=aa615d1d vocab=c7f6a736
-/
@[simp]
theorem finSumFinEquiv_symm_apply_natAdd (x : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

/--
@isnad1 id=eq.0h1v.s7.4daee7b3eaad from=seed src=0 shape=2666c792 vocab=47de2930
-/
@[simp]
theorem finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  finSumFinEquiv_symm_apply_natAdd 0

/-- Equivalence between `Fin n ⊕ ℕ` and `ℕ` that sends `inl (a : Fin n)` to
`(a : ℕ)` and `inr a` to `n + a`. -/
def finSumNatEquiv (n : ℕ) : Fin n ⊕ ℕ ≃ ℕ where
  toFun := Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dite_eq_left (Fin.is_lt _))
    (fun _ => (dite_eq_right (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
  right_inv i := (apply_dite _ _ _ _).trans <| (i.lt_or_ge n).by_cases
    (fun hi => dite_eq_left hi)
    (fun hi => (dite_eq_right hi.not_gt).trans <| Nat.add_sub_cancel' hi)

/--
@isnad1 id=eq.0h2v.s5.1e1b63942ce5 from=seed src=0 shape=45bc8651 vocab=ab39b415
-/
@[simp] theorem finSumNatEquiv_apply_left (i : Fin n) :
    finSumNatEquiv n (.inl i) = i := rfl

/--
@isnad1 id=eq.0h2v.s5.317d77874f72 from=seed src=0 shape=a377be38 vocab=ea8ee71f
-/
@[simp] theorem finSumNatEquiv_apply_right (i : ℕ) :
    finSumNatEquiv n (.inr i) = n + i := rfl

/--
@isnad1 id=eq.1h2v.s6.4e26d8d8bbf8 from=seed src=0 shape=b6967ed3 vocab=d7d1b557
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_lt {i : ℕ} (hi : i < n) :
    (finSumNatEquiv n).symm i = .inl ⟨i, hi⟩ := dite_eq_left hi

/--
@isnad1 id=eq.1h2v.s6.4ee85961d5ee from=seed src=0 shape=d051e540 vocab=200ffbb1
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_ge {i : ℕ} (hi : n ≤ i) :
    (finSumNatEquiv n).symm i = .inr (i - n) := dite_eq_right (Nat.not_lt_of_ge hi)

/--
@isnad1 id=eq.0h2v.s5.126095e448d4 from=seed src=0 shape=c0de8e0d vocab=1dd3228b
-/
theorem finSumNatEquiv_symm_apply_fin (i : Fin n) :
    (finSumNatEquiv n).symm i = .inl i := by simp

/--
@isnad1 id=eq.0h2v.s5.0561b499f50a from=seed src=0 shape=47e4984e vocab=fde61726
-/
theorem finSumNatEquiv_symm_apply_add_left (i : ℕ) :
    (finSumNatEquiv n).symm (i + n) = .inr i := by simp

/--
@isnad1 id=eq.0h2v.s5.b4720917557b from=seed src=0 shape=e432288c vocab=fde61726
-/
theorem finSumNatEquiv_symm_apply_add_right (i : ℕ) :
    (finSumNatEquiv n).symm (n + i) = .inr i := by simp

/--
@isnad1 id=eq.0h2v.s5.a3ad7f36f03f from=seed src=0 shape=844df733 vocab=f9dc237e
-/
@[simp] theorem isLeft_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isLeft = decide (i < n) := by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]

/--
@isnad1 id=eq.0h2v.s5.665e296e8d47 from=seed src=0 shape=2fba2ffa vocab=5ed4c7bd
-/
@[simp] theorem isRight_finSumNatEquiv_symm_apply (i : ℕ) :
    ((finSumNatEquiv n).symm i).isRight = decide (n ≤ i) := by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl

/-- The equivalence between `Fin (m + n)` and `Fin (n + m)` which rotates by `n`. -/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

/--
@isnad1 id=eq.0h3v.s7.06b2c4f7497f from=seed src=0 shape=1a753b7f vocab=24b90f2d
-/
@[simp]
theorem finAddFlip_apply_castAdd (k : Fin m) (n : ℕ) :
    finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by simp [finAddFlip]

/--
@isnad1 id=eq.0h3v.s7.dfb774d39198 from=seed src=0 shape=455f634b vocab=24b90f2d
-/
@[simp]
theorem finAddFlip_apply_natAdd (k : Fin n) (m : ℕ) :
    finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by simp [finAddFlip]

/--
@isnad1 id=eq.1h5v.s7.81f532680895 from=seed src=0 shape=78de8def vocab=f02125df
-/
@[simp]
theorem finAddFlip_apply_mk_left {k : ℕ} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
    (hnk : n + k < n + m := Nat.add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert! finAddFlip_apply_castAdd ⟨k, h⟩ n

/--
@isnad1 id=eq.2h3v.s7.c8d232cc5b4a from=seed src=0 shape=aadc2cd1 vocab=ee0acc9f
-/
@[simp]
theorem finAddFlip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by lia⟩ := by
  convert! @finAddFlip_apply_natAdd n ⟨k - m, by lia⟩ m
  simp [Nat.add_sub_cancel' h₁]

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)` -/
@[simps]
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ ≤ x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
        _ = (x.1.1 + 1) * n := Eq.symm <| Nat.succ_mul _ _
        _ ≤ m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
    have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 <| H ▸ y.2
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1)
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2)
  right_inv _ := Fin.eq_of_val_eq <| Nat.mod_add_div _ _

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement. -/
@[simps]
def Nat.divModEquiv (n : ℕ) [NeZero n] : ℕ ≃ ℕ × Fin n where
  toFun a := (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ n.pos_of_neZero, Nat.div_eq_of_lt p.2.is_lt,
      Nat.zero_add]

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement. -/
@[simps]
def Int.divModEquiv (n : ℕ) [NeZero n] : ℤ ≃ ℤ × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_mul_add_emod]
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Prod.mk_inj, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [Int.add_comm, add_mul_ediv_right _ _ (natCast_eq_zero.not.2 (NeZero.ne n)),
      ediv_eq_zero_of_lt h1 h2, natMod, add_mul_emod_self_right, emod_eq_of_lt h1 h2, toNat_natCast]
    exact ⟨q.zero_add, Fin.val_cast_of_lt hrn⟩

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained.

This is the `Equiv` version of `Fin.castLE`. -/
@[simps apply symm_apply]
def Fin.castLEquiv {n m : ℕ} (h : n ≤ m) : Fin n ≃ { i : Fin m // (i : ℕ) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The natural `Equiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α` -/
@[simps]
def Fin.appendEquiv {α : Type*} (m n : ℕ) :
    (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) where
  toFun fg := Fin.append fg.1 fg.2
  invFun f := ⟨fun i ↦ f (Fin.castAdd n i), fun i ↦ f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

/-- `Fin (n + 1) → α` and `(Fin n → α) × α` are equivalent. -/
@[simps!]
def Fin.succFunEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α :=
  (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ ↦ Equiv.funUnique (Fin 1) α)
