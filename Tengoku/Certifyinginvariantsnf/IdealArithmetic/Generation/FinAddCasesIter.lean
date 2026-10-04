import Tengoku

/-!
# Concatenating tuples

API to concatenate tuples.

## Main definition
- `Fin.addCasesIter`: concatenates a family of tuples `g : ∀ i, Fin (e i) → α` into a
tuple `Fin (∑ i, e i) → α`
- `indexPairEquiv` : computable bijection between `Fin (∑ i, e i)`, the global index,
  and `Σ (i : Fin r), Fin (e i)`, the pairs of local indices.

## Main results
- `addCasesIter_apply` : describes the evaluation of `Fin.addCasesIter` in terms of the pair of
  local indices.  -/

/-- Form a tuple by concatenating a family of tuples `g` with arities given by `e`. -/
def Fin.addCasesIter {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α) :
    Fin (∑ i, e i) → α := by
  revert e
  induction r with
  | zero => exact fun e he =>  Fin.elim0
  | succ r hr =>
    intro e g
    exact (Fin.addCases ((hr (fun i => e i.castSucc) (fun i => g i.castSucc)) )
      (g (last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))

lemma List.ofFn_addCases {n m} {α} (left : Fin m → α) (right : Fin n → α) :
    List.ofFn (Fin.addCases left right) = List.ofFn left ++ List.ofFn right := by
  simp_rw [List.ofFn_add,  Fin.addCases_right]
  congr
  ext i
  exact Fin.addCases_left i

lemma List.addCases_comp {n m} {α} (f : Fin m → α)  (eq : n = m) :
    List.ofFn (f ∘ (Fin.cast eq))  = List.ofFn f := by
  refine ofFn_inj'.mpr ?_
  ext
  · exact eq
  · exact (Fin.heq_fun_iff eq).mpr (congrFun rfl)

lemma List.ofFn_addCasesIter {α : Type*} {r : ℕ} (e : Fin (r + 1) → ℕ) (g : ∀ i, Fin (e i) → α) :
    List.ofFn (Fin.addCasesIter e g) =
      List.ofFn (Fin.addCasesIter (fun i => e i.castSucc) (fun (i : Fin r) => g i.castSucc))
      ++ List.ofFn (g (Fin.last r)) := by
  match r with
  | 0 =>
    simp [Fin.addCasesIter, Fin.addCases]
    rfl
  | r =>
    unfold Fin.addCasesIter
    simp_rw [List.addCases_comp, List.ofFn_addCases]

/-- Send `j : Fin (∑ i, e i)` to `⟨k, t⟩`, where `k` and `t : Fin (e k)` are
such that `j = t + ∑ i<k, e i` . -/
def indexPair {r : ℕ} (e : Fin r → ℕ) (j : Fin (∑ i, e i)) : Σ (i : Fin r), Fin (e i) := by
  revert e
  induction r with
  | zero =>
    intro e j
    exact ⟨j, IsEmpty.elim (α := Fin 0) (p := fun (i : Fin 0) => Fin (e i)) (Fin.isEmpty') j⟩
  | succ r hr =>
    intro e j
    let e' : Fin r → ℕ := fun i => e i.castSucc
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · obtain ⟨i, hi⟩ := hr e' ⟨↑j, h⟩
      exact ⟨i.castSucc, hi⟩
    · let j' := Fin.subNat (∑ (i : Fin r), e i.castSucc) (Fin.cast (show ( ∑ i, e i =
        e (Fin.last r) + ∑ (i : Fin r), e i.castSucc ) by rw [Fin.sum_univ_castSucc, add_comm]) j)
      refine ⟨Fin.last r, ?_⟩
      refine j' ?_
      simp only [Fin.val_cast]
      omega

lemma indexPair_left_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)}
    (h : j < ∑ (i : Fin r), e i.castSucc) :
    indexPair e j = ⟨Fin.castSucc (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).1,
      (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).2 ⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte, Fin.val_cast]

lemma indexPair_right_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)}
    (h : ¬ j < ∑ (i : Fin r), e i.castSucc) :
    indexPair e j = ⟨Fin.last r, Fin.subNat (∑ (i : Fin r), e i.castSucc)
      (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc )
        by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.val_cast] ;  omega)⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte]

/-- The evaluation of `Fin.addCasesIter` in terms of the pair of local indices. -/
lemma addCasesIter_apply {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α)
    (j : Fin (∑ i, e i)) :
    Fin.addCasesIter e g j = g (indexPair e j).1 (indexPair e j).2 := by
  revert e
  induction r with
  | zero =>
    intro e g j
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at j
    exfalso
    exact Fin.isEmpty'.false j
  | succ r hr =>
    intro e g j
    let e' := (fun (i : Fin r) => e i.castSucc)
    let g' := (fun (i : Fin r) => g i.castSucc)
    let f :=  Fin.addCasesIter e' g'
    have : Fin.addCasesIter e g = (Fin.addCases f (g (Fin.last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))  := rfl
    rw [this, Function.comp_apply]
    let t := g (Fin.last r)
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) = (Fin.castAdd (e (Fin.last r)) (⟨j, h⟩ )) := by rfl
      rw [this, Fin.addCases_left]
      simp only [hr e' g' ⟨j, h⟩, f, e', g']
      rw [indexPair_left_aux]
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) =
        (Fin.natAdd (∑ (i : Fin r), e i.castSucc) (Fin.subNat (∑ (i : Fin r), e i.castSucc)
        (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc )
        by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.val_cast] ;  omega))) := by
        erw [Fin.natAdd_subNat_cast (i := Fin.cast (Fin.sum_univ_castSucc e) j )]
      rw [this, Fin.addCases_right, indexPair_right_aux h]

section

lemma forall_addCasesIter_prop {A B : Type*} {r : ℕ} {e : Fin r → ℕ}
    (g : ∀ (i : Fin r), Fin (e i) → A) (M : ∀ (i : Fin r), Fin (e i) → B)
    (P : A → B → Prop) (h : ∀ i, ∀ j , P (g i j) (M i j)) :
    ∀ k : Fin (∑ (i : Fin r), e i) , P ((Fin.addCasesIter e g) k) ((Fin.addCasesIter e M) k) := by
  intro k
  rw [addCasesIter_apply, addCasesIter_apply]
  refine h (indexPair e k).1 (indexPair e k).2

end
