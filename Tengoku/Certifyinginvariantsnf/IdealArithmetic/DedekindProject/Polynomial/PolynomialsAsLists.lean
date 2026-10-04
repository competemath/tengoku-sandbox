import Tengoku

/-! # Polynomials as Lists

In this file we define arithmetic operations on lists which correspond to polynomial arithemtic.
We also define computable polynomials as lists with no trailing zeros and show that they are isomorphic
to Mathlib polynomials.

## Main definitions:
- `Polynomial.ofList` : turns a list of coefficients into the corresponding polynomial.
- `computablePolynomialRingEquiv` : the ring isomorphism between computable polynomials and Mathlib
polynomials -/

open Polynomial BigOperators

variable {R : Type*}

def Finsupp.ofList {R : Type*} [DecidableEq R] [Zero R] (xs : List R) : ℕ →₀ R where
  toFun := (fun i => xs.getD i 0)
  support := (Finset.range xs.length).filter (fun i => xs.getD i 0 ≠ 0)
  mem_support_toFun a := by
    simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    apply List.getD_eq_default

/-- Pointwise addition of lists. -/
def List.addPointwise [AddMonoid R]: List R → List R → List R
  | as, [] => as
  | [], bs => bs
  | (a :: as), (b :: bs) => (a + b) :: as.addPointwise bs

def List.neg [AddGroup R] : List R → List R :=
  fun l => List.map (fun a => - a) l

def List.mulPointwise [Monoid R](c : R) : List R → List R :=
  fun l => l.map (fun a => c * a)

def List.mulAddPointwise [Semiring R] (c d : R) : List R → List R → List R :=
  fun l₁ l₂ => List.addPointwise (l₁.mulPointwise c) (l₂.mulPointwise d)

/-- Removes the trailing zeros of a list. -/
def List.dropTrailingZeros [Zero R] [DecidableEq R] : List R → List R
  | [] => []
  | x :: xs => if x ≠ 0 ∨ xs.any (fun x => x ≠ 0) then x :: xs.dropTrailingZeros else []

@[simp] lemma List.dropTrailingZeros_nil [Zero R]  [DecidableEq R]:
    List.dropTrailingZeros (R := R) [] = [] := rfl

@[simp] lemma List.dropTrailingZeros_eq_empty [Zero R]  [DecidableEq R](xs : List R)
  (hxs : xs.all fun x => x = 0) :
    List.dropTrailingZeros (R := R) (0 :: xs) = [] := ite_eq_right (by aesop)

/-- Convolution of lists, which corresponds to polynomial multiplication. -/
def List.convolve [Semiring R]: List R → List R → List R
  | [], _ => []
  | _, [] => []
  | (a :: as), bs => List.mulAddPointwise a 1 bs (0 :: as.convolve bs)
-- (a + X * as) * bs = a * bs + X * (as * bs)

/-- A more efficient version of dropTrailingZeros in case the last entry is nonzero. -/
def List.dropTrailingZeros' [Zero R][DecidableEq R] : List R → List R
  | [] => []
  | (a :: as) => if List.getLast _ (List.cons_ne_nil a as) ≠ 0 then (a :: as)
    else (a :: as).dropTrailingZeros

------------------------------------------------

@[simp]
lemma addPointwise_nil_left [AddMonoid R] (l : List R) : List.addPointwise [] l = l := by
  induction l
  rfl ; rfl

@[simp]
lemma addPointwise_nil_right [AddMonoid R] (l : List R) : List.addPointwise l [] = l := by
  induction l
  rfl ; rfl

@[simp]
lemma addPointwise_cons [AddMonoid R] (x y : R) (l l' : List R) :
    List.addPointwise (x :: l) (y :: l') = (x + y) :: (List.addPointwise l l') := by
  rfl

lemma List.dropTrailingZeros_of_zero [Zero R] [DecidableEq R]
    (l : List R) (h : ∀ x ∈ l, x = 0) : l.dropTrailingZeros = [] := by
  match l with
  | [] => rfl
  | (a :: as) =>
    by_cases h2 : ¬ a = 0 ∨ ∃ x ∈ as, ¬x = 0
    · simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, ite_eq_right_iff, reduceCtorEq, imp_false, not_or,
      Decidable.not_not, not_exists, not_and]
      simp only [mem_cons, forall_eq_or_imp] at h
      simpa using h
    · simp only [dropTrailingZeros, ne_eq, decide_not, any_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, h2, ↓reduceIte]

lemma List.dropTrailingZeros_ne_zero_of_ne_zero [Zero R] [DecidableEq R]
    (l : List R) (h : ∃ x ∈ l, x ≠ 0) : ∃ x ∈ l.dropTrailingZeros, x ≠ 0 := by
  induction l with
  | nil => simp only [not_mem_nil, ne_eq, false_and, exists_const] at h
  | cons a as ha =>
    simp only [mem_cons, ne_eq, exists_eq_or_imp] at h
    simp [dropTrailingZeros, h]
    rcases h with h1 | h2
    · exact Or.inl h1
    · exact not_or_of_imp fun _ => ha h2

lemma dropTrailingZeros_iter [Zero R] (l : List R) [DecidableEq R] :
    l.dropTrailingZeros =  (l.dropTrailingZeros).dropTrailingZeros := by
  induction l with
  | nil => simp only [List.dropTrailingZeros]
  | cons a as ha =>
    by_cases h : (a ≠ 0 ∨ as.any (fun x => x ≠ 0))
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at  h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.dropTrailingZeros]
      rcases h with h1 | h2
      · simp only [h1, not_false_eq_true, true_or, ↓reduceIte, List.cons.injEq, true_and]
        exact ha
      · simp only [List.dropTrailingZeros_ne_zero_of_ne_zero as h2, or_true, ↓reduceIte,
        List.cons.injEq, true_and]
        exact ha
    · simp only [ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.dropTrailingZeros]

lemma dropTrailingZeros_length [Zero R] [DecidableEq R] (l : List R) :
    (l.dropTrailingZeros).length ≤ l.length := by
  induction l with
  | nil => simp only [List.dropTrailingZeros, List.length_nil, le_refl]
  | cons a as ha =>
    by_cases h : ¬a = 0 ∨ ∃ x ∈ as, ¬x = 0
    · simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, h, ↓reduceIte, List.length_cons]
      exact Nat.pred_le_iff.mp ha
    · simp only [List.dropTrailingZeros, ne_eq, decide_not, List.any_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, h, ↓reduceIte, List.length_nil, List.length_cons, zero_le]

-------------------------------------------------------------------------------

/- For lists, we define an addition, multiplication and other operations.  -/

instance [AddMonoid R] : Add (List R) where
  add := λ l₁ l₂ => l₁.addPointwise l₂

instance [AddGroup R] : Neg (List R) where
  neg := List.neg

instance [AddGroup R] : Sub (List R) where
  sub := λ l₁ l₂ => l₁.addPointwise (l₂.neg)

instance [Semiring R] : Mul (List R) where
  mul := λ l₁ l₂ => l₁.convolve l₂

instance [One R] : One (List R) where
  one := [1]

instance : Zero (List R) where
  zero := []

lemma zero_def : (0 : List R) = [] := rfl

instance [Semiring R] : NatPow (List R)  where
  pow := λ l => λ n => npowRec n l

instance [Semiring R] : NatCast (List  R) where
  natCast := λ n => [(n : R)]

instance [Semiring R] : AddZeroClass (List R) where
  zero_add := addPointwise_nil_left
  add_zero := addPointwise_nil_right

instance [Semiring R] : MulZeroClass (List R) where
  zero_mul := by
    intro a
    induction a ; repeat rfl
  mul_zero := by
    intro a
    induction a ; repeat rfl

lemma List.zero_def [Zero R] : (0 : List R) = [] := rfl

lemma List.one_def [One R] : (1 : List R) = [1] := rfl

lemma List.add_def [AddMonoid R] (l₁ l₂ : List R) : l₁ + l₂ = l₁.addPointwise l₂ := rfl

lemma List.mul_def [Semiring R] (l₁ l₂ : List R) : l₁ * l₂ = l₁.convolve l₂ := rfl

lemma List.pow_def [Semiring R] (l : List R) (n : ℕ): l ^ n = npowRec n l := rfl

lemma List.neg_def [AddGroup R] (l : List R) : - l  = l.neg := rfl

@[simp]
lemma List.mul_nil [Semiring R] (l : List R) : l * [] = [] := by
  induction l
  · rfl
  · rfl

@[simp]
lemma List.nil_mul [Semiring R] (l : List R) : [] * l = [] := by
  induction l
  · rfl
  · rfl

@[simp]
lemma List.nil_add [AddMonoid R] (l : List R) : [] + l = l := by
  induction l
  · rfl
  · rfl

@[simp]
lemma List.add_nil [AddMonoid R] (l : List R) : l + [] = l := by
  induction l
  · rfl
  · rfl

lemma List.neg_eq_neg_one_mul [Ring R] (l : List R) : l.neg = [- 1] * l := by
  match l with
  | [] => rfl
  | (a :: as) =>
    simp only [neg, map_cons]
    congr
    · simp only [neg_mul, one_mul, mul_zero, add_zero]
    · simp only [neg_mul, one_mul, convolve, map_nil, addPointwise]

lemma List.add_length [AddMonoid R] (l₁ l₂ : List R) :
    (l₁ + l₂).length = max l₁.length l₂.length := by
  have : ∀ (l : List R), (l₁ + l).length = max l₁.length l.length := by
    induction l₁ with
    | nil =>
      intro l
      rw [List.nil_add]
      simp only [length_nil, zero_le, max_eq_right]
    | cons a as hi =>
      intro l
      match l with
      | [] =>
      · rw [List.add_nil]
        simp only [length_cons, length_nil, zero_le, max_eq_left]
      | (b :: bs) =>
      · have : a :: as + b :: bs = (a + b) :: (as + bs) := by rfl
        rw [this, length_cons, hi bs, length_cons, length_cons]
        exact (Nat.succ_max_succ (length as) (length bs)).symm
  exact this l₂

lemma List.mulPointwise_length [Semiring R] (l : List R) (a : R) :
    (List.mulPointwise a l).length = l.length := by
  unfold mulPointwise
  simp only [length_map]

lemma List.mul_eq_mulPointwise [Semiring R] (l : List R) (a : R) :
    [a] * l = List.mulPointwise a l :=
  match l with
  | [] => rfl
  | (b :: bs) => by
    rw [(show [a] * (b :: bs) = [a].convolve (b :: bs) by rfl)]
    simp only [convolve, mulAddPointwise, addPointwise, add_zero, one_mul, map_nil,
      mulPointwise, map_cons]

/- Lemmas relating operations on functions `Fin n → R` and lists. -/

lemma List.add_length_ofFn [AddMonoid R] (a b : Fin n →  R):
    List.length ((List.ofFn a) + (List.ofFn b)) = n := by
  simp only [List.add_length, length_ofFn, max_self]

lemma List.add_ofFn [AddMonoid R] (a b : Fin n →  R) :
    (List.ofFn a) + (List.ofFn b) = List.ofFn (a + b) := by
  induction n with
  | zero =>
    simp only [ofFn_zero, Matrix.empty_add_empty]
    rfl
  | succ n hn =>
    rw [List.ofFn_succ, List.ofFn_succ , ofFn_succ, Pi.add_apply]
    erw [← hn (fun i => a (Fin.succ i)) (fun i => b (Fin.succ i))]
    rfl

variable [Semiring R]

lemma List.mulPointwise_ofFn (a : Fin n → R) (c : R) :
    List.mulPointwise c (List.ofFn a) = List.ofFn (c • a) := by
  match n with
  | 0 =>
    simp only [ofFn_zero, Matrix.smul_empty]
    rfl
  | Nat.succ n =>
    rw [List.ofFn_succ]
    unfold mulPointwise
    simp only [map_cons, map_ofFn, ofFn_succ, Pi.smul_apply, smul_eq_mul, cons.injEq, ofFn_inj,
      true_and]
    rfl

lemma List.sum_ofFn' {m n : ℕ} (hm : m ≠ 0) (f : Fin m → (Fin n → R)) :
    List.ofFn (∑ i, f i) = List.sum (List.ofFn (fun i => List.ofFn (f i))) := by
  induction m with
  | zero => contradiction
  | succ m hmm =>
    cases m
    case zero =>
      simp [zero_def, add_nil]
    case succ m =>
      unfold List.sum
      have := hmm m.succ_ne_zero (fun i => f i.succ)
      rw [List.ofFn_succ, List.foldr_cons, Fin.sum_univ_succ, ← add_ofFn, this]
      rfl

/- Properties of `ofList` -/

omit [Semiring R] in
lemma List.zero_eq : (0 : List R) = [] := rfl

variable [DecidableEq R]

/-- Sends a polynomial to a list of its coefficients. The zero polynomial is sent to [].  -/
def Polynomial.toList [DecidableEq R] (p : Polynomial R) : List R :=
  (List.ofFn (λ (i : Fin (p.natDegree + 1)) => p.coeff i : Fin (p.natDegree + 1) → R)).dropTrailingZeros

-----------------------

lemma List.dvd_foldl_gcd {R : Type u} [CommSemiring R] [IsDomain R]
    [DecidableEq R] [GCDMonoid R] (x : R) (l : List R) (hdvd : ∀ a, a ∈ l → x ∣ a) :
    x ∣ List.foldr gcd 0 l := by
  induction l with
  | nil => simp only [foldr_nil, dvd_zero]
  | cons b bs hb =>
    simp only [mem_cons, forall_eq_or_imp] at hdvd
    rw [foldr_cons]
    exact (dvd_gcd_iff _ _ _ ).2 ⟨hdvd.1, (hb hdvd.2)⟩

/- If the last entry of `l` is 1, then `ofList l` is monic. -/

/-- Given a list of length `n`, this is the function `Fin n → R`
  that sends `i` to the `i`-th entry of the list. -/
def FnOfList {α : Type*} (n : ℕ) (l : List α) (hl : l.length = n) : Fin n → α :=
  fun (i : Fin n) => (l.get (Fin.cast hl.symm i))

lemma listOfFn_of_FnOfList
  {α : Type*}(n : ℕ)(l : List α)(hl : l.length = n) : List.ofFn (FnOfList n l hl) = l := by
  unfold FnOfList
  rw [← List.ofFn_congr hl _, List.ofFn_get]

lemma FnOfList_of_OfFn {α : Type*} (n : ℕ) (a : Fin n → α) :
    FnOfList n (List.ofFn a) (List.length_ofFn) = a := by
  unfold FnOfList
  simp only [List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self]

------------

/- # EXTRA OPERATIONS ON LISTS -/

/-- Adds `n - 1` zeros between entries of a list. In characteristic `n`, this corresponds to
  computing the `n`-th power of a list. -/
def List.expand {α : Type*} [DecidableEq α] [Zero α] (n : ℕ)  : List α → List α
  | [] => []
  | (a :: as) => if as = [] then [a] else [a] ++  (List.replicate (n - 1) (0 : α)) ++ expand n as

/-- Given `l`, computes the list corresponding to the derivative of the polynomial defined by `l`. -/
def List.derivative [Semiring R] : List R → List R
  | [] => []
  | (_ :: as) => as + (0 :: derivative as)

def List.eval [Semiring R] (x : R) : List R → R
  | [] => 0
  | (a :: as) => a + (eval x as) * x

----------------------------------------------------------------------

section ComputablePolynomialsSemiring

/-- A computable polynomial is a list without no trailing zeros
  (i.e. equal to itself after removing trailing zeros). -/
@[reducible]
def ComputablePolynomial (R : Type*) [Semiring R] [DecidableEq R]:=
  {p : List R // p = p.dropTrailingZeros }

variable  {R : Type*} [Semiring R][DecidableEq R]

instance [AddMonoid R] : Add (ComputablePolynomial R) where
  add := λ p q =>
   ⟨(p.1 + q.1).dropTrailingZeros , dropTrailingZeros_iter (p.1 + q.1)⟩

instance [Semiring R] : Mul (ComputablePolynomial R) where
  mul := λ p q =>
   ⟨(p.1 * q.1).dropTrailingZeros , dropTrailingZeros_iter _ ⟩

instance [Semiring R] : Zero (ComputablePolynomial R) where
  zero := ⟨(0 : List R), rfl⟩

instance [Semiring R] : One (ComputablePolynomial R) where
  one := ⟨ (1 : List R).dropTrailingZeros , by exact dropTrailingZeros_iter 1 ⟩

instance [Semiring R] : Pow (ComputablePolynomial R) ℕ where
  pow := λ p => λ n => ⟨(p.1 ^ n).dropTrailingZeros,  dropTrailingZeros_iter _ ⟩

instance [Semiring R] : NatCast (ComputablePolynomial R) where
  natCast := λ n => ⟨[(n : R)].dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance [Semiring R] : SMul ℕ (ComputablePolynomial R) where
  smul := λ n => λ p => (↑n * p)

/-- Sends a polynomial to the corresponding computable polynomial. -/
def toComputablePolynomial (p : R[X]) : ComputablePolynomial R :=
  ⟨toList p, dropTrailingZeros_iter _ ⟩

end ComputablePolynomialsSemiring

variable {R : Type*} [DecidableEq R] [Ring R]

instance : Neg (ComputablePolynomial R) where
  neg := fun p => ⟨(p.1).neg.dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance : Sub (ComputablePolynomial R) where
  sub := fun p q => p + (- q)

instance : IntCast (ComputablePolynomial R) where
  intCast := fun z => ⟨[↑z].dropTrailingZeros, dropTrailingZeros_iter _ ⟩

instance : SMul ℤ (ComputablePolynomial R) where
  smul := fun z => fun p => z * p

/- Ring isomorphism between polynomials and computable polynomials. -/
