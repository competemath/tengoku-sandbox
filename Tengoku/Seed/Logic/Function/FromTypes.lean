/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Tengoku.Seed.Data.Fin.VecNotation

/-! # Function types of a given heterogeneous arity

This provides `Function.FromTypes`, such that `FromTypes ![α, β] τ = α → β → τ`.
Note that it is often preferable to use `((i : Fin n) → p i) → τ` in place of `FromTypes p τ`.

## Main definitions

* `Function.FromTypes p τ`: `n`-ary function `p 0 → p 1 → ... → p (n - 1) → β`.
-/

@[expose] public section

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The type of `n`-ary functions `p 0 → p 1 → ... → p (n - 1) → τ`. -/
def FromTypes : {n : ℕ} → (Fin n → Type u) → Type u → Type u
  | 0    , _, τ => τ
  | n + 1, p, τ => vecHead p → @FromTypes n (vecTail p) τ

/--
@isnad1 id=eq.0h2v.s4.6ff1c1252965 from=seed src=0 shape=150f8c3f vocab=ae903312
-/
theorem fromTypes_zero (p : Fin 0 → Type u) (τ : Type u) : FromTypes p τ = τ := rfl

/--
@isnad1 id=eq.0h1v.s3.083c7072d690 from=seed src=0 shape=b53b7d92 vocab=ed245705
-/
theorem fromTypes_nil (τ : Type u) : FromTypes ![] τ = τ := fromTypes_zero ![] τ

-- prefer `fromTypes_cons` when it (syntactically) applies
/--
@isnad1 id=eq.0h3v.s5.5c07db999165 from=seed src=0 shape=f39c5587 vocab=b1486909
-/
theorem fromTypes_succ {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ = (vecHead p → FromTypes (vecTail p) τ) := rfl

/--
@isnad1 id=eq.0h4v.s4.fa9224cdc8f7 from=seed src=0 shape=75ed4ccd vocab=d70e8c7b
-/
theorem fromTypes_cons {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ = (α → FromTypes p τ) := fromTypes_succ _ τ

/-- The definitional equality between `0`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
def fromTypes_zero_equiv (p : Fin 0 → Type u) (τ : Type u) :
    FromTypes p τ ≃ τ := Equiv.refl _

/-- The definitional equality between `![]`-ary heterogeneous functions into `τ` and `τ`. -/
@[simps!]
def fromTypes_nil_equiv (τ : Type u) : FromTypes ![] τ ≃ τ :=
  fromTypes_zero_equiv ![] τ

/-- The definitional equality between `p`-ary heterogeneous functions into `τ`
  and function from `vecHead p` to `(vecTail p)`-ary heterogeneous functions into `τ`. -/
@[simps!]
def fromTypes_succ_equiv {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    FromTypes p τ ≃ (vecHead p → FromTypes (vecTail p) τ) := Equiv.refl _

/-- The definitional equality between `(vecCons α p)`-ary heterogeneous functions into `τ`
  and function from `α` to `p`-ary heterogeneous functions into `τ`. -/
@[simps!]
def fromTypes_cons_equiv {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    FromTypes (vecCons α p) τ ≃ (α → FromTypes p τ) := fromTypes_succ_equiv _ _

namespace FromTypes

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Constant `n`-ary function with value `t`. -/
def const : {n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → (t : τ) → FromTypes p τ
  | 0,     _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

/--
@isnad1 id=eq.0h3v.s5.c50f568ad788 from=seed src=0 shape=8d8afe96 vocab=6aa590f3
-/
@[simp]
theorem const_zero (p : Fin 0 → Type u) {τ : Type u} (t : τ) : const p t = t :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.539f1e28ecfd from=seed src=0 shape=fe2a9e5c vocab=c239ce8a
-/
@[simp]
theorem const_succ {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ) :
    const p t = fun _ => const (vecTail p) t := rfl

/--
@isnad1 id=eq.0h5v.s6.b6e649b12be7 from=seed src=0 shape=adf34763 vocab=d37f5150
-/
theorem const_succ_apply {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ)
    (x : p 0) : const p t x = const (vecTail p) t := rfl

instance inhabited {n} {p : Fin n → Type u} {τ} [Inhabited τ] :
    Inhabited (FromTypes p τ) := ⟨const p default⟩

end FromTypes

end Function
