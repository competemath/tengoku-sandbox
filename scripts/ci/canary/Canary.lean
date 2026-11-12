import Tengoku.All

set_option Elab.async false
set_option linter.unusedVariables false

/-!
# Canary: `import Tengoku.All` must stay usable.

Everything below is ordinary Lean and Mathlib, written the way a person or a prover writes it. It must elaborate on the whole tree, whatever any library of the tree declares
globally. A failure here is a library that leaks into everybody else: a global instance or simp lemma (`positivity`, `linarith`, `omega`, `ring` fail), a global notation
(`-(3 * x)` is "Ambiguous term"), a reserved word (`fun v => …` is "unexpected token"). The gate that runs it: scripts/ci/canary/README.md.
-/

/-! ## notation: the same symbols as core and Mathlib -/

example (x : ℝ) : -(3 * x) = -3 * x := by ring
example (x y : ℝ) : -(x + y) = -x - y := by ring
example (f g : ℕ → ℕ) : (f ∘ g) 0 = f (g 0) := rfl
example (x : ℝ) (h : x ≠ 0) : x⁻¹ * x = 1 := inv_mul_cancel₀ h
example (G : Type) [Group G] (g : G) : g⁻¹ * g = 1 := inv_mul_cancel g
example : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)
example (s : Finset ℕ) (h : 3 ∈ s) : 3 ∈ insert 5 s := by simp [h]
example (x : ℝ) : x ∉ (∅ : Set ℝ) := by simp
example (l : List ℕ) (h : 2 ∈ l) : 2 ∈ 1 :: l := by simp [h]
example (l : List ℕ) (h : 0 < l.length) : l[0] = l[0] := rfl
example (a b : Type) (e : a ≃ b) : a ≃ b := e
example (s t : Finset ℕ) (h : s ⊆ t) : s ⊆ insert 1 t := by intro x hx; simp [h hx]
example (n : ℕ) : (↑n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

section category
open CategoryTheory
example {C : Type} [Category C] (X Y : C) (f : X ⟶ Y) : X ⟶ Y := f
example {C : Type} [Category C] (X : C) : X ≅ X := Iso.refl X
end category

/-! ## words: names a person gives to a variable or a hypothesis -/

example (a b c d e f g h i j k l m n o p q r s t u v w x y z : ℕ) : a + z = z + a := by omega
example (α β γ δ ε ζ η θ ι κ μ ν ξ ρ σ τ φ χ ψ ω : Type) : True := trivial
example (na ih hx hy hn hab hxy this hf hg hs ht hp hq : Prop) : True := trivial
example (eval sum prod card dim rank ker im re deg dom ran op comp inv exp log abs sq pow neg succ pred : ℕ) : True := trivial
example (wkn swkn Sg Pg Dlt memo table apply cases : ℕ) : True := trivial
example (diaDot KAx EFQAx Δ ω : ℕ) : True := trivial

/-! ## tactics: the first ones everybody reaches for -/

example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega
example (a b : ℤ) (h : a < b) : a + 1 ≤ b := by omega
example (x : ℝ) : 0 < x ^ 2 + 1 := by positivity
example (x y : ℝ) (h : x < y) : x < y + 1 := by linarith
example (x y : ℝ) : 0 ≤ (x - y) ^ 2 := by nlinarith [sq_nonneg (x - y)]
example (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
example (x : ℝ) (h : x ≠ 0) : x / x = 1 := by field_simp
example : (2 : ℝ) + 2 = 4 := by norm_num
example (l : List ℕ) : (l ++ []).length = l.length := by simp
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
example : (3 : ℕ) ∣ 12 := by decide
example (a : ℤ) (h : 0 < a) : a / a = 1 := by simp [Int.ediv_self h.ne']
example (n : ℕ) : n * 2 / 2 = n := by omega
example (n : ℕ) : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
example (x : ℝ) (h : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ x := h.1
example (a b : ℤ) (h : a ≤ b) : a < b + 1 := by linarith
example (a : ℤ) (h : 0 < a) : a ≠ 0 := h.ne'
example (a b : ℝ) : min a b ≤ max a b := le_trans (min_le_left a b) (le_max_left a b)
example : Continuous (fun x : ℝ => x ^ 2 + 1) := by fun_prop
example : Measurable (fun x : ℝ => x + 1) := by fun_prop
example : Fintype.card (Fin 5) = 5 := by simp
example (n : ℕ) (h : n < 3) : n * n < 9 := by interval_cases n <;> omega
example (p q : Prop) (h : p ∧ q) : q ∧ p := by obtain ⟨a, b⟩ := h; exact ⟨b, a⟩
example (x : ℝ) : |x| ≥ 0 := by positivity

/-! ## reserved words: the atoms of a library's `elab`/`macro`/`syntax` must not be tokens of the whole tree

equational-theories (a generated library) kept these global until its notation was scoped by the generator (scripts/scope_notation.py, tengoku#615/#618, 2026-10-18). -/

example (resolve : ℕ) : True := trivial
example (superpose : ℕ) : True := trivial
example (Facts : ℕ) : True := trivial
example (memoFinOp : ℕ) : True := trivial
example (finOpTable : ℕ) : True := trivial
example (mod_symm : ℕ) : True := trivial
