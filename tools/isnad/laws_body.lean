-- The laws of the isnad recipe, checked on real elaborated statements (scripts/isnad.py laws). Core Lean only: no Mathlib, no tree.
universe u v
set_option linter.unusedVariables false

theorem l_add (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem l_add2 (x y : Nat) : x + y = y + x := by omega
namespace Ns
theorem l_add3 (m n : Nat) : m + n = n + m := by simp [Nat.add_comm]
end Ns
theorem l_mul (a b : Nat) : a * b = b * a := Nat.mul_comm a b
theorem l_refl_u (α : Type u) (a : α) : a = a := rfl
theorem l_refl_v (β : Type v) (b : β) : b = b := Eq.refl b
theorem l_hyp (a b : Nat) (h : a ≤ b) : a < b + 1 := Nat.lt_succ_of_le h
theorem l_hyp2 (c d : Nat) (hh : c ≤ d) : c < d + 1 := by omega
theorem l_and (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
theorem l_and2 (r s : Prop) (h1 : r) (h2 : s) : r ∧ s := And.intro h1 h2
theorem l_all (p : Nat → Prop) (h : ∀ n, p n) : p 0 := h 0
theorem l_all2 (q : Nat → Prop) (k : ∀ m, q m) : q 0 := k 0
theorem l_swapped (a b : Nat) : b + a = a + b := Nat.add_comm b a
theorem l_i1 (α : Type) (i j : Add α) (a b : α) : @Add.add α i a b = @Add.add α i a b := rfl
theorem l_i2 (α : Type) (i j : Add α) (a b : α) : @Add.add α j a b = @Add.add α j a b := rfl
-- the first lab form wrote `Π(<type>.<body>)` with unquoted names: `A → B.C` and `A.B → C` were both `Π(A.B.C)`. Two constants whose dotted names run together
def IsnadP : Type := Unit
def IsnadQ.IsnadR : Type := Unit
def IsnadP.IsnadQ : Type := Unit
def IsnadR : Type := Unit
theorem l_amb1 : Nonempty (IsnadP → IsnadQ.IsnadR) := ⟨fun _ => ()⟩
theorem l_amb2 : Nonempty (IsnadP.IsnadQ → IsnadR) := ⟨fun _ => ()⟩
private def secretProp : Prop := True
theorem l_priv : secretProp := trivial

open Lean Elab Command in
elab "#isnad_laws" : command => do
  let env ← getEnv
  let rec' (n : Name) : CommandElabM (List String) := do
    let some ci := env.find? n | throwError "isnad laws: unknown theorem {n}"
    return Isnad.fields env n "<laws>" ci.type
  -- fields: 0 name 1 module 2 kind 3 hyps 4 vars 5 nodes 6 canonical 7 shape 8 vocabulary
  let same (field : Nat) (ns : List Name) : CommandElabM Bool := do
    let fs ← ns.mapM fun n => do return (← rec' n)[field]!
    return fs.eraseDups.length == 1
  let mut checks : Array (Bool × String) := #[]
  -- the identity ignores binder names, theorem names and namespaces, universe parameter names, and proofs
  checks := checks.push ((← same 6 [`l_add, `l_add2, `Ns.l_add3, `Nat.add_comm]), "binder names, theorem names, namespaces and proofs do not enter the canonical form")
  checks := checks.push ((← same 6 [`l_refl_u, `l_refl_v]), "universe parameter names do not enter the canonical form")
  checks := checks.push ((← same 6 [`l_hyp, `l_hyp2]), "hypothesis names do not enter the canonical form")
  checks := checks.push ((← same 6 [`l_and, `l_and2]), "propositional variable names do not enter the canonical form")
  checks := checks.push ((← same 6 [`l_all, `l_all2]), "a predicate variable's name does not enter the canonical form")
  -- different statements are different
  checks := checks.push ((!(← same 6 [`l_add, `l_mul])), "a different operation changes the canonical form")
  checks := checks.push ((!(← same 6 [`l_add, `l_swapped])), "the order of the sides is part of the statement")
  checks := checks.push ((!(← same 6 [`l_hyp, `l_and])), "different statements differ")
  -- the canonical form is injective where names and separators could run together (regression: the first lab form made these two the same string)
  checks := checks.push ((!(← same 6 [`l_amb1, `l_amb2])), "dotted names that run together do not make two statements equal")
  -- shape: the same pattern over different objects; vocabulary: different objects
  checks := checks.push ((← same 7 [`l_add, `l_mul]), "a + b = b + a and a * b = b * a have the same shape")
  checks := checks.push ((!(← same 8 [`l_add, `l_mul])), "…and different vocabularies")
  -- instance arguments are dropped from the shape by the parameter they sit at, a bound instance variable included; the canonical form keeps them
  checks := checks.push ((← same 7 [`l_i1, `l_i2]), "a bound instance variable is dropped from the shape like any instance argument")
  checks := checks.push ((!(← same 6 [`l_i1, `l_i2])), "…but the canonical form tells the two instances apart")
  -- a private constant keeps its whole name: it cannot be mistaken for another module's private constant of the same short name
  checks := checks.push ((((← rec' `l_priv)[6]!.splitOn "_private.").length == 2), "a private constant keeps its `_private.<Module>.0.` prefix")
  -- the profile: kind, hypotheses, variables (the heuristic of the recipe: a binder whose type is a propositional variable counts as a variable)
  checks := checks.push (((((← rec' `l_hyp).drop 2).take 3) == ["lt", "1", "2"]), "l_hyp concludes lt with 1 hypothesis and 2 variables")
  checks := checks.push (((((← rec' `l_add).drop 2).take 3) == ["eq", "0", "2"]), "l_add concludes eq with 0 hypotheses and 2 variables")
  checks := checks.push (((((← rec' `l_and).drop 2).take 3) == ["and", "0", "4"]), "l_and: hp : p counts as a variable (v1 heuristic)")
  -- the canonical form is one line with no tab
  for n in [`l_add, `l_hyp, `l_and, `l_all] do
    let c := (← rec' n)[6]!
    checks := checks.push (!(c.contains '\t' || c.contains '\n'), s!"{n}: the canonical form has no tab or newline")
  let failures := (checks.filter (!·.1)).map (·.2)
  if failures.isEmpty then
    logInfo s!"isnad laws: {checks.size} checks passed"
  else
    throwError "isnad laws FAILED ({failures.size} of {checks.size}):\n{"\n".intercalate failures.toList}"

#isnad_laws
