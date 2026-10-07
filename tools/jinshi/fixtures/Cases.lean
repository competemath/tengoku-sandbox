/-
Jinshi fixtures: a module with planted faults, one per examination, compiled against Lean's own library (no tree, no cache),
so the self-test runs anywhere the toolchain does. tools/jinshi/fixtures/expected.tsv names what must be found; everything
else in this file must stay quiet. The "seed" of the self-test is `Init` (--seed Init): a name that Init declares is a seed name.
-/
namespace JinshiFixtures

-- shadow: a library-side `Nat.succ` and `List.length` (Init declares both); a theorem whose statement uses the library's
def Nat.succ (n : Nat) : Nat := n + 2
def List.length (_ : List α) : Nat := 0
theorem uses_shadowed (n : Nat) : JinshiFixtures.Nat.succ n = n + 2 := rfl

-- dossier: a theorem resting on a trivial predicate, on a predicate that ignores its argument, and on a fieldless structure
def RiemannHypothesis : Prop := True
def IsBig (_ : Nat) : Prop := 1 = 1
structure Witness where
theorem rh_holds : RiemannHypothesis := trivial
theorem everything_is_big (n : Nat) : IsBig n := rfl
theorem witness_exists : ∃ _w : Witness, True := ⟨⟨⟩, trivial⟩

-- dossier, quiet: an honest local definition
def IsEven (n : Nat) : Prop := n % 2 = 0
theorem two_even : IsEven 2 := rfl

-- content: conclusions that are a hypothesis, True, a = a, p ↔ p
theorem conclusion_is_hypothesis (p : Prop) (hp : p) : p := hp
theorem conclusion_true (n : Nat) : True := trivial
theorem refl_only (n : Nat) : n + 1 = n + 1 := rfl
theorem iff_self_only (p : Prop) : p ↔ p := Iff.rfl

-- arith: ℕ-subtraction and ℕ-division in statements (the real-like types live in the tree, not in Lean's own library)
theorem nat_sub_claim (a b : Nat) : a - b + b = a ∨ a < b := by omega
theorem nat_div_claim (n : Nat) : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2

-- tcb: unsafe, partial (an opaque with an unsafe implementation), opaque and implemented_by; a theorem whose statement mentions an opaque constant
unsafe def unsafeLength (l : List Nat) : Nat := l.length
partial def loopForever (n : Nat) : Nat := loopForever (n + 1)
opaque secret : Nat
def fastId (n : Nat) : Nat := n
@[implemented_by fastId] def slowId (n : Nat) : Nat := n
theorem about_secret : secret = secret := rfl

-- autoimplicit: `m` is never bound; with the tree's default options this compiles, quantified over `m`
theorem typo_quantified (n : Nat) : n + 0 = n ∨ n = m := Or.inl (Nat.add_zero n)

-- quiet: ordinary theorems
theorem add_zero' (n : Nat) : n + 0 = n := Nat.add_zero n
theorem le_succ' (n : Nat) : n ≤ n + 1 := Nat.le_succ n

end JinshiFixtures
