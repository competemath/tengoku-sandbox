-- jinshi: only nested
/-
Jinshi fixture for `nested` (docs/jinshi.md): a genuinely nested inductive (`Tree`, nesting itself inside `List`) against a
plain, direct-recursive one (`Peano`) that must stay quiet. Lean core only, no tree, no cache.
-/
namespace JinshiFixtures

inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : (children : List (Tree α)) → Tree α

inductive Peano where
  | zero : Peano
  | succ : (n : Peano) → Peano

end JinshiFixtures
