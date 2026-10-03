/-!
# Indexing a list without carrying a bounds proof

Three lemmas, all about reading a list positionally with `getD` -- the total
accessor that takes a fallback value instead of a proof that the index is in
range. `getD_mem` says a reading below the length really is a member of the
list, `getD_step_of_pairwise` says consecutive readings of a `Pairwise R` list
are related by `R`, and `range_pairwise_lt_lt` supplies the standard instance
where the list is `List.range n` and the relation is "increasing and below
`n`".

Using `getD` rather than the dependently typed accessor is the point of the
file. A tagged partition is a list of points that has to be indexed inside
arithmetic, and the bounds proof would otherwise travel through every
rewriting step in the argument. With `getD` the index is an ordinary `Nat`,
the bound appears only as a hypothesis of the lemma that needs it, and the
fallback value is never reached.

## Position in the development

Bottom of the dependency order, no imports. All four consumers are in the
Henstock--Kurzweil development --
`Tautology.RealIntegral.HenstockKurzweil.FiniteLevelGrouping`,
`Tautology.RealIntegral.HenstockKurzweil.Core.HenstockLemma.Basics`,
`Tautology.RealDerivative.Integral.HenstockKurzweil.ExceptionalSet` and
`.PrimitiveDifferentiation` -- where the ordering of tags along a partition is
exactly a `Pairwise` fact consumed one step at a time. The file exists for
that pattern and has not been needed elsewhere.

## Role

Implementation.
-/

namespace Tautology
namespace List

/-- A positional read below the length lands inside the list: with
`k < xs.length` the value `xs.getD k fallback` is a member, so within range
the fallback never surfaces. -/
theorem getD_mem
    {alpha : Type u} (xs : _root_.List alpha) (fallback : alpha) :
    forall {k : Nat},
      k < xs.length -> _root_.List.Mem (xs.getD k fallback) xs
  | 0, hk => by
      cases xs with
      | nil => exact False.elim (Nat.not_lt_zero 0 hk)
      | cons _ _ => exact _root_.List.Mem.head _
  | k + 1, hk => by
      cases xs with
      | nil => exact False.elim (Nat.not_lt_zero (k + 1) hk)
      | cons head tail =>
          exact _root_.List.Mem.tail head
            (getD_mem tail fallback (Nat.lt_of_succ_lt_succ hk))

/-- Consecutive positional reads of a `Pairwise R` list are related: with
`k + 1 < xs.length`, `R` holds between the entries read at `k` and `k + 1`.
Only the upper index needs a bounds hypothesis; the lower one is then in
range as well. -/
theorem getD_step_of_pairwise
    {alpha : Type u} {R : alpha -> alpha -> Prop}
    (fallback : alpha) :
    forall {xs : _root_.List alpha}, _root_.List.Pairwise R xs ->
      forall {k : Nat}, k + 1 < xs.length ->
        R (xs.getD k fallback) (xs.getD (k + 1) fallback)
  | [], _hpair, k, hk => by
      exact False.elim (Nat.not_lt_zero (k + 1) hk)
  | head :: tail, hpair, 0, hk => by
      cases hpair with
      | cons hhead _htail =>
          change R head (tail.getD 0 fallback)
          apply hhead
          apply getD_mem tail fallback
          exact Nat.lt_of_succ_lt_succ hk
  | head :: tail, hpair, k + 1, hk => by
      cases hpair with
      | cons _hhead htail =>
          change R (tail.getD k fallback) (tail.getD (k + 1) fallback)
          apply getD_step_of_pairwise fallback htail
          exact Nat.lt_of_succ_lt_succ hk

theorem range_pairwise_lt_lt (n : Nat) :
    _root_.List.Pairwise (fun i j : Nat => And (i < j) (j < n))
      (_root_.List.range n) := by
  rw [_root_.List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using And.intro hij hj

end List
end Tautology
