/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kimi K3
-/

module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

@[expose] public section

/-!
# USA Mathematical Olympiad 1983, Problem 1

If six points are chosen sequentially at random on the circumference of a
circle, what is the probability that the triangle formed by the first three
is disjoint from that formed by the second three?
-/

namespace Usa1983P1

/-- The cyclic order in which the six chosen points appear around the circle:
`σ i` is the position of the `i`-th chosen point among the six positions
`0, …, 5` listed in clockwise order. Only the cyclic order of the six points
matters for this problem, and all `6!` orders are equally likely, so we take
the uniform distribution on `Equiv.Perm (Fin 6)` as the sample space. -/
abbrev Ordering := Equiv.Perm (Fin 6)

/-- The event that the triangle formed by the first three points is disjoint
from the triangle formed by the last three points. With six points on a
circle, the two triangles are disjoint iff the two vertex sets do not
interleave around the circle, which for `3 + 3` points means that the first
three points occupy three (cyclically) consecutive positions. -/
def Favorable (σ : Ordering) : Prop :=
  ∃ k : Fin 6, ({σ 0, σ 1, σ 2} : Finset (Fin 6)) = {k, k + 1, k + 2}

instance : DecidablePred Favorable :=
  fun σ ↦ inferInstanceAs
    (Decidable (∃ k : Fin 6, ({σ 0, σ 1, σ 2} : Finset (Fin 6)) = {k, k + 1, k + 2}))

noncomputable abbrev solution : ENNReal := 3 / 10

/-- The number of cyclic orders in which the first three points occupy three
consecutive positions: `6` choices for the starting position of the block,
times `3!` orders of the first three points within the block, times `3!`
orders of the remaining three points. Verified by exhaustive enumeration. -/
lemma card_favorable :
    (Finset.univ.filter Favorable).card = 216 := by
  set_option maxRecDepth 10000 in
  decide

/-- The total number of cyclic orders of the six points. -/
lemma card_orderings : Fintype.card Ordering = 720 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  decide

end Usa1983P1
