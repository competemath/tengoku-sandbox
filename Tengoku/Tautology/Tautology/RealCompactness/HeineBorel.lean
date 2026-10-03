import Tengoku.Tautology.Tautology.RealBootstrap.Lattice
import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealSequence.Order

/-!
# Compact subsets are exactly the closed bounded ones

The Heine-Borel theorem at subset level, and the place where the route graph's
output is spent: compactness of a closed interval enters as a hypothesis, and
the file converts it into a characterisation of compact subsets.

The three directions cost different things. Compactness of a closed bounded set
is the only one that consumes the closed-interval principle: adjoin the
complement of the set to its cover as an extra open member indexed by `none`,
apply the principle to the whole interval, and project the resulting finite
list of optional indices back. Boundedness and closedness of a compact set need
no completeness at all -- boundedness by covering the set with unit intervals
centred at its own points and folding the finitely many centres, closedness by
covering with balls of half the distance to an outside point and running the
minimum radius over the finite subcover.

The unit-interval cover has to be indexed by the points themselves, which do
not live in the cover's universe; that is why `ULift.{u,0}` appears here. It is
the same rigidity that `Tautology.RealCompactness.Compact` records for
`IsCompact.{u}`, not a stylistic artefact.

## Position and role

Implementation module. Its hypothesis is supplied at the selected carrier by
`Tautology.RealCompactness.ClosedInterval.Selected`, and its results reach the
library through the facade `Tautology.RealTheory.Compactness`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

universe u

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The indices appearing as `some` entries of a list of optional indices, with
the `none` entries dropped. It converts a finite subcover drawn from an
`Option`-indexed family back into an index list of the original family, which
is how `compact_of_closed_subset_closedInterval` below, and the image
compactness proof of `Tautology.RealFunction.Compact`, undo the adjunction of
an extra open set. -/
def optionSomeList {iota : Type u} : List (Option iota) -> List iota
  | [] => []
  | none :: rest => optionSomeList rest
  | some i :: rest => i :: optionSomeList rest

/-- Membership survives the filtering: an entry witnessed as `some i` of
the list gives an entry `i` of the `some`-projection, so a point covered by
an original family member stays covered after the optional indices are
projected away. -/
theorem mem_optionSomeList_of_mem_some {iota : Type u}
    {i : iota} {js : List (Option iota)}
    (h : List.Mem (some i) js) :
    List.Mem i (optionSomeList js) := by
  induction js with
  | nil =>
      cases h
  | cons j rest ih =>
      cases j with
      | none =>
          cases h with
          | tail _ htail =>
              exact ih htail
      | some k =>
          cases h with
          | head =>
              exact List.Mem.head _
          | tail _ htail =>
              exact List.Mem.tail _ (ih htail)

/-- The points of a list of lifted points, with the universe lift undone.
`IsCompact` fixes one universe for the index types of covers, so a cover
indexed by the field's own points has to run over `ULift.{u, 0} alpha`; this
is the projection back, applied below to the centres of a finite subcover. -/
def centerList : List (ULift.{u, 0} alpha) -> List alpha
  | [] => []
  | c :: rest => c.down :: centerList rest

theorem mem_centerList_of_mem {c : ULift.{u, 0} alpha} :
    forall {cs : List (ULift.{u, 0} alpha)},
      List.Mem c cs -> List.Mem c.down (centerList cs)
  | [], h => by
      cases h
  | d :: rest, h => by
      cases h with
      | head =>
          exact List.Mem.head _
      | tail _ htail =>
          exact List.Mem.tail _ (mem_centerList_of_mem htail)

/-- A fold producing a lower bound for the quantities `x - 1` with `x` on
the list: each step keeps the smaller of `x - 1` and the bound for the
rest. The empty-list value, zero, is a convention that never matters, since
only the companion lemma reading the bound off a member is ever used. -/
noncomputable def finiteLower : List alpha -> alpha
  | [] => F.zero
  | x :: rest =>
      let r := finiteLower rest
      if F.le (F.sub x F.one) r then F.sub x F.one else r

/-- The upper mirror of `finiteLower`: a fold producing an upper bound for
the quantities `x + 1` with `x` on the list. -/
noncomputable def finiteUpper : List alpha -> alpha
  | [] => F.zero
  | x :: rest =>
      let r := finiteUpper rest
      if F.le r (F.add x F.one) then F.add x F.one else r

/-- The fold of `finiteLower` really is a lower bound: a listed entry `x`
has the returned value at or below `x - 1`. Together with its mirror
`add_one_le_finiteUpper_of_mem` this is all that is ever asked of the two
folds; their behaviour away from the listed entries is irrelevant. -/
theorem finiteLower_le_sub_one_of_mem {x : alpha}
    {xs : List alpha}
    (hmem : List.Mem x xs) :
    F.le (finiteLower F xs) (F.sub x F.one) := by
  induction xs with
  | nil =>
      cases hmem
  | cons y ys ih =>
      dsimp [finiteLower]
      let r := finiteLower F ys
      by_cases hy : F.le (F.sub y F.one) r
      · rw [ite_eq_left hy]
        cases hmem with
        | head =>
            exact F.le_refl (F.sub x F.one)
        | tail _ htail =>
            exact F.le_trans hy (ih htail)
      · rw [ite_eq_right hy]
        cases hmem with
        | head =>
            cases F.le_total r (F.sub x F.one) with
            | inl h => exact h
            | inr h => exact False.elim (hy h)
        | tail _ htail =>
            exact ih htail

/-- The mirror of `finiteLower_le_sub_one_of_mem`: a listed entry `x` has
`x + 1` at or below the value returned by the `finiteUpper` fold. -/
theorem add_one_le_finiteUpper_of_mem {x : alpha}
    {xs : List alpha}
    (hmem : List.Mem x xs) :
    F.le (F.add x F.one) (finiteUpper F xs) := by
  induction xs with
  | nil =>
      cases hmem
  | cons y ys ih =>
      dsimp [finiteUpper]
      let r := finiteUpper F ys
      by_cases hy : F.le r (F.add y F.one)
      · rw [ite_eq_left hy]
        cases hmem with
        | head =>
            exact F.le_refl (F.add x F.one)
        | tail _ htail =>
            exact F.le_trans (ih htail) hy
      · rw [ite_eq_right hy]
        cases hmem with
        | head =>
            cases F.le_total (F.add x F.one) r with
            | inl h => exact h
            | inr h => exact False.elim (hy h)
        | tail _ htail =>
            exact ih htail

/-- The pairwise minimum of the field's order, forwarding `min2` of
`Tautology.RealBootstrap.Lattice`; the three lemmas that follow restate the
pieces of the `min2` interface that the half-radius computations below use. -/
noncomputable def min (x y : alpha) : alpha :=
  min2 F x y

theorem min_le_left (x y : alpha) :
    F.le (min F x y) x :=
  min2_le_left F x y

theorem min_le_right (x y : alpha) :
    F.le (min F x y) y :=
  min2_le_right F x y

theorem min_pos {x y : alpha}
    (hx : F.lt F.zero x) (hy : F.lt F.zero y) :
    F.lt F.zero (min F x y) :=
  min2_pos F hx hy

/-- The member at centre `c` of the open cover that proves compact sets are
closed, for a point `x` outside the set: the empty interval when `c = x`,
and otherwise the open interval of radius half the distance from `c` to `x`,
centred at `c`. Halving makes this member disjoint from the interval of the
same radius about `x`, by the triangle inequality, which is what lets a
finite subcover of this cover produce a neighbourhood of `x` missing the
set. -/
def compactClosedCover (x : alpha) :
    ULift.{u, 0} alpha -> alpha -> Prop :=
  fun c y =>
    if c.down = x then
      OpenInterval F x x y
    else
      OpenInterval F
        (F.sub c.down (half F (dist F c.down x)))
        (F.add c.down (half F (dist F c.down x))) y

/-- The radius read off a finite subcover of `compactClosedCover`: the
running minimum of the half-distances of the listed centres, skipping the
centres equal to `x` and starting from one. It plays the role of a Lebesgue
number for the point `x` -- positive, and small enough to honour every
constraint at once. -/
noncomputable def compactClosedRadius (x : alpha) :
    List (ULift.{u, 0} alpha) -> alpha
  | [] => F.one
  | c :: cs =>
      if c.down = x then
        compactClosedRadius x cs
      else
        min F (half F (dist F c.down x)) (compactClosedRadius x cs)

/-- The running minimum stays positive: it starts at one and only ever meets
positive half-distances. The centres equal to `x` are skipped precisely
because the members of the cover they carry are empty. -/
theorem compactClosedRadius_pos (x : alpha) :
    forall cs : List (ULift.{u, 0} alpha),
      F.lt F.zero (compactClosedRadius F x cs)
  | [] => zero_lt_one F
  | c :: cs => by
      dsimp [compactClosedRadius]
      by_cases hcx : c.down = x
      · rw [ite_eq_left hcx]
        exact compactClosedRadius_pos x cs
      · rw [ite_eq_right hcx]
        exact min_pos F
          (half_pos F (dist_pos_of_ne F hcx))
          (compactClosedRadius_pos x cs)

/-- The running minimum bounds the half-distance of every listed centre
other than `x`: minima only shrink as the list grows, and at that centre's
own entry the fold met its half-distance. The exclusion of `x` matches the
empty member such centres carry. -/
theorem compactClosedRadius_le_half_dist_of_mem {x : alpha}
    {c : ULift.{u, 0} alpha} {cs : List (ULift.{u, 0} alpha)}
    (hmem : List.Mem c cs)
    (hcx : Not (c.down = x)) :
    F.le (compactClosedRadius F x cs)
      (half F (dist F c.down x)) := by
  induction cs with
  | nil =>
      cases hmem
  | cons d ds ih =>
      dsimp [compactClosedRadius]
      by_cases hdx : d.down = x
      · rw [ite_eq_left hdx]
        cases hmem with
        | head =>
            exact False.elim (hcx hdx)
        | tail _ htail =>
            exact ih htail
      · rw [ite_eq_right hdx]
        cases hmem with
        | head =>
            exact min_le_left F
              (half F (dist F c.down x))
              (compactClosedRadius F x ds)
        | tail _ htail =>
            exact F.le_trans
              (min_le_right F
                (half F (dist F d.down x))
                (compactClosedRadius F x ds))
              (ih htail)

theorem compact_empty :
    IsCompact.{u} F (SetPred.Empty : alpha -> Prop) := by
  exact
    fun {idx : Type u} (U : idx -> alpha -> Prop)
      (hopen : forall i : idx, IsOpen F (U i))
      (hcover : Covers U (SetPred.Empty : alpha -> Prop)) => by
    refine Exists.intro ([] : List idx) ?_
    intro x hx
    exact False.elim hx

/-- The cover of the adjunction step: the `none` index carries the
complement of `S`, every other index the corresponding member of `U`.
Adjoining one more open set to a cover of `S` turns it into a cover of any
closed interval around `S`, provided that complement is open, which is
exactly the closedness hypothesis of the theorem using this. -/
def closedSubsetIntervalCover {iota : Type u}
    (S : alpha -> Prop) (U : iota -> alpha -> Prop) :
    Option iota -> alpha -> Prop
  | none => SetPred.Compl S
  | some i => U i

/-- A closed subset of a closed interval is compact, from the closed-interval
principle. The given cover of the subset is widened, through
`closedSubsetIntervalCover`, to a cover of the whole interval by adjoining
the complement of `S`; the principle returns a finite list of optional
indices, and `optionSomeList` drops the complement entry should it appear. -/
theorem compact_of_closed_subset_closedInterval
    (hcompact : ClosedIntervalCompactnessPrinciple.{u} F)
    {S : alpha -> Prop} {left right : alpha}
    (hle : F.le left right)
    (hclosed : IsClosed F S)
    (hsub : SetPred.Subset S (ClosedInterval F left right)) :
    IsCompact.{u} F S := by
  exact
    fun {idx : Type u} (U : idx -> alpha -> Prop)
      (hopen : forall i : idx, IsOpen F (U i))
      (hcover : Covers U S) => by
    let W : Option idx -> alpha -> Prop :=
      closedSubsetIntervalCover S U
    have hWopen : forall j : Option idx, IsOpen F (W j) := by
      intro j
      cases j with
      | none =>
          exact hclosed
      | some i =>
          exact hopen i
    have hWcover : Covers W (ClosedInterval F left right) := by
      intro x hxInterval
      classical
      by_cases hxS : S x
      · cases hcover x hxS with
        | intro i hi =>
            exact Exists.intro (some i) hi
      · exact Exists.intro none hxS
    cases hcompact.finite_subcover left right W hle hWopen hWcover with
    | intro js hjs =>
        refine Exists.intro (optionSomeList js) ?_
        intro x hxS
        have hxInterval : ClosedInterval F left right x :=
          hsub x hxS
        cases hjs x hxInterval with
        | intro j hj =>
            cases j with
            | none =>
                exact False.elim (hj.right hxS)
            | some i =>
                exact
                  Exists.intro i
                    (And.intro
                      (mem_optionSomeList_of_mem_some hj.left)
                      hj.right)

/-- The Heine-Borel direction that spends completeness: a closed bounded set
is compact. The endpoints of `SetBounded` need not be ordered, so the
seating of `S` into its interval goes through a point of `S` that forces
their order, and the empty set, having no such point, is covered by the
empty list outright. -/
theorem compact_of_closed_bounded
    (hcompact : ClosedIntervalCompactnessPrinciple.{u} F)
    {S : alpha -> Prop}
    (hclosed : IsClosed F S)
    (hbdd : SetBounded F S) :
    IsCompact.{u} F S := by
  classical
  by_cases hnonempty : SetPred.Nonempty S
  · cases hbdd with
    | intro left hleft =>
        cases hleft with
        | intro right hbounds =>
            cases hnonempty with
            | intro x hxS =>
                have hxBounds := hbounds x hxS
                have hle : F.le left right :=
                  F.le_trans hxBounds.left hxBounds.right
                exact compact_of_closed_subset_closedInterval F hcompact
                  hle hclosed hbounds
  · intro U hopen hcover
    refine Exists.intro [] ?_
    intro x hxS
    exact False.elim (hnonempty (Exists.intro x hxS))

/-- Compact sets are bounded, over any ordered field with no completeness
entering. The set is covered by the open unit intervals centred at its own
points, indexed through `ULift.{u, 0} alpha` because `IsCompact` fixes the
universe of index types, and the bounds are read off the finitely many
centres that survive, shifted out by one. -/
theorem bounded_of_compact {S : alpha -> Prop}
    (hcompact : IsCompact.{u} F S) :
    SetBounded F S := by
  let U : ULift.{u, 0} alpha -> alpha -> Prop :=
    fun c => OpenInterval F (F.sub c.down F.one) (F.add c.down F.one)
  have hopen : forall c : ULift.{u, 0} alpha, IsOpen F (U c) := by
    intro c
    exact open_interval F (F.sub c.down F.one) (F.add c.down F.one)
  have hcover : Covers U S := by
    intro x hxS
    exact Exists.intro (ULift.up x)
      (And.intro (sub_one_lt F x) (lt_add_one F x))
  cases hcompact U hopen hcover with
  | intro cs hcs =>
      let centers := centerList (alpha := alpha) cs
      refine Exists.intro (finiteLower F centers) ?_
      refine Exists.intro (finiteUpper F centers) ?_
      intro x hxS
      cases hcs x hxS with
      | intro c hc =>
          have hmem : List.Mem c.down centers :=
            mem_centerList_of_mem hc.left
          have hleft :
              F.le (finiteLower F centers) (F.sub c.down F.one) :=
            finiteLower_le_sub_one_of_mem F hmem
          have hright :
              F.le (F.add c.down F.one) (finiteUpper F centers) :=
            add_one_le_finiteUpper_of_mem F hmem
          exact And.intro
            (F.le_trans hleft (le_of_lt F hc.right.left))
            (F.le_trans (le_of_lt F hc.right.right) hright)

/-- Compact sets are closed, again over any ordered field. For `x` outside
the set, the disjoint-balls cover `compactClosedCover` has a finite
subcover, and the radius `compactClosedRadius` extracted from its centres
is small enough that the interval of that radius about `x` meets no member,
hence misses the set entirely. -/
theorem closed_of_compact {S : alpha -> Prop}
    (hcompact : IsCompact.{u} F S) :
    IsClosed F S := by
  intro x hxS
  let U : ULift.{u, 0} alpha -> alpha -> Prop :=
    compactClosedCover F x
  have hopen : forall c : ULift.{u, 0} alpha, IsOpen F (U c) := by
    intro c
    dsimp [U]
    unfold compactClosedCover
    by_cases hcx : c.down = x
    · apply open_congr F (open_interval F x x)
      intro y
      dsimp
      rw [ite_eq_left hcx]
    · apply open_congr F
        (open_interval F
          (F.sub c.down (half F (dist F c.down x)))
          (F.add c.down (half F (dist F c.down x))))
      intro y
      dsimp
      rw [ite_eq_right hcx]
  have hcover : Covers U S := by
    intro y hyS
    have hyx : Not (y = x) := by
      intro hyx
      exact hxS (by rwa [hyx] at hyS)
    refine Exists.intro (ULift.up y) ?_
    dsimp [U, compactClosedCover]
    rw [ite_eq_right hyx]
    have hrpos :
        F.lt F.zero (half F (dist F y x)) :=
      half_pos F (dist_pos_of_ne F hyx)
    exact And.intro
      (sub_lt_self_of_pos F hrpos)
      (lt_add_of_pos F hrpos)
  cases hcompact U hopen hcover with
  | intro cs hcs =>
      let delta := compactClosedRadius F x cs
      have hdelta : F.lt F.zero delta :=
        compactClosedRadius_pos F x cs
      refine Exists.intro (F.sub x delta) ?_
      refine Exists.intro (F.add x delta) ?_
      refine And.intro (sub_lt_self_of_pos F hdelta) ?_
      refine And.intro (lt_add_of_pos F hdelta) ?_
      intro y hyInterval hyS
      have hyCover := hcs y hyS
      cases hyCover with
      | intro c hc =>
          dsimp [U, compactClosedCover] at hc
          by_cases hcx : c.down = x
          · rw [ite_eq_left hcx] at hc
            exact (lt_asymm F hc.right.left) hc.right.right
          · rw [ite_eq_right hcx] at hc
            let r := half F (dist F c.down x)
            have hdelta_le_r :
                F.le delta r :=
              compactClosedRadius_le_half_dist_of_mem F
                hc.left hcx
            have hyx_dist :
                F.lt (dist F y x) delta := by
              unfold dist
              exact abs_sub_lt_of_bounds F
                hyInterval.left hyInterval.right
            have hyc_dist :
                F.lt (dist F y c.down) r := by
              unfold dist
              exact abs_sub_lt_of_bounds F
                hc.right.left hc.right.right
            have hyx_lt_r :
                F.lt (dist F y x) r :=
              lt_of_lt_of_le F hyx_dist hdelta_le_r
            have hsum :
                F.lt
                  (F.add (dist F y x) (dist F y c.down))
                  (dist F c.down x) := by
              have hsum_r :
                  F.lt
                    (F.add (dist F y x) (dist F y c.down))
                    (F.add r r) :=
                add_lt_add F hyx_lt_r hyc_dist
              rwa [half_add_half F (dist F c.down x)] at hsum_r
            have htri :
                F.le (dist F c.down x)
                  (F.add (dist F y x) (dist F y c.down)) := by
              have h :=
                dist_triangle F c.down y x
              rwa [
                dist_comm F c.down y,
                F.add_comm (dist F y c.down) (dist F y x)
              ] at h
            have hbad :
                F.lt (dist F c.down x) (dist F c.down x) :=
              lt_of_le_of_lt F htri hsum
            exact (lt_irrefl F (dist F c.down x)) hbad

/-- The Heine-Borel equivalence. Only the direction from closed-and-bounded
to compact receives the closed-interval principle; the two converses hold
over any ordered field and are where the unit-interval and disjoint-balls
covers enter. -/
theorem compact_iff_closed_bounded
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F)
    (S : alpha -> Prop) :
    IsCompact.{u} F S <-> And (IsClosed F S) (SetBounded F S) := by
  constructor
  · intro hcompact
    exact And.intro
      (closed_of_compact F hcompact)
      (bounded_of_compact F hcompact)
  · intro h
    exact compact_of_closed_bounded F
      hclosedIntervalCompact h.left h.right

/-- The closed-interval principle repackaged as the full Heine-Borel
statement, with the subset universally quantified the way
`CompactIffClosedBoundedStatement` demands. This is the packaged form
`Tautology.RealTheory.Compactness` carries down to the rest of the library. -/
def realSubsetCompactnessFiniteCoverPackage
    (hclosedIntervalCompact : ClosedIntervalCompactnessPrinciple.{u} F) :
    CompactIffClosedBoundedStatement.{u} F :=
  compact_iff_closed_bounded F hclosedIntervalCompact

end

end IsOrderedFieldBaseLike
end Tautology
