import Tengoku.Tautology.Tautology.RealCompactness.ClosedInterval.Statements
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealSequence.Algebra

/-!
# Entry: the supremum property gives finite subcovers

The other completeness entry, landing on the cover side of the graph, and the
only file in this subdirectory whose proof needs no Archimedean input at all.

The set of right endpoints `x` such that `[left, x]` already has a finite
subcover is nonempty and bounded above. If its supremum fell short of the
right end, the cover member containing that supremum would push the set past
it, so the supremum is the right end, and one more member finishes the
interval.

Completeness is spent exactly once, on that supremum.

## Position and role

Entry module, exporting a universe-polymorphic `Target` that
`Tautology.RealCompactness.ClosedInterval.Routes` instantiates at `max u 1`,
the level at which the downstream edges consume compactness. Like its
sequential companion it is proved but not travelled by the selected route.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike
namespace Compactness
namespace FromSupFinite

universe u

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The ordered field carried by the completeness bundle. The only appeal
to completeness below is the `exists_lub` field, invoked once, inside
`finiteSubcover`; the rest is ordered-field reasoning about open intervals
and midpoints. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The promise of this entry point: the field underlying a
Dedekind-complete bundle satisfies the closed-interval compactness node,
for covers indexed at any universe. Where `FromSupSequential` enters the
graph at the sequential Bolzano-Weierstrass node, this entry reaches the
compactness half directly. -/
def Target : Prop :=
  IsOrderedFieldBaseLike.ClosedIntervalCompactnessPrinciple.{u} (F C)

/-- The inductive predicate of the supremum argument: `x` is an extendable
right endpoint when `left ≤ x ≤ right` and the initial segment `[left, x]`
already has a finite subcover. The argument pushes this set rightwards
until its least upper bound can no longer be distinct from `right`. -/
def ExtendableEndpoint {iota : Type u}
    (U : iota -> alpha -> Prop)
    (left right x : alpha) : Prop :=
  And ((F C).le left x)
    (And ((F C).le x right)
      (IsOrderedFieldBaseLike.FiniteSubcover U
        ((F C).ClosedInterval left x)))

theorem left_endpoint_finite_subcover {iota : Type u}
    {left right : alpha} {U : iota -> alpha -> Prop}
    (hle : (F C).le left right)
    (hcover : IsOrderedFieldBaseLike.Covers U
      ((F C).ClosedInterval left right)) :
    IsOrderedFieldBaseLike.FiniteSubcover U
      ((F C).ClosedInterval left left) := by
  have hleft_interval :
      (F C).ClosedInterval left right left :=
    And.intro ((F C).le_refl left) hle
  cases hcover left hleft_interval with
  | intro i hi =>
      refine Exists.intro [i] ?_
      intro x hx
      have hx_eq : x = left :=
        (F C).le_antisymm hx.right hx.left
      refine Exists.intro i ?_
      constructor
      · exact List.Mem.head []
      · rw [hx_eq]
        exact hi

/-- The induction starts at `left`: the degenerate initial segment is
covered by the single member that covers its one point. -/
theorem left_endpoint_extendable {iota : Type u}
    {left right : alpha} {U : iota -> alpha -> Prop}
    (hle : (F C).le left right)
    (hcover : IsOrderedFieldBaseLike.Covers U
      ((F C).ClosedInterval left right)) :
    ExtendableEndpoint C U left right left := by
  constructor
  · exact (F C).le_refl left
  · constructor
    · exact hle
    · exact left_endpoint_finite_subcover C hle hcover

theorem right_endpoint_upperBound {iota : Type u}
    (U : iota -> alpha -> Prop) (left right : alpha) :
    IsUpperBound (F C).le (ExtendableEndpoint C U left right) right := by
  intro x hx
  exact hx.right.left

/-- One extension step, as a statement about lists. Points of `[left, r]`
up to `x` are served by the old list; points beyond `x` exceed `a` and
stay below `r < b`, so the one new member swallows them all. Appending a
single index is what keeps the subcover a list throughout the argument. -/
theorem append_open_interval_cover {iota : Type u}
    {U : iota -> alpha -> Prop}
    {left x r a b : alpha} {i : iota} {js : List iota}
    (hjs :
      IsOrderedFieldBaseLike.ListSubcover U
        ((F C).ClosedInterval left x) js)
    (hax : (F C).lt a x)
    (hrb : (F C).lt r b)
    (hU :
      forall y : alpha,
        (F C).OpenInterval a b y -> U i y) :
    IsOrderedFieldBaseLike.ListSubcover U
      ((F C).ClosedInterval left r) (js ++ [i]) := by
  intro y hy
  by_cases hyx : (F C).le y x
  · cases hjs y (And.intro hy.left hyx) with
    | intro j hj =>
        refine Exists.intro j ?_
        constructor
        · exact List.mem_append_left [i] hj.left
        · exact hj.right
  · have hxy_le : (F C).le x y := by
      cases (F C).le_total x y with
      | inl hxy => exact hxy
      | inr hyx' => exact False.elim (hyx hyx')
    have hxy : (F C).lt x y :=
      IsOrderedFieldBaseLike.lt_of_le_of_not_le (F C) hxy_le hyx
    have hay : (F C).lt a y :=
      IsOrderedFieldBaseLike.lt_trans (F C) hax hxy
    have hyb : (F C).lt y b :=
      IsOrderedFieldBaseLike.lt_of_le_of_lt (F C) hy.right hrb
    refine Exists.intro i ?_
    constructor
    · exact List.mem_append_right js (List.Mem.head [])
    · exact hU y (And.intro hay hyb)

/-- The extension step off the least upper bound: when the supremum `s`
lies strictly inside the open interval `(a, b)` of a cover member and `r`
is a point with `s < r ≤ right` still below `b`, then `r` is extendable.
`exists_lt_of_lt_lub` supplies an extendable `x` with `a < x ≤ s`, whose
finite subcover the step appends the new member to. -/
theorem extend_endpoint_from_lub_neighborhood {iota : Type u}
    {U : iota -> alpha -> Prop}
    {left right s r a b : alpha} {i : iota}
    (hs :
      IsLeastUpperBound (F C).le
        (ExtendableEndpoint C U left right) s)
    (has : (F C).lt a s)
    (hsr : (F C).lt s r)
    (hrright : (F C).le r right)
    (hrb : (F C).lt r b)
    (hU :
      forall y : alpha,
        (F C).OpenInterval a b y -> U i y) :
    ExtendableEndpoint C U left right r := by
  cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub (F C) hs has with
  | intro x hx =>
      have hxE : ExtendableEndpoint C U left right x := hx.left
      have hax : (F C).lt a x := hx.right
      have hxs : (F C).le x s :=
        IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs hxE
      have hxr : (F C).le x r :=
        (F C).le_trans hxs (IsOrderedFieldBaseLike.le_of_lt (F C) hsr)
      constructor
      · exact (F C).le_trans hxE.left hxr
      · constructor
        · exact hrright
        · cases hxE.right.right with
          | intro js hjs =>
              refine Exists.intro (js ++ [i]) ?_
              exact append_open_interval_cover C hjs hax hrb hU

/-- Room above `s`: when `s < right` and `s < b`, the midpoint of `s` with
whichever of `right` and `b` is nearer gives an `r` with `s < r ≤ right`
and `r < b`. -/
theorem exists_right_extension_point {s right b : alpha}
    (hsr : (F C).lt s right)
    (hsb : (F C).lt s b) :
    Exists
      (fun r : alpha =>
        And ((F C).lt s r)
          (And ((F C).le r right) ((F C).lt r b))) := by
  by_cases hright_b : (F C).le right b
  · refine Exists.intro (IsOrderedFieldBaseLike.midpoint (F C) s right) ?_
    constructor
    · exact IsOrderedFieldBaseLike.left_lt_midpoint (F C) hsr
    · constructor
      · exact IsOrderedFieldBaseLike.midpoint_le_right (F C)
          (IsOrderedFieldBaseLike.le_of_lt (F C) hsr)
      · exact IsOrderedFieldBaseLike.lt_of_lt_of_le (F C)
          (IsOrderedFieldBaseLike.midpoint_lt_right (F C) hsr)
          hright_b
  · have hb_right : (F C).le b right := by
      cases (F C).le_total b right with
      | inl hbr => exact hbr
      | inr hrb => exact False.elim (hright_b hrb)
    refine Exists.intro (IsOrderedFieldBaseLike.midpoint (F C) s b) ?_
    constructor
    · exact IsOrderedFieldBaseLike.left_lt_midpoint (F C) hsb
    · constructor
      · exact (F C).le_trans
          (IsOrderedFieldBaseLike.midpoint_le_right (F C)
            (IsOrderedFieldBaseLike.le_of_lt (F C) hsb))
          hb_right
      · exact IsOrderedFieldBaseLike.midpoint_lt_right (F C) hsb

/-- The main theorem: an open cover of a closed interval has a finite
subcover. The extendable endpoints are nonempty and bounded, so
`exists_lub` gives their supremum `s`; if `s < right`, the member covering
`s` extends the set strictly past `s`, contradicting the upper bound, so
`s = right`, and then the member covering `right` itself, appended to a
subcover reaching close enough to `right`, finishes the interval. -/
theorem finiteSubcover {iota : Type u}
    (left right : alpha) (U : iota -> alpha -> Prop)
    (hle : (F C).le left right)
    (hopen : forall i : iota, (F C).IsOpen (U i))
    (hcover : IsOrderedFieldBaseLike.Covers U
      ((F C).ClosedInterval left right)) :
    IsOrderedFieldBaseLike.FiniteSubcover U
      ((F C).ClosedInterval left right) := by
  let E := ExtendableEndpoint C U left right
  have hleftE : E left :=
    left_endpoint_extendable C hle hcover
  have hnonempty : Exists E :=
    Exists.intro left hleftE
  have hbdd : Exists (IsUpperBound (F C).le E) :=
    Exists.intro right (right_endpoint_upperBound C U left right)
  cases C.exists_lub E hnonempty hbdd with
  | intro s hs =>
      have hleft_s : (F C).le left s :=
        IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs hleftE
      have hs_right : (F C).le s right :=
        IsOrderedFieldBaseLike.lub_le_of_upper (F C) hs
          (right_endpoint_upperBound C U left right)
      have hs_eq_right : s = right := by
        by_cases hright_s : (F C).le right s
        · exact (F C).le_antisymm hs_right hright_s
        · have hs_lt_right : (F C).lt s right :=
            IsOrderedFieldBaseLike.lt_of_le_of_not_le (F C)
              hs_right hright_s
          have hs_interval :
              (F C).ClosedInterval left right s :=
            And.intro hleft_s hs_right
          cases hcover s hs_interval with
          | intro i hi =>
              cases hopen i s hi with
              | intro a ha =>
                  cases ha with
                  | intro b hb =>
                      cases exists_right_extension_point C
                          hs_lt_right hb.right.left with
                      | intro r hr =>
                          have hrE : E r :=
                            extend_endpoint_from_lub_neighborhood C hs
                              hb.left hr.left hr.right.left
                              hr.right.right hb.right.right
                          have hrs : (F C).le r s := hs.left r hrE
                          have hbad : (F C).lt r r :=
                            IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
                              hrs hr.left
                          exact False.elim
                            (IsOrderedFieldBaseLike.lt_irrefl (F C) r hbad)
      have hright_interval :
          (F C).ClosedInterval left right right :=
        And.intro hle ((F C).le_refl right)
      cases hcover right hright_interval with
      | intro i hi =>
          cases hopen i right hi with
          | intro a ha =>
              cases ha with
              | intro b hb =>
                  have has : (F C).lt a s := by
                    rw [hs_eq_right]
                    exact hb.left
                  cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub
                      (F C) hs has with
                  | intro x hx =>
                      have hxE : E x := hx.left
                      have hax : (F C).lt a x := hx.right
                      have hxr : (F C).le x right := hxE.right.left
                      cases hxE.right.right with
                      | intro js hjs =>
                          refine Exists.intro (js ++ [i]) ?_
                          exact append_open_interval_cover C hjs hax
                            hb.right.left hb.right.right

/-- The node statement in the structure's own shape, at universe `u`;
`finiteSubcover` above has already proved the mathematical content. -/
theorem compactnessPrinciple :
    IsOrderedFieldBaseLike.ClosedIntervalCompactnessPrinciple.{u} (F C) where
  finite_subcover := by
    intro iota left right U hle hopen hcover
    exact finiteSubcover C left right U hle hopen hcover

/-- The entry point into the graph: a Dedekind-complete ordered field
satisfies the closed-interval compactness node, reached through the
supremum property rather than through Bolzano-Weierstrass. The statement
is universe-polymorphic, and `Routes` runs it at the raised universe the
edges consuming this node demand. -/
theorem target : Target.{u} C :=
  compactnessPrinciple C

end FromSupFinite
end Compactness
end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
