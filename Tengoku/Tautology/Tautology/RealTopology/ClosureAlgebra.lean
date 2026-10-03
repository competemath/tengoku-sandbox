import Tengoku.Tautology.Tautology.RealTopology.Subspace

/-!
# The algebra of interior, closure and boundary

No new definitions -- this is what the operators of
`Tautology.RealTopology.Closed` satisfy. The interior is the largest open
subset and is open; the closure is the smallest closed superset and is closed;
closedness is equivalent to the closure being contained in the set; interior
distributes over binary intersection and closure over binary union, while
closure over intersection holds in one direction only; and the boundary is the
closure met with the closure of the complement.

The one place where something has to be constructed rather than transported is
`not_closure_witness_early`: a point outside the closure comes with an open set
separating it from the set. That witness is the engine of the hard direction of
the closedness criterion, and everything else in the file moves open-set
quantifiers around.

## Position and role

Implementation module, built on `Tautology.RealTopology.Subspace` and feeding
`Tautology.RealTopology.Sequential`. Stated over an arbitrary ordered field:
closedness is defined here through complements rather than through sequences,
so neither completeness nor an Archimedean principle is needed.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

theorem subset_closure (S : alpha -> Prop) :
    SetPred.Subset S (Closure F S) := by
  intro x hx U hUopen hxU
  exact Exists.intro x (And.intro hx hxU)

theorem closure_mono {S T : alpha -> Prop}
    (hST : SetPred.Subset S T) :
    SetPred.Subset (Closure F S) (Closure F T) := by
  intro x hx U hUopen hxU
  cases hx U hUopen hxU with
  | intro y hy =>
      exact Exists.intro y (And.intro (hST y hy.left) hy.right)

theorem interior_subset (S : alpha -> Prop) :
    SetPred.Subset (Interior F S) S := by
  intro x hx
  cases hx with
  | intro U hU =>
      exact hU.right.right x hU.right.left

theorem open_subset_interior {U S : alpha -> Prop}
    (hUopen : IsOpen F U)
    (hUS : SetPred.Subset U S) :
    SetPred.Subset U (Interior F S) := by
  intro x hx
  exact Exists.intro U
    (And.intro hUopen (And.intro hx hUS))

/-- The interior of any set is open. This is not definitional:
`InteriorPoint` only witnesses some open set around each point, and the
proof re-witnesses through the interval that this open set itself provides
at the point. -/
theorem open_interior (S : alpha -> Prop) :
    IsOpen F (Interior F S) := by
  intro x hx
  cases hx with
  | intro U hU =>
      cases hU.left x hU.right.left with
      | intro left hleft =>
          cases hleft with
          | intro right hright =>
              refine Exists.intro left ?_
              refine Exists.intro right ?_
              refine And.intro hright.left ?_
              refine And.intro hright.right.left ?_
              intro y hy
              exact Exists.intro U
                (And.intro hU.left
                  (And.intro (hright.right.right y hy) hU.right.right))

/-- The maximality property of the interior under its usual name -- any open
subset of `S` sits inside `Interior S`. Literally `open_subset_interior`,
restated because the maximality reading is the one
the algebra of interiors is standardly organised around. -/
theorem interior_maximal_open {U S : alpha -> Prop}
    (hUopen : IsOpen F U)
    (hUS : SetPred.Subset U S) :
    SetPred.Subset U (Interior F S) :=
  open_subset_interior F hUopen hUS

/-- Interior commutes with binary intersection on the nose, as a pointwise
`Same` rather than a one-sided inclusion. The direction needing work
intersects the two witnessing open sets, using that finite intersections
of open sets are open. -/
theorem interior_inter_same (A B : alpha -> Prop) :
    SetPred.Same
      (Interior F (SetPred.Inter A B))
      (SetPred.Inter (Interior F A) (Interior F B)) := by
  intro x
  constructor
  · intro hx
    cases hx with
    | intro U hU =>
        exact And.intro
          (Exists.intro U
            (And.intro hU.left
              (And.intro hU.right.left
                (fun y hy => (hU.right.right y hy).left))))
          (Exists.intro U
            (And.intro hU.left
              (And.intro hU.right.left
                (fun y hy => (hU.right.right y hy).right))))
  · intro hx
    cases hx.left with
    | intro U hU =>
        cases hx.right with
        | intro V hV =>
            exact Exists.intro (SetPred.Inter U V)
              (And.intro (open_inter F hU.left hV.left)
                (And.intro (And.intro hU.right.left hV.right.left)
                  (fun y hy =>
                    And.intro
                      (hU.right.right y hy.left)
                      (hV.right.right y hy.right))))

/-- Closure distributes over binary intersection only one way. Contrast
`closure_union_same`, where the corresponding statement for unions is exact;
no reverse inclusion is claimed here. -/
theorem closure_inter_subset (A B : alpha -> Prop) :
    SetPred.Subset
      (Closure F (SetPred.Inter A B))
      (SetPred.Inter (Closure F A) (Closure F B)) := by
  intro x hx
  exact And.intro
    (closure_mono F (S := SetPred.Inter A B) (T := A)
      (fun y hy => hy.left) x hx)
    (closure_mono F (S := SetPred.Inter A B) (T := B)
      (fun y hy => hy.right) x hx)

/-- A point outside the closure can be separated from the set: some open
neighborhood of `x` misses `S` entirely. The proof is pure classical logic
on the existential, and this is the engine behind
`closed_of_closure_subset` below. -/
theorem not_closure_witness_early {S : alpha -> Prop} {x : alpha}
    (hx : Not (Closure F S x)) :
    Exists
      (fun U : alpha -> Prop =>
        And (IsOpen F U)
          (And (U x) (forall y : alpha, S y -> Not (U y)))) := by
  classical
  by_cases h :
      Exists
        (fun U : alpha -> Prop =>
          And (IsOpen F U)
            (And (U x) (forall y : alpha, S y -> Not (U y))))
  · exact h
  · exact False.elim
      (hx
        (fun U hUopen hxU =>
          by
            by_cases hex : Exists (fun y : alpha => And (S y) (U y))
            · exact hex
            · exact False.elim
                (h
                  (Exists.intro U
                    (And.intro hUopen
                      (And.intro hxU
                        (fun y hyS hyU =>
                          hex (Exists.intro y
                            (And.intro hyS hyU)))))))))

/-- The closure is contained in every closed superset of `S`; together with
`closed_closure` this makes it the smallest closed set above `S`. Immediate
in this form: the superset's complement is an open neighborhood of any
outside point, and a closure point meets every such neighborhood. -/
theorem closure_minimal_closed {S Cset : alpha -> Prop}
    (hclosed : IsClosed F Cset)
    (hSC : SetPred.Subset S Cset) :
    SetPred.Subset (Closure F S) Cset := by
  intro x hx
  classical
  by_cases hxC : Cset x
  · exact hxC
  · cases hx (SetPred.Compl Cset) hclosed hxC with
    | intro y hy =>
        exact False.elim (hy.right (hSC y hy.left))

theorem closure_subset_of_closed {S : alpha -> Prop}
    (hclosed : IsClosed F S) :
    SetPred.Subset (Closure F S) S :=
  closure_minimal_closed F hclosed (SetPred.subset_refl S)

/-- The converse of `closure_subset_of_closed`, and the nontrivial half of
the closedness test: if every closure point of `S` already lies in `S`,
then `S` is closed. Each outside point is separated from `S` by the open
set of `not_closure_witness_early`, and that set's witness interval stays
inside the complement. -/
theorem closed_of_closure_subset {S : alpha -> Prop}
    (hsub : SetPred.Subset (Closure F S) S) :
    IsClosed F S := by
  intro x hxS
  have hxNotClosure : Not (Closure F S x) := by
    intro hxClosure
    exact hxS (hsub x hxClosure)
  cases not_closure_witness_early F hxNotClosure with
  | intro U hU =>
      cases hU.left x hU.right.left with
      | intro left hleft =>
          cases hleft with
          | intro right hright =>
              exact Exists.intro left
                (Exists.intro right
                  (And.intro hright.left
                    (And.intro hright.right.left
                      (fun y hy hyS =>
                        hU.right.right y hyS
                          (hright.right.right y hy)))))

theorem closed_iff_closure_subset (S : alpha -> Prop) :
    IsClosed F S <-> SetPred.Subset (Closure F S) S :=
  Iff.intro
    (closure_subset_of_closed F)
    (closed_of_closure_subset F)

/-- The closure of a set is itself closed. The proof plays the closure
condition twice: an open set meeting `Closure S` at some `y` is itself a
neighborhood of `y`, so it already meets `S`, and no new closure points
appear. -/
theorem closed_closure (S : alpha -> Prop) :
    IsClosed F (Closure F S) := by
  apply closed_of_closure_subset F
  intro x hx U hUopen hxU
  cases hx U hUopen hxU with
  | intro y hy =>
      exact hy.left U hUopen hy.right

theorem closure_union_subset_union_closure (A B : alpha -> Prop) :
    SetPred.Subset
      (SetPred.Union (Closure F A) (Closure F B))
      (Closure F (SetPred.Union A B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      exact closure_mono F (S := A) (T := SetPred.Union A B)
        (fun y hy => Or.inl hy) x hxA
  | inr hxB =>
      exact closure_mono F (S := B) (T := SetPred.Union A B)
        (fun y hy => Or.inr hy) x hxB

/-- The separation witness of `not_closure_witness_early`, restated next to
the results that use it. -/
theorem not_closure_witness {S : alpha -> Prop} {x : alpha}
    (hx : Not (Closure F S x)) :
    Exists
      (fun U : alpha -> Prop =>
        And (IsOpen F U)
          (And (U x) (forall y : alpha, S y -> Not (U y)))) :=
  not_closure_witness_early F hx

/-- Closure commutes with binary union on the nose. The direction needing
work separates `x` from `A` and from `B` by open sets and intersects the
two; the other direction is monotonicity. -/
theorem closure_union_same (A B : alpha -> Prop) :
    SetPred.Same
      (Closure F (SetPred.Union A B))
      (SetPred.Union (Closure F A) (Closure F B)) := by
  intro x
  constructor
  · intro hx
    classical
    by_cases hxA : Closure F A x
    · exact Or.inl hxA
    · by_cases hxB : Closure F B x
      · exact Or.inr hxB
      · cases not_closure_witness F hxA with
        | intro U hU =>
            cases not_closure_witness F hxB with
            | intro V hV =>
                cases hx (SetPred.Inter U V)
                    (open_inter F hU.left hV.left)
                    (And.intro hU.right.left hV.right.left) with
                | intro y hy =>
                    cases hy.left with
                    | inl hyA =>
                        exact False.elim
                          (hU.right.right y hyA hy.right.left)
                    | inr hyB =>
                        exact False.elim
                          (hV.right.right y hyB hy.right.right)
  · intro hx
    exact closure_union_subset_union_closure F A B x hx

/-- The boundary as an intersection of two closures, by `rfl`: `Boundary` is
defined as exactly this intersection in `Tautology.RealTopology.Closed`, so
this records the definitional unfolding rather than proving anything. -/
theorem boundary_eq_closure_inter_closure_compl (S : alpha -> Prop) :
    Boundary F S = SetPred.Inter (Closure F S) (Closure F (SetPred.Compl S)) :=
  rfl

/-- The same unfolding as a pointwise `Same` -- the form the `RealTheory`
facade re-exports. -/
theorem boundary_same_closure_inter_closure_compl (S : alpha -> Prop) :
    SetPred.Same
      (Boundary F S)
      (SetPred.Inter (Closure F S) (Closure F (SetPred.Compl S))) := by
  intro x
  exact Iff.rfl

theorem boundary_subset_closure (S : alpha -> Prop) :
    SetPred.Subset (Boundary F S) (Closure F S) := by
  intro x hx
  exact hx.left

/-- The boundary of a set and of its complement agree. In the
closure-intersection form above this is manifest, the two factors just
swap; the proof only chases the double complement back into place. -/
theorem boundary_compl_same (S : alpha -> Prop) :
    SetPred.Same (Boundary F (SetPred.Compl S)) (Boundary F S) := by
  intro x
  classical
  have hdouble_to :
      SetPred.Subset (SetPred.Compl (SetPred.Compl S)) S := by
    intro y hyy
    by_cases hyS : S y
    · exact hyS
    · exact False.elim (hyy hyS)
  have hto_double :
      SetPred.Subset S (SetPred.Compl (SetPred.Compl S)) := by
    intro y hyS hnotS
    exact hnotS hyS
  constructor
  · intro hx
    exact And.intro
      (closure_mono F hdouble_to x hx.right)
      hx.left
  · intro hx
    exact And.intro
      hx.right
      (closure_mono F hto_double x hx.left)

end IsOrderedFieldBaseLike
end Tautology
