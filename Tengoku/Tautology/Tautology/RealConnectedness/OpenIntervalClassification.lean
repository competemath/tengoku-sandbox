import Tengoku.Tautology.Tautology.RealConnectedness.OpenDecomposition

/-!
# The four shapes an open interval set can take

Completing the decomposition: a nonempty open interval set over a
Dedekind-complete ordered field is a bounded open interval, a lower ray, an
upper ray, or the whole line (`openIntervalSet_classification`). Together with
`Tautology.RealConnectedness.OpenDecomposition` this says every open set is a
countable disjoint union of sets of those four shapes, which is the form the
rest of the library quotes.

The proof splits on whether the set is bounded below and above. Completeness
enters exactly twice, as `exists_glb` and `exists_lub`, converting each bound
that exists into an endpoint; openness then forces the inequalities at those
endpoints to be strict, and interval-ness supplies membership in between.

## Position and role

Implementation module, the last of `RealConnectedness`. It builds on
`Tautology.RealConnectedness.OpenDecomposition`, and
`Tautology.RealTheory.Topology` specialises its results to the selected
carrier. Two private lemmas carry the endpoint strictness and are not part of
the exported interface.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- One of the four open connected shapes, up to extensional equality: a
bounded open interval, a lower ray, an upper ray, or the whole line.
"Generalized" records that the endpoints may be absent, rays and the whole
line being admitted alongside `OpenInterval`, and agreement with the shape is
`SetPred.Same`, matching how sets are compared throughout. -/
def IsGeneralizedOpenInterval (I : alpha -> Prop) : Prop :=
  Or
    (Exists
      (fun a : alpha =>
        Exists
          (fun b : alpha =>
            SetPred.Same I (OpenInterval F a b))))
    (Or
      (Exists
        (fun b : alpha =>
          SetPred.Same I (OpenLowerRay F b)))
      (Or
        (Exists
          (fun a : alpha =>
            SetPred.Same I (OpenUpperRay F a)))
        (SetPred.Same I (SetPred.Universal : alpha -> Prop))))

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

private theorem member_gt_glb_of_open_intervalSet
    {I : alpha -> Prop} {a x : alpha}
    (hOpen : (F C).IsOpen I)
    (hglb : IsGreatestLowerBound (F C).le I a)
    (hxI : I x) :
    (F C).lt a x := by
  let F := F C
  have ha_le_x : F.le a x :=
    IsOrderedFieldBaseLike.glb_le_of_mem F hglb hxI
  apply IsOrderedFieldBaseLike.lt_of_le_of_not_le F ha_le_x
  intro hx_le_a
  cases hOpen x hxI with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          let y := F.midpoint left x
          have hy_left : F.lt left y :=
            IsOrderedFieldBaseLike.left_lt_midpoint F hright.left
          have hy_x : F.lt y x :=
            IsOrderedFieldBaseLike.midpoint_lt_right F hright.left
          have hy_right : F.lt y right :=
            IsOrderedFieldBaseLike.lt_trans F hy_x hright.right.left
          have hyI : I y :=
            hright.right.right y (And.intro hy_left hy_right)
          have ha_y : F.le a y :=
            IsOrderedFieldBaseLike.glb_le_of_mem F hglb hyI
          have hx_y : F.le x y := F.le_trans hx_le_a ha_y
          exact (IsOrderedFieldBaseLike.not_le_of_lt F hy_x) hx_y

private theorem member_lt_lub_of_open_intervalSet
    {I : alpha -> Prop} {b x : alpha}
    (hOpen : (F C).IsOpen I)
    (hlub : IsLeastUpperBound (F C).le I b)
    (hxI : I x) :
    (F C).lt x b := by
  let F := F C
  have hx_le_b : F.le x b :=
    IsOrderedFieldBaseLike.le_lub_of_mem F hlub hxI
  apply IsOrderedFieldBaseLike.lt_of_le_of_not_le F hx_le_b
  intro hb_le_x
  cases hOpen x hxI with
  | intro left hleft =>
      cases hleft with
      | intro right hright =>
          let y := F.midpoint x right
          have hx_y : F.lt x y :=
            IsOrderedFieldBaseLike.left_lt_midpoint F hright.right.left
          have hy_right : F.lt y right :=
            IsOrderedFieldBaseLike.midpoint_lt_right F hright.right.left
          have hleft_y : F.lt left y :=
            IsOrderedFieldBaseLike.lt_trans F hright.left hx_y
          have hyI : I y :=
            hright.right.right y (And.intro hleft_y hy_right)
          have hy_b : F.le y b :=
            IsOrderedFieldBaseLike.le_lub_of_mem F hlub hyI
          have hy_x : F.le y x := F.le_trans hy_b hb_le_x
          exact (IsOrderedFieldBaseLike.not_le_of_lt F hx_y) hy_x

/-- Every nonempty open interval set is one of the four generalized open
intervals, the case split being on which sides of `I` carry bounds;
`exists_glb` and `exists_lub` turn the present bounds into the endpoints,
and this is the only place completeness enters. Openness is what makes those
endpoints strict. The empty set is an open interval set that is none of the
four shapes, hence the nonempty hypothesis. -/
theorem openIntervalSet_classification
    {I : alpha -> Prop}
    (hne : SetPred.Nonempty I)
    (hI : (F C).IsOpenIntervalSet I) :
    (F C).IsGeneralizedOpenInterval I := by
  let F := F C
  have hOpen : F.IsOpen I := hI.left
  have hInterval : F.IsIntervalSet I := hI.right.right
  classical
  by_cases hLower : Exists (IsLowerBound F.le I)
  · cases C.exists_glb I hne hLower with
    | intro a hglb =>
        by_cases hUpper : Exists (IsUpperBound F.le I)
        · cases C.exists_lub I hne hUpper with
          | intro b hlub =>
              refine Or.inl ?_
              refine Exists.intro a ?_
              refine Exists.intro b ?_
              intro x
              constructor
              · intro hxI
                exact And.intro
                  (member_gt_glb_of_open_intervalSet C hOpen hglb hxI)
                  (member_lt_lub_of_open_intervalSet C hOpen hlub hxI)
              · intro hx
                cases IsOrderedFieldBaseLike.exists_gt_of_glb_lt F hglb hx.left with
                | intro y hy =>
                    cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub F hlub hx.right with
                    | intro z hz =>
                        exact hInterval y x z hy.left hz.left
                          (And.intro
                            (IsOrderedFieldBaseLike.le_of_lt F hy.right)
                            (IsOrderedFieldBaseLike.le_of_lt F hz.right))
        · refine Or.inr (Or.inr (Or.inl ?_))
          refine Exists.intro a ?_
          intro x
          constructor
          · intro hxI
            exact member_gt_glb_of_open_intervalSet C hOpen hglb hxI
          · intro hax
            cases IsOrderedFieldBaseLike.exists_gt_of_glb_lt F hglb hax with
            | intro y hy =>
                have hnotUpper : Not (IsUpperBound F.le I x) := by
                  intro hxUpper
                  exact hUpper (Exists.intro x hxUpper)
                cases IsOrderedFieldBaseLike.exists_gt_of_not_upperBound F hnotUpper with
                | intro z hz =>
                    exact hInterval y x z hy.left hz.left
                      (And.intro
                        (IsOrderedFieldBaseLike.le_of_lt F hy.right)
                        (IsOrderedFieldBaseLike.le_of_lt F hz.right))
  · by_cases hUpper : Exists (IsUpperBound F.le I)
    · cases C.exists_lub I hne hUpper with
      | intro b hlub =>
          refine Or.inr (Or.inl ?_)
          refine Exists.intro b ?_
          intro x
          constructor
          · intro hxI
            exact member_lt_lub_of_open_intervalSet C hOpen hlub hxI
          · intro hxb
            have hnotLower : Not (IsLowerBound F.le I x) := by
              intro hxLower
              exact hLower (Exists.intro x hxLower)
            cases IsOrderedFieldBaseLike.exists_lt_of_not_lowerBound F hnotLower with
            | intro y hy =>
                cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub F hlub hxb with
                | intro z hz =>
                    exact hInterval y x z hy.left hz.left
                      (And.intro
                        (IsOrderedFieldBaseLike.le_of_lt F hy.right)
                        (IsOrderedFieldBaseLike.le_of_lt F hz.right))
    · refine Or.inr (Or.inr (Or.inr ?_))
      intro x
      constructor
      · intro _x
        exact True.intro
      · intro _trivial
        have hnotLower : Not (IsLowerBound F.le I x) := by
          intro hxLower
          exact hLower (Exists.intro x hxLower)
        have hnotUpper : Not (IsUpperBound F.le I x) := by
          intro hxUpper
          exact hUpper (Exists.intro x hxUpper)
        cases IsOrderedFieldBaseLike.exists_lt_of_not_lowerBound F hnotLower with
        | intro y hy =>
            cases IsOrderedFieldBaseLike.exists_gt_of_not_upperBound F hnotUpper with
            | intro z hz =>
                exact hInterval y x z hy.left hz.left
                  (And.intro
                    (IsOrderedFieldBaseLike.le_of_lt F hy.right)
                    (IsOrderedFieldBaseLike.le_of_lt F hz.right))

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
