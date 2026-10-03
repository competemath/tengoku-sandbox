import Tengoku.Tautology.Tautology.RealBootstrap.Supremum
import Tengoku.Tautology.Tautology.RealSequence.Order
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# Entry: the supremum property gives the Cauchy criterion

The third way in, landing directly on the Cauchy node without passing through
either of the others.

Completeness is spent on a supremum, as in the sibling entries; what differs is
the set it is taken of, which has to be built from the Cauchy condition rather
than read off a monotone sequence.

## Position and role

Entry module exporting `cauchyCriterion`, feeding
`RealSequence.Principles.Routes.fromCauchy`. Proved and not travelled by the
selected route.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

namespace FromSupCauchy

/-- The ordered-field reduct of `C`; the supremum property of `C` is used
only through `exists_lub`, in the construction below. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- The pivotal definition of this entry: `x` is an eventual lower bound of
`u` when from some index on every term sits at or above `x`. The limit of the
Cauchy sequence will be the supremum of exactly these, so no limit has to be
guessed before it is proved to exist. -/
def EventualLowerBound (u : Nat -> alpha) (x : alpha) : Prop :=
  Exists (fun N : Nat => forall n : Nat, N <= n -> (F C).le x (u n))

theorem eventualLowerBound_mono {u : Nat -> alpha} {x y : alpha}
    (hxy : (F C).le y x)
    (hx : EventualLowerBound C u x) :
    EventualLowerBound C u y := by
  cases hx with
  | intro N hN =>
      exact Exists.intro N
        (fun n hn => (F C).le_trans hxy (hN n hn))

theorem cauchy_tail_center_lower {u : Nat -> alpha}
    {eps : alpha} {N n : Nat}
    (hc :
      forall n m : Nat,
        N <= n ->
          N <= m ->
            (F C).lt
              (IsOrderedFieldBaseLike.abs (F C)
                ((F C).sub (u n) (u m))) eps)
    (hn : N <= n) :
    (F C).lt ((F C).sub (u N) eps) (u n) := by
  have hclose : (F C).lt
      (IsOrderedFieldBaseLike.abs (F C) ((F C).sub (u n) (u N))) eps :=
    hc n N hn (Nat.le_refl N)
  exact IsOrderedFieldBaseLike.abs_sub_lt_left (F C) hclose

theorem cauchy_tail_center_upper {u : Nat -> alpha}
    {eps : alpha} {N n : Nat}
    (hc :
      forall n m : Nat,
        N <= n ->
          N <= m ->
            (F C).lt
              (IsOrderedFieldBaseLike.abs (F C)
                ((F C).sub (u n) (u m))) eps)
    (hn : N <= n) :
    (F C).lt (u n) ((F C).add (u N) eps) := by
  have hclose : (F C).lt
      (IsOrderedFieldBaseLike.abs (F C) ((F C).sub (u n) (u N))) eps :=
    hc n N hn (Nat.le_refl N)
  exact IsOrderedFieldBaseLike.abs_sub_lt_right (F C) hclose

/-- The eventual lower bounds form a nonempty set: for a Cauchy index `N` at
tolerance one, `u N - 1` is one. Together with the upper bound below, this
is what makes `exists_lub` applicable. -/
theorem eventual_lower_nonempty_of_cauchy {u : Nat -> alpha}
    (hu : (F C).SeqCauchy u) :
    Exists (EventualLowerBound C u) := by
  cases hu (F C).one (IsOrderedFieldBaseLike.zero_lt_one (F C)) with
  | intro N hN =>
      refine Exists.intro ((F C).sub (u N) (F C).one) ?_
      refine Exists.intro N ?_
      intro n hn
      exact IsOrderedFieldBaseLike.le_of_lt (F C)
        (cauchy_tail_center_lower C hN hn)

/-- The eventual lower bounds are bounded above, by `u N + 1` for a Cauchy
index `N` at tolerance one: each of them sits below some common late term,
and the Cauchy condition keeps late terms within one of `u N`. -/
theorem eventual_lower_bounded_above_of_cauchy {u : Nat -> alpha}
    (hu : (F C).SeqCauchy u) :
    Exists (IsUpperBound (F C).le (EventualLowerBound C u)) := by
  cases hu (F C).one (IsOrderedFieldBaseLike.zero_lt_one (F C)) with
  | intro N hN =>
      refine Exists.intro ((F C).add (u N) (F C).one) ?_
      intro x hx
      cases hx with
      | intro M hM =>
          let K := Nat.max N M
          have hNK : N <= K := Nat.le_max_left N M
          have hMK : M <= K := Nat.le_max_right N M
          have hxK : (F C).le x (u K) := hM K hMK
          have hKupper : (F C).lt (u K) ((F C).add (u N) (F C).one) :=
            cauchy_tail_center_upper C (n := K) hN hNK
          exact (F C).le_trans hxK
            (IsOrderedFieldBaseLike.le_of_lt (F C) hKupper)

/-- The same membership at an arbitrary tolerance: for a Cauchy index at
`eps`, the lower edge `u N - eps` of the tail band is an eventual lower
bound, and so bounds the supremum from below. Together with the lemma below
it traps the limit candidate inside the band. -/
theorem tail_center_lower_mem {u : Nat -> alpha}
    {eps : alpha} {N : Nat}
    (hc :
      forall n m : Nat,
        N <= n ->
          N <= m ->
            (F C).lt
              (IsOrderedFieldBaseLike.abs (F C)
                ((F C).sub (u n) (u m))) eps) :
    EventualLowerBound C u ((F C).sub (u N) eps) := by
  refine Exists.intro N ?_
  intro n hn
  exact IsOrderedFieldBaseLike.le_of_lt (F C)
    (cauchy_tail_center_lower C (n := n) hc hn)

/-- Its upper partner: `u N + eps` is an upper bound of all eventual lower
bounds, so the supremum stays below it. -/
theorem tail_center_upper_bound {u : Nat -> alpha}
    {eps : alpha} {N : Nat}
    (hc :
      forall n m : Nat,
        N <= n ->
          N <= m ->
            (F C).lt
              (IsOrderedFieldBaseLike.abs (F C)
                ((F C).sub (u n) (u m))) eps) :
    IsUpperBound (F C).le (EventualLowerBound C u)
      ((F C).add (u N) eps) := by
  intro x hx
  cases hx with
  | intro M hM =>
      let K := Nat.max N M
      have hNK : N <= K := Nat.le_max_left N M
      have hMK : M <= K := Nat.le_max_right N M
      have hxK : (F C).le x (u K) := hM K hMK
      have hKupper : (F C).lt (u K) ((F C).add (u N) eps) :=
        cauchy_tail_center_upper C (n := K) hc hNK
      exact (F C).le_trans hxK
        (IsOrderedFieldBaseLike.le_of_lt (F C) hKupper)

/-- The limit of the Cauchy sequence, before convergence is proved: the
least upper bound of the eventual lower bounds. For a Cauchy sequence this
is the one point all tail bands must agree on, and the convergence proof
below verifies that it is. -/
noncomputable def limitCandidate {u : Nat -> alpha}
    (hu : (F C).SeqCauchy u) : alpha :=
  Classical.choose
    (C.exists_lub (EventualLowerBound C u)
      (eventual_lower_nonempty_of_cauchy C hu)
      (eventual_lower_bounded_above_of_cauchy C hu))

theorem limitCandidate_is_lub {u : Nat -> alpha}
    (hu : (F C).SeqCauchy u) :
    IsLeastUpperBound (F C).le
      (EventualLowerBound C u) (limitCandidate C hu) :=
  Classical.choose_spec
    (C.exists_lub (EventualLowerBound C u)
      (eventual_lower_nonempty_of_cauchy C hu)
      (eventual_lower_bounded_above_of_cauchy C hu))

/-- The convergence: at `eps`, run the Cauchy condition at half of it. The
candidate then sits between `u N - eps / 2`, a member, and `u N + eps / 2`,
an upper bound, while the tail sits in the same band; the halving is what
collapses the two into `s - eps < u n < s + eps`. -/
theorem limitCandidate_tendsto {u : Nat -> alpha}
    (hu : (F C).SeqCauchy u) :
    (F C).SeqTendsto u (limitCandidate C hu) := by
  intro eps heps
  let d := IsOrderedFieldBaseLike.half (F C) eps
  have hd : (F C).lt (F C).zero d :=
    IsOrderedFieldBaseLike.half_pos (F C) heps
  cases hu d hd with
  | intro N hN =>
      refine Exists.intro N ?_
      intro n hn
      let s := limitCandidate C hu
      have hs : IsLeastUpperBound (F C).le
          (EventualLowerBound C u) s :=
        limitCandidate_is_lub C hu
      have hlower_mem : EventualLowerBound C u ((F C).sub (u N) d) :=
        tail_center_lower_mem C hN
      have hlower_le_s : (F C).le ((F C).sub (u N) d) s :=
        IsOrderedFieldBaseLike.le_lub_of_mem (F C) hs hlower_mem
      have hupper_bound : IsUpperBound (F C).le
          (EventualLowerBound C u) ((F C).add (u N) d) :=
        tail_center_upper_bound C hN
      have hs_le_upper : (F C).le s ((F C).add (u N) d) :=
        IsOrderedFieldBaseLike.lub_le_of_upper (F C) hs hupper_bound
      have hcenter_close : (F C).lt
          (IsOrderedFieldBaseLike.abs (F C)
            ((F C).sub (u N) (u n))) d :=
        hN N n (Nat.le_refl N) hn
      have hcenter_lt_n_add :
          (F C).lt (u N) ((F C).add (u n) d) :=
        IsOrderedFieldBaseLike.abs_sub_lt_right (F C) hcenter_close
      have hupper_lt_n_eps :
          (F C).lt ((F C).add (u N) d) ((F C).add (u n) eps) := by
        have h := (F C).add_lt_add_right hcenter_lt_n_add d
        have hright :
            (F C).add ((F C).add (u n) d) d =
              (F C).add (u n) eps := by
          unfold d
          exact IsOrderedFieldBaseLike.add_half_add_half (F C) (u n) eps
        rwa [hright] at h
      have hs_lt_n_eps :
          (F C).lt s ((F C).add (u n) eps) :=
        IsOrderedFieldBaseLike.lt_of_le_of_lt (F C)
          hs_le_upper hupper_lt_n_eps
      have hsdiff_lt :
          (F C).lt ((F C).sub s (u n)) eps :=
        IsOrderedFieldBaseLike.sub_lt_of_lt_add (F C) hs_lt_n_eps
      have hleft : (F C).lt ((F C).sub s eps) (u n) :=
        IsOrderedFieldBaseLike.sub_lt_of_lt_right (F C) hsdiff_lt
      have hn_upper_center :
          (F C).lt (u n) ((F C).add (u N) d) :=
        cauchy_tail_center_upper C (n := n) hN hn
      have hcenter_le_s_eps :
          (F C).le ((F C).add (u N) d) ((F C).add s eps) := by
        have h := (F C).add_le_add_right hlower_le_s eps
        have hleft_eq :
            (F C).add ((F C).sub (u N) d) eps =
              (F C).add (u N) d := by
          unfold d
          exact IsOrderedFieldBaseLike.sub_half_add_self (F C) (u N) eps
        rwa [hleft_eq] at h
      have hright : (F C).lt (u n) ((F C).add s eps) :=
        IsOrderedFieldBaseLike.lt_of_lt_of_le (F C)
          hn_upper_center hcenter_le_s_eps
      exact IsOrderedFieldBaseLike.abs_sub_lt_of_bounds (F C)
        hleft hright

/-- The third entry of the graph: from the supremum property alone, the
Cauchy-criterion node. Of the three entries this one has to work hardest --
no limit is available to aim at, so one is manufactured as the supremum of
the eventual lower bounds and then chased through the tail bands. -/
theorem cauchyCriterion :
    (F C).CauchyCriterionPrinciple where
  converges := by
    intro u hu
    exact Exists.intro (limitCandidate C hu)
      (limitCandidate_tendsto C hu)

end FromSupCauchy

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
