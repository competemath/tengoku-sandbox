import Tengoku.Tautology.Tautology.RealBootstrap.OrderAlgebra
import Tengoku.Tautology.Tautology.RealBootstrap.InternalNat
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum

/-!
# The Archimedean property, in the forms the library actually uses

Two named principles rather than one theorem, because different arguments want
different shapes: `InvNatArchimedeanPrinciple`, that `1 / (n + 1)` eventually
drops below any positive bound, and `LinearArchimedeanPrinciple`, that some
multiple of a positive quantity passes any bound. Both are stated over an
arbitrary ordered field, as hypotheses that an argument can carry.

The complete-field half then *derives* both, from the fact that the embedded
naturals have no upper bound -- and that is where completeness is spent: were
they bounded, their least upper bound would be exceeded by a successor.

Stating the principles separately from their derivation is what lets modules
upstream stay at ordered-field level while still using them. Whole subtrees --
the bisection edges of the completeness route graph, the sequential
characterisation of closure in `Tautology.RealTopology.Sequential` -- take one
of these as an explicit hypothesis rather than reaching for completeness, and
the selection points discharge it once from the bundle.

## Position and role

Implementation module spanning both levels, built on
`Tautology.RealBootstrap.Supremum` and `Tautology.RealBootstrap.InternalNat`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The embedded naturals as a predicate on the field: x equals `nat F n` for
some external n. That this set has no upper bound is `natRange_unbounded`
below, and the Archimedean consequences of this file flow from that one. -/
def NatRange (x : alpha) : Prop :=
  Exists (fun n : Nat => x = nat F n)

theorem natRange_zero :
    NatRange F F.zero := by
  exact Exists.intro 0 rfl

theorem natRange_succ {x : alpha}
    (hx : NatRange F x) :
    NatRange F (F.add x F.one) := by
  cases hx with
  | intro n hn =>
      subst hn
      exact Exists.intro (n + 1) (by rw [nat_succ])

/-- The reciprocal Archimedean principle as a bundled proposition: for every
positive eps, some reciprocal `1 / (n + 1)` lies below it. The successor
form keeps the reciprocal of a positive natural. Bundled as a structure
rather than assumed of the field, since the project carries no typeclasses;
`invNatArchimedean` below supplies it for every complete field. -/
structure InvNatArchimedeanPrinciple : Prop where
  small_inv_succ :
    forall {eps : alpha},
      F.lt F.zero eps ->
        Exists
          (fun n : Nat =>
            F.lt (F.inv (nat F (n + 1))) eps)

/-- The linear Archimedean principle as a bundled proposition: multiples of a
positive eps eventually outgrow every nonnegative L. The nonnegativity
hypothesis matches the classical statement, though completeness in fact
renders it unnecessary; see `exists_nat_mul_gt` below. -/
structure LinearArchimedeanPrinciple : Prop where
  large_nat_mul :
    forall {L eps : alpha},
      F.le F.zero L ->
        F.lt F.zero eps ->
          Exists
            (fun n : Nat =>
              F.lt L (F.mul (nat F n) eps))

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- The embedded naturals have no upper bound. This is where Dedekind
completeness enters the Archimedean chain: were s a least upper bound of
`NatRange`, some `nat n` would exceed `s - 1`, and the successor
`nat (n + 1)` would exceed s itself, contradicting upper boundedness. -/
theorem natRange_unbounded :
    Not (Exists
      (IsUpperBound C.field.le
        (IsOrderedFieldBaseLike.NatRange C.field))) := by
  intro hbdd
  let S : alpha -> Prop := IsOrderedFieldBaseLike.NatRange C.field
  have hne : Exists S :=
    Exists.intro C.field.zero
      (IsOrderedFieldBaseLike.natRange_zero C.field)
  cases C.exists_lub S hne hbdd with
  | intro s hs =>
      have hsub : C.field.lt (C.field.sub s C.field.one) s :=
        IsOrderedFieldBaseLike.sub_lt_self_of_pos C.field
          (IsOrderedFieldBaseLike.zero_lt_one C.field)
      cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub C.field hs hsub with
      | intro y hy =>
          cases hy.left with
          | intro n hyn =>
              subst hyn
              have hsucc :
                  C.field.lt s
                    (IsOrderedFieldBaseLike.nat C.field (n + 1)) := by
                have h :=
                  IsOrderedFieldBaseLike.add_lt_add_right C.field
                    hy.right C.field.one
                rwa [
                  IsOrderedFieldBaseLike.sub_add_cancel C.field s C.field.one,
                  <- IsOrderedFieldBaseLike.nat_succ C.field n
                ] at h
              have hupper :
                  C.field.le
                    (IsOrderedFieldBaseLike.nat C.field (n + 1)) s :=
                hs.left
                  (IsOrderedFieldBaseLike.nat C.field (n + 1))
                  (Exists.intro (n + 1) rfl)
              exact
                (IsOrderedFieldBaseLike.not_le_of_lt C.field hsucc)
                  hupper

/-- Every element lies below some embedded natural, the Archimedean property
in the form the rest of the library quotes. An element above every natural
would upper-bound `NatRange`, which `natRange_unbounded` forbids. -/
theorem exists_nat_gt (x : alpha) :
    Exists (fun n : Nat =>
      C.field.lt x (IsOrderedFieldBaseLike.nat C.field n)) := by
  by_cases hex :
      Exists (fun n : Nat =>
        C.field.lt x (IsOrderedFieldBaseLike.nat C.field n))
  · exact hex
  · have hUpper :
        IsUpperBound C.field.le
          (IsOrderedFieldBaseLike.NatRange C.field) x := by
      intro y hy
      cases hy with
      | intro n hyn =>
          subst hyn
          by_cases hynx :
              C.field.le (IsOrderedFieldBaseLike.nat C.field n) x
          · exact hynx
          · cases C.field.le_total x
                (IsOrderedFieldBaseLike.nat C.field n) with
            | inl hxyn =>
                have hlt :
                    C.field.lt x
                      (IsOrderedFieldBaseLike.nat C.field n) :=
                  IsOrderedFieldBaseLike.lt_of_le_of_not_le C.field
                    hxyn hynx
                exact False.elim (hex (Exists.intro n hlt))
            | inr hynx' =>
                exact hynx'
    exact False.elim
      (natRange_unbounded C (Exists.intro x hUpper))

/-- Some multiple of a positive eps exceeds one, the unit-bound instance of
`exists_nat_mul_gt` kept as its own statement because it is the
denominator-choosing form `Tautology.RealBootstrap.RationalDensity` consumes:
an n with `1 < n * (y - x)` is a grid fine enough to place a rational inside
the gap. -/
theorem exists_nat_pos_mul_gt_one {eps : alpha}
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun n : Nat =>
      C.field.lt C.field.one
        (C.field.mul (IsOrderedFieldBaseLike.nat C.field n) eps)) := by
  cases exists_nat_gt C (C.field.inv eps) with
  | intro n hn =>
      have heps_ne : Not (eps = C.field.zero) := by
        intro h
        exact IsOrderedFieldBaseLike.ne_of_lt C.field heps h.symm
      have hmul :=
        IsOrderedFieldBaseLike.mul_lt_mul_pos_right C.field hn heps
      refine Exists.intro n ?_
      rwa [C.field.inv_mul_cancel heps_ne] at hmul

/-- Some reciprocal `1 / n` of a positive natural drops below eps, the
positivity of n carried as an explicit conjunct rather than folded into a
successor. This is the working shape inside the file:
`invNatArchimedean` repackages it into the `n + 1` form in which the
bundled `InvNatArchimedeanPrinciple` is stated. -/
theorem exists_inv_nat_lt {eps : alpha}
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun n : Nat =>
      And (Not (n = 0))
        (C.field.lt
          (C.field.inv (IsOrderedFieldBaseLike.nat C.field n))
          eps)) := by
  cases exists_nat_pos_mul_gt_one C heps with
  | intro n hn =>
      have hn_ne : Not (n = 0) := by
        intro hn0
        subst hn0
        have hbad : C.field.lt C.field.one C.field.zero := by
          rwa [
            IsOrderedFieldBaseLike.nat_zero C.field,
            IsOrderedFieldBaseLike.zero_mul C.field
          ] at hn
        exact
          (IsOrderedFieldBaseLike.lt_asymm C.field
            (IsOrderedFieldBaseLike.zero_lt_one C.field)) hbad
      have hn_pos :
          C.field.lt C.field.zero
            (IsOrderedFieldBaseLike.nat C.field n) :=
        IsOrderedFieldBaseLike.nat_pos_of_ne_zero C.field hn_ne
      have hn_nat_ne :
          Not (IsOrderedFieldBaseLike.nat C.field n = C.field.zero) :=
        IsOrderedFieldBaseLike.nat_ne_zero_of_ne_zero C.field hn_ne
      have hmul :
          C.field.lt
            (C.field.mul
              (IsOrderedFieldBaseLike.nat C.field n)
              (C.field.inv (IsOrderedFieldBaseLike.nat C.field n)))
            (C.field.mul
              (IsOrderedFieldBaseLike.nat C.field n) eps) := by
        rwa [<- C.field.mul_inv_cancel hn_nat_ne] at hn
      refine Exists.intro n ?_
      exact And.intro hn_ne
        (IsOrderedFieldBaseLike.lt_of_mul_lt_mul_pos_left C.field
          hmul hn_pos)

/-- Multiples of a positive eps outgrow any field element. The
nonnegativity hypothesis on L is unused: completeness delivers the
conclusion for all L at once, and the bundled
`LinearArchimedeanPrinciple` keeps the hypothesis only to match the
classical shape. -/
theorem exists_nat_mul_gt {L eps : alpha}
    (_hL : C.field.le C.field.zero L)
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun n : Nat =>
      C.field.lt L
        (C.field.mul (IsOrderedFieldBaseLike.nat C.field n) eps)) := by
  cases exists_nat_gt C (C.field.mul L (C.field.inv eps)) with
  | intro n hn =>
      have heps_ne : Not (eps = C.field.zero) := by
        intro h
        exact IsOrderedFieldBaseLike.ne_of_lt C.field heps h.symm
      have hmul :=
        IsOrderedFieldBaseLike.mul_lt_mul_pos_right C.field hn heps
      refine Exists.intro n ?_
      rwa [
        IsOrderedFieldBaseLike.mul_inv_mul_cancel_right C.field L heps_ne
      ] at hmul

theorem invNatArchimedean :
    C.field.InvNatArchimedeanPrinciple where
  small_inv_succ := by
    intro eps heps
    cases exists_inv_nat_lt C heps with
    | intro n hn =>
        cases n with
        | zero =>
            exact False.elim (hn.left rfl)
        | succ k =>
            exact Exists.intro k hn.right

theorem linearArchimedean :
    C.field.LinearArchimedeanPrinciple where
  large_nat_mul := by
    intro L eps hL heps
    exact exists_nat_mul_gt C hL heps

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
