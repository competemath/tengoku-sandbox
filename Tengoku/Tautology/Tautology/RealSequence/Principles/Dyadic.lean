import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealSequence.Principles.Statements

/-!
# The dyadic Archimedean principle

The form of the Archimedean property that bisection arguments want: that
`length / 2 ^ n` eventually drops below any positive bound. It is stated as its
own principle, so that an edge which needs it can take it as an explicit
hypothesis instead of reaching for completeness.

That distinction is the reason this file exists. The bisection edge
`Tautology.RealSequence.Principles.FromNestedMonotone` stays at ordered-field
level precisely because this hypothesis is handed to it; the complete-field
bundle can discharge it, and does so in
`Tautology.RealSequence.Principles.Selected`, but nothing forces an ordered
field to have it.

## Position and role

Support module. Consumed by the bisection edges here and, in `RealCompactness`,
by `Tautology.RealCompactness.ClosedInterval.FromNestedSequential` and
`Tautology.RealCompactness.ClosedInterval.FromNestedFinite`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The dyadic scale of the field: the powers of two, starting at one and
doubling at each step. The graph needs them as the scale on which the
Archimedean principle below is phrased, and the bisection machinery of the
nested-to-monotone edge measures its interval lengths against them. -/
def dyadic : Nat -> alpha
  | 0 => F.one
  | n + 1 => F.mul (dyadic n) (two F)

theorem dyadic_zero :
    dyadic F 0 = F.one :=
  rfl

theorem dyadic_succ (n : Nat) :
    dyadic F (n + 1) = F.mul (dyadic F n) (two F) :=
  rfl

theorem dyadic_succ_eq_add (n : Nat) :
    dyadic F (n + 1) = F.add (dyadic F n) (dyadic F n) := by
  rw [dyadic_succ]
  unfold two
  rw [F.mul_add, F.mul_one]

theorem dyadic_pos (n : Nat) :
    F.lt F.zero (dyadic F n) := by
  induction n with
  | zero =>
      rw [dyadic_zero]
      exact zero_lt_one F
  | succ n ih =>
      rw [dyadic_succ]
      exact mul_pos F ih (zero_lt_two F)

theorem dyadic_ne_zero (n : Nat) :
    Not (dyadic F n = F.zero) := by
  intro h
  exact ne_of_lt F (dyadic_pos F n) h.symm

theorem one_le_dyadic (n : Nat) :
    F.le F.one (dyadic F n) := by
  induction n with
  | zero =>
      rw [dyadic_zero]
      exact F.le_refl F.one
  | succ n ih =>
      have h0 : F.le F.zero (dyadic F n) :=
        le_of_lt F (dyadic_pos F n)
      have hle_self_add :
          F.le (dyadic F n) (F.add (dyadic F n) (dyadic F n)) := by
        have h := add_le_add_left F h0 (dyadic F n)
        rwa [F.add_zero] at h
      exact F.le_trans ih (by
        rwa [<- dyadic_succ_eq_add F n] at hle_self_add)

/-- Every embedded natural number is bounded by its own dyadic power.
Provable by induction at ordered-field level, this is the bridge that turns
"some embedded natural exceeds `x`" into "some dyadic power exceeds `x`" in
`exists_dyadic_gt` below, and it is the only bridge the file needs between
the two scales. -/
theorem nat_le_dyadic (n : Nat) :
    F.le (nat F n) (dyadic F n) := by
  induction n with
  | zero =>
      rw [nat_zero, dyadic_zero]
      exact zero_le_one F
  | succ n ih =>
      rw [nat_succ, dyadic_succ_eq_add]
      exact add_le_add F ih (one_le_dyadic F n)

/-- An Archimedean principle phrased on the dyadic scale: dividing a
nonnegative `L` by the dyadic powers eventually lands below any positive
`eps`. Over a bare ordered field this is not provable -- it is exactly the
hypothesis the nested-to-monotone edge needs to drive its bisected lengths
to zero -- while `FromArchimedeanDyadic`, later in this file, derives it
from Dedekind completeness. -/
structure DyadicArchimedeanPrinciple : Prop where
  small_mul_inv :
    forall {L eps : alpha},
      F.le F.zero L ->
        F.lt F.zero eps ->
          Exists
            (fun n : Nat =>
              F.lt (F.mul L (F.inv (dyadic F n))) eps)

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

namespace FromArchimedeanDyadic

/-- The ordered-field reduct of `C`; the completeness of `C` enters only
through the two derivations that follow. -/
abbrev F : IsOrderedFieldBaseLike alpha :=
  C.field

/-- Above every field element sits a dyadic power. This is where completeness
enters the file: the natural Archimedean bound `exists_nat_gt` gives an
embedded natural beyond `x`, and `nat_le_dyadic` pushes the dyadic past
it. -/
theorem exists_dyadic_gt (x : alpha) :
    Exists (fun n : Nat => (F C).lt x (IsOrderedFieldBaseLike.dyadic (F C) n)) := by
  cases exists_nat_gt C x with
  | intro n hn =>
      refine Exists.intro n ?_
      exact IsOrderedFieldBaseLike.lt_of_lt_of_le (F C) hn
        (IsOrderedFieldBaseLike.nat_le_dyadic (F C) n)

/-- Converts unboundedness of the dyadics into smallness of their
reciprocals: a dyadic beyond `L / eps` exists, and cross-multiplying by the
positive `dyadic` and `eps` turns that into `L / dyadic < eps`. The
nonnegativity hypothesis is not used -- the argument works for any `L` -- but
it is kept so the statement matches the `small_mul_inv` field of
`DyadicArchimedeanPrinciple`. -/
theorem small_mul_inv {L eps : alpha}
    (_hL : (F C).le (F C).zero L)
    (heps : (F C).lt (F C).zero eps) :
    Exists
      (fun n : Nat =>
        (F C).lt
          ((F C).mul L
            ((F C).inv (IsOrderedFieldBaseLike.dyadic (F C) n)))
          eps) := by
  cases exists_dyadic_gt C ((F C).mul L ((F C).inv eps)) with
  | intro n hn =>
      let d := IsOrderedFieldBaseLike.dyadic (F C) n
      have hdpos : (F C).lt (F C).zero d :=
        IsOrderedFieldBaseLike.dyadic_pos (F C) n
      have hdne : Not (d = (F C).zero) :=
        IsOrderedFieldBaseLike.dyadic_ne_zero (F C) n
      have heps_ne : Not (eps = (F C).zero) := by
        intro h
        exact IsOrderedFieldBaseLike.ne_of_lt (F C) heps h.symm
      have hinv_eps_pos : (F C).lt (F C).zero ((F C).inv eps) :=
        IsOrderedFieldBaseLike.inv_pos (F C) heps
      have hmul_gt :
          (F C).lt L ((F C).mul d eps) := by
        have h := IsOrderedFieldBaseLike.mul_lt_mul_pos_right (F C) hn heps
        have hleft :
            (F C).mul ((F C).mul L ((F C).inv eps)) eps = L := by
          calc
            (F C).mul ((F C).mul L ((F C).inv eps)) eps =
                (F C).mul L ((F C).mul ((F C).inv eps) eps) := by
                  rw [(F C).mul_assoc]
            _ = (F C).mul L (F C).one := by
                  rw [(F C).inv_mul_cancel heps_ne]
            _ = L := by rw [(F C).mul_one]
        have hright :
            (F C).mul d eps = (F C).mul d eps := rfl
        rwa [hleft, hright] at h
      refine Exists.intro n ?_
      apply IsOrderedFieldBaseLike.lt_of_mul_lt_mul_pos_right (F C)
        (z := d) ?_ hdpos
      have hleft :
          (F C).mul
              ((F C).mul L ((F C).inv d)) d = L := by
        calc
          (F C).mul
              ((F C).mul L ((F C).inv d)) d =
              (F C).mul L ((F C).mul ((F C).inv d) d) := by
                rw [(F C).mul_assoc]
          _ = (F C).mul L (F C).one := by
                rw [(F C).inv_mul_cancel hdne]
          _ = L := by rw [(F C).mul_one]
      have hright :
          (F C).mul eps d = (F C).mul d eps := by
        rw [(F C).mul_comm eps d]
      rwa [hleft, hright]

/-- The dyadic Archimedean principle as a value over a Dedekind-complete
field, so that edges stated at ordered-field level can take it as a
hypothesis and be fed this by their callers. The compactness region consumes
it the same way, at its own selection point. -/
theorem dyadicArchimedean :
    (F C).DyadicArchimedeanPrinciple where
  small_mul_inv := by
    intro L eps hL heps
    exact small_mul_inv C hL heps

end FromArchimedeanDyadic

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
