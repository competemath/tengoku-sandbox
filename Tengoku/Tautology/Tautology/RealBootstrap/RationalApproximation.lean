import Tengoku.Tautology.Tautology.RealBootstrap.Abs
import Tengoku.Tautology.Tautology.RealBootstrap.RationalDensity

/-!
# Approximating a point by an internal rational

Three convenience forms of density: a rational in the gap above a point, one in
the gap below, and one within a given absolute-value tolerance. The last is the
shape approximation arguments upstream want, since they are written with `abs`.

Nothing is proved here that `Tautology.RealBootstrap.RationalDensity` does not
already give; the file exists so that the common phrasings are named once.

## Position and role

Implementation module at complete-field level.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

theorem exists_internalRat_between_self_add {x eps : alpha}
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun q : alpha =>
      And (IsOrderedFieldBaseLike.InternalRat C.field q)
        (And (C.field.lt x q)
          (C.field.lt q (C.field.add x eps)))) := by
  have hx_lt : C.field.lt x (C.field.add x eps) := by
    have h := IsOrderedFieldBaseLike.add_lt_add_left C.field heps x
    rwa [C.field.add_zero] at h
  exact exists_internalRat_between C hx_lt

theorem exists_internalRat_between_sub_self {x eps : alpha}
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun q : alpha =>
      And (IsOrderedFieldBaseLike.InternalRat C.field q)
        (And (C.field.lt (C.field.sub x eps) q)
          (C.field.lt q x))) := by
  have hx_lt : C.field.lt (C.field.sub x eps) x :=
    IsOrderedFieldBaseLike.sub_lt_self_of_pos C.field heps
  exact exists_internalRat_between C hx_lt

/-- An internal rational within absolute-value distance `eps` of `x`, the
two-sided form that approximation arguments written with `abs` consume. The
witness is produced on one side only, above `x`, where the absolute value
unfolds to the plain difference. -/
theorem exists_internalRat_abs_sub_lt {x eps : alpha}
    (heps : C.field.lt C.field.zero eps) :
    Exists (fun q : alpha =>
      And (IsOrderedFieldBaseLike.InternalRat C.field q)
        (C.field.lt
          (IsOrderedFieldBaseLike.abs C.field (C.field.sub q x))
          eps)) := by
  cases exists_internalRat_between_self_add C (x := x) heps with
  | intro q hq =>
      have hsub_pos :
          C.field.lt C.field.zero (C.field.sub q x) :=
        IsOrderedFieldBaseLike.sub_pos_of_lt C.field hq.right.left
      have hsub_lt :
          C.field.lt (C.field.sub q x) eps :=
        IsOrderedFieldBaseLike.sub_lt_of_lt_add C.field hq.right.right
      have habs :
          IsOrderedFieldBaseLike.abs C.field (C.field.sub q x) =
            C.field.sub q x :=
        IsOrderedFieldBaseLike.abs_of_nonneg C.field
          (IsOrderedFieldBaseLike.le_of_lt C.field hsub_pos)
      exact Exists.intro q (And.intro hq.left (by rwa [habs]))

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
