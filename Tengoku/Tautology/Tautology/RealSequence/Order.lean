import Tengoku.Tautology.Tautology.RealSequence.Algebra

/-!
# Between absolute values and two-sided bounds

The translation layer of the region: three pointwise lemmas turning
`|x - a| < eps` into the two inequalities it stands for and back, and on top of
them the order facts about limits -- an eventual inequality passes to the
limit, and the squeeze theorem.

Small file, heavily used: those three pointwise lemmas are quoted about fifty
times each across some thirty files, since every argument that unfolds a limit
estimate goes through them.

## Position and role

Implementation module over an arbitrary ordered field; completeness plays no
part.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- The lower half of the translation from absolute-value closeness to plain
inequalities: `|x - a| < eps` implies `a - eps < x`. Stated for points, not
sequences, so that a convergence hypothesis can be peeled one index at a
time. -/
theorem abs_sub_lt_left {x a eps : alpha}
    (h : F.lt (abs F (F.sub x a)) eps) :
    F.lt (F.sub a eps) x := by
  exact sub_lt_of_lt_right F
    (sub_lt_of_lt_add F (lt_left_add_of_abs_sub_lt F h))

/-- The upper half of the same translation: `|x - a| < eps` implies
`x < a + eps`. With `abs_sub_lt_left` it delimits the `eps`-window around
`a`. -/
theorem abs_sub_lt_right {x a eps : alpha}
    (h : F.lt (abs F (F.sub x a)) eps) :
    F.lt x (F.add a eps) :=
  lt_right_add_of_abs_sub_lt F h

/-- The converse direction of the translation: a two-sided inequality at
distance `eps` gives `|x - a| < eps`. This is the closing shape of squeeze
arguments, reassembled from the two halves. -/
theorem abs_sub_lt_of_bounds {x a eps : alpha}
    (hleft : F.lt (F.sub a eps) x)
    (hright : F.lt x (F.add a eps)) :
    F.lt (abs F (F.sub x a)) eps :=
  abs_sub_lt_of_two_sided_sub_lt F
    (sub_lt_of_lt_add F hright)
    (sub_lt_of_sub_lt_left F hleft)

/-- Limits respect eventual inequalities: if `u n <= v n` from some index
on and both sequences converge, then `a <= b`. Eventual dominance is enough,
and the proof contradicts a strict gap `b < a` at half its size; order-based
limit arguments throughout the library reduce to this theorem.
-/
theorem seqTendsto_le_of_eventually_le {u v : Nat -> alpha} {a b : alpha}
    (hu : SeqTendsto F u a)
    (hv : SeqTendsto F v b)
    (huv : Eventually (fun n : Nat => F.le (u n) (v n))) :
    F.le a b := by
  by_cases hab : F.le a b
  · exact hab
  · have hba_le : F.le b a := by
      cases F.le_total b a with
      | inl hba => exact hba
      | inr hab' => exact False.elim (hab hab')
    have hba : F.lt b a :=
      lt_of_le_of_not_le F hba_le hab
    have hgap : F.lt F.zero (F.sub a b) :=
      sub_pos_of_lt F hba
    let eps := half F (F.sub a b)
    have heps : F.lt F.zero eps :=
      half_pos F hgap
    have hu_eps := hu eps heps
    have hv_eps := hv eps heps
    cases Eventually.and (Eventually.and hu_eps hv_eps) huv with
    | intro N hN =>
        have hN' := hN N (Nat.le_refl N)
        have hu_close := hN'.left.left
        have hv_close := hN'.left.right
        have huvN := hN'.right
        have hlow : F.lt (F.sub a eps) (u N) :=
          abs_sub_lt_left F hu_close
        have hmid_left : F.lt (F.sub a eps) (v N) :=
          lt_of_lt_of_le F hlow huvN
        have hhigh : F.lt (v N) (F.add b eps) :=
          abs_sub_lt_right F hv_close
        have hbad : F.lt (F.sub a eps) (F.add b eps) :=
          lt_trans F hmid_left hhigh
        have hmid :
            F.add b eps = F.sub a eps := by
          exact add_half_sub_eq_sub_half F a b
        rw [hmid] at hbad
        exact False.elim ((lt_irrefl F (F.sub a eps)) hbad)

/-- An eventually nonnegative sequence has a nonnegative limit: the
preceding theorem against the constant zero sequence. Eventual suffices,
which is what lets tail behaviour alone settle sign questions. -/
theorem seqTendsto_nonneg_of_eventually_nonneg {u : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (hnonneg : Eventually (fun n : Nat => F.le F.zero (u n))) :
    F.le F.zero a :=
  seqTendsto_le_of_eventually_le F
    (seqTendsto_const F F.zero) hu hnonneg

/-- The squeeze theorem: a sequence trapped eventually between two sequences
converging to the same limit converges to that limit. No hypothesis is made
on the trapped sequence itself; the proof pins it inside the `eps`-window of
the common limit using both outer convergences and closes with
`abs_sub_lt_of_bounds`. -/
theorem seqTendsto_of_squeeze {u v w : Nat -> alpha} {a : alpha}
    (hu : SeqTendsto F u a)
    (hw : SeqTendsto F w a)
    (huv : Eventually (fun n : Nat => F.le (u n) (v n)))
    (hvw : Eventually (fun n : Nat => F.le (v n) (w n))) :
    SeqTendsto F v a := by
  intro eps heps
  have hu_eps := hu eps heps
  have hw_eps := hw eps heps
  have hE := Eventually.and (Eventually.and hu_eps hw_eps)
    (Eventually.and huv hvw)
  apply Eventually.mono ?_ hE
  intro n hn
  have hu_close := hn.left.left
  have hw_close := hn.left.right
  have huvN := hn.right.left
  have hvwN := hn.right.right
  have hleft_u : F.lt (F.sub a eps) (u n) :=
    abs_sub_lt_left F hu_close
  have hleft_v : F.lt (F.sub a eps) (v n) :=
    lt_of_lt_of_le F hleft_u huvN
  have hright_w : F.lt (w n) (F.add a eps) :=
    abs_sub_lt_right F hw_close
  have hright_v : F.lt (v n) (F.add a eps) :=
    lt_of_le_of_lt F hvwN hright_w
  exact abs_sub_lt_of_bounds F hleft_v hright_v

end IsOrderedFieldBaseLike
end Tautology
