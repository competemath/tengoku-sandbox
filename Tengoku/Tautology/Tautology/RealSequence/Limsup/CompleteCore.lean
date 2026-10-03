import Tengoku.Tautology.Tautology.RealSequence.Basic
import Tengoku.Tautology.Tautology.RealBootstrap.Supremum

/-!
# Constructing limsup and liminf

The construction half of the upper and lower limits: the tail suprema
`tailSup N`, the tail infima `tailInf N`, and then `limsup` as the infimum of
the tail suprema and `liminf` as the supremum of the tail infima, each with the
specification lemma that identifies it.

Despite the name, the file is not uniformly at complete-field level. Its first
declaration, `TailValues`, is ordered-field vocabulary; the boundary runs
through the file by namespace, not around it. Completeness is spent at exactly
four points, the `Classical.choose` inside each of the four definitions --
`exists_lub` for `tailSup` and `liminf`, `exists_glb` for `tailInf` and
`limsup`. Everything else here, the nonemptiness and boundedness lemmas, uses
only boundedness of the sequence.

One hypothesis is easy to misread. `limsup` requires the sequence to be bounded
*below*, not above: the lower bound is what keeps the family of tail suprema
bounded below so that its infimum exists. `liminf` mirrors it. These are
existence conditions for the construction, not part of what limsup means --
the meaning lives in the predicates of `Tautology.RealSequence.Limsup`.

## Position and role

Implementation module, consumed only by `Tautology.RealSequence.Limsup` and
`Tautology.RealSequence.LimsupMul`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}

/-- The values of `u` from index `N` onwards. The only definition of
this module that stays below completeness -- pure ordered-field
vocabulary, which the rest of the module exists to take suprema and
infima of. -/
def TailValues (u : Nat -> alpha) (N : Nat) : alpha -> Prop :=
  fun x : alpha => Exists (fun n : Nat => And (N <= n) (x = u n))

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

theorem tailValues_nonempty (u : Nat -> alpha) (N : Nat) :
    Exists (IsOrderedFieldBaseLike.TailValues u N) :=
  Exists.intro (u N)
    (Exists.intro N (And.intro (Nat.le_refl N) rfl))

theorem tailValues_bddAbove {u : Nat -> alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (N : Nat) :
    Exists
      (IsUpperBound C.field.le
        (IsOrderedFieldBaseLike.TailValues u N)) := by
  cases hAbove with
  | intro B hB =>
      refine Exists.intro B ?_
      intro x hx
      cases hx with
      | intro n hn =>
          rw [hn.right]
          exact hB n

theorem tailValues_bddBelow {u : Nat -> alpha}
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat) :
    Exists
      (IsLowerBound C.field.le
        (IsOrderedFieldBaseLike.TailValues u N)) := by
  cases hBelow with
  | intro B hB =>
      refine Exists.intro B ?_
      intro x hx
      cases hx with
      | intro n hn =>
          rw [hn.right]
          exact hB n

/-- The supremum of the `N`-th tail of `u`, and the module's first use of
Dedekind completeness: the value is read off `C.exists_lub`, the wrapper of
`Tautology.RealBootstrap.Supremum` around the completeness field of `C`. It
exists because an upper bound for the whole sequence bounds every tail. -/
noncomputable def tailSup
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (N : Nat) : alpha :=
  Classical.choose
    (C.exists_lub
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailValues_nonempty u N)
      (tailValues_bddAbove C hAbove N))

/-- The specification of `tailSup`: a least upper bound of the `N`-th tail, in
the `IsLeastUpperBound` sense of `Tautology.Foundation.OrderField`. Consumers
go through this lemma, never through the choice hidden in the definition. -/
theorem tailSup_is_lub
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (N : Nat) :
    IsLeastUpperBound C.field.le
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailSup C u hAbove N) :=
  Classical.choose_spec
    (C.exists_lub
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailValues_nonempty u N)
      (tailValues_bddAbove C hAbove N))

/-- The infimum of the `N`-th tail, the mirror construction, read off
`C.exists_glb` -- itself a derived interface, since
`Tautology.RealBootstrap.Supremum` produces greatest lower bounds by taking a
supremum of the lower bounds. -/
noncomputable def tailInf
    (u : Nat -> alpha)
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat) : alpha :=
  Classical.choose
    (C.exists_glb
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailValues_nonempty u N)
      (tailValues_bddBelow C hBelow N))

/-- The specification of `tailInf`: a greatest lower bound of the `N`-th
tail. -/
theorem tailInf_is_glb
    (u : Nat -> alpha)
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat) :
    IsGreatestLowerBound C.field.le
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailInf C u hBelow N) :=
  Classical.choose_spec
    (C.exists_glb
      (IsOrderedFieldBaseLike.TailValues u N)
      (tailValues_nonempty u N)
      (tailValues_bddBelow C hBelow N))

/-- The family of all tail suprema of `u`. Shrinking the tail can only lower
its supremum (`tailSup_mono` of `Tautology.RealSequence.LimsupMul`), so the
limsup is naturally a greatest lower bound of this family. -/
def TailSupValues
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u) : alpha -> Prop :=
  fun x : alpha => Exists (fun N : Nat => x = tailSup C u hAbove N)

/-- The family of all tail infima of `u`, whose least upper bound is the
liminf. -/
def TailInfValues
    (u : Nat -> alpha)
    (hBelow : C.field.SeqBoundedBelow u) : alpha -> Prop :=
  fun x : alpha => Exists (fun N : Nat => x = tailInf C u hBelow N)

theorem tailSupValues_nonempty
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u) :
    Exists (TailSupValues C u hAbove) :=
  Exists.intro (tailSup C u hAbove 0) (Exists.intro 0 rfl)

theorem tailInfValues_nonempty
    (u : Nat -> alpha)
    (hBelow : C.field.SeqBoundedBelow u) :
    Exists (TailInfValues C u hBelow) :=
  Exists.intro (tailInf C u hBelow 0) (Exists.intro 0 rfl)

/-- A lower bound for the whole sequence is a lower bound for every tail
supremum, each of which dominates a term of the sequence. This is the step
that makes the limsup below need `SeqBoundedBelow`: without it the family of
tail suprema would have no lower bound, and no greatest lower bound. -/
theorem tailSupValues_bddBelow
    {u : Nat -> alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    Exists (IsLowerBound C.field.le (TailSupValues C u hAbove)) := by
  cases hBelow with
  | intro B hB =>
      refine Exists.intro B ?_
      intro x hx
      cases hx with
      | intro N hN =>
          rw [hN]
          have hmem :
              IsOrderedFieldBaseLike.TailValues u N (u N) :=
            Exists.intro N (And.intro (Nat.le_refl N) rfl)
          have hle_tail :
              C.field.le (u N) (tailSup C u hAbove N) :=
            IsOrderedFieldBaseLike.le_lub_of_mem C.field
              (tailSup_is_lub C u hAbove N) hmem
          exact C.field.le_trans (hB N) hle_tail

/-- The mirrored step: an upper bound for the sequence bounds every tail
infimum from above, which is why the liminf needs `SeqBoundedAbove`. -/
theorem tailInfValues_bddAbove
    {u : Nat -> alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    Exists (IsUpperBound C.field.le (TailInfValues C u hBelow)) := by
  cases hAbove with
  | intro B hB =>
      refine Exists.intro B ?_
      intro x hx
      cases hx with
      | intro N hN =>
          rw [hN]
          have hmem :
              IsOrderedFieldBaseLike.TailValues u N (u N) :=
            Exists.intro N (And.intro (Nat.le_refl N) rfl)
          have htail_le :
              C.field.le (tailInf C u hBelow N) (u N) :=
            IsOrderedFieldBaseLike.glb_le_of_mem C.field
              (tailInf_is_glb C u hBelow N) hmem
          exact C.field.le_trans htail_le (hB N)

/-- The limit superior of a two-sided bounded sequence: the greatest lower
bound of the family of tail suprema, read off `C.exists_glb`. The `hBelow`
argument is not decoration -- it reaches the definition only through
`tailSupValues_bddBelow`, and is what makes the value exist; once the value
exists, everything downstream runs on the bound-free predicate `IsLimsup`
of `Tautology.RealSequence.Limsup`. -/
noncomputable def limsup
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) : alpha :=
  Classical.choose
    (C.exists_glb
      (TailSupValues C u hAbove)
      (tailSupValues_nonempty C u hAbove)
      (tailSupValues_bddBelow C hAbove hBelow))

/-- The specification of `limsup`: a greatest lower bound of the family of
tail suprema. The form everything downstream consumes; the epsilonic
characterization is derived from it in `Tautology.RealSequence.Limsup`. -/
theorem limsup_is_glb
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    IsGreatestLowerBound C.field.le
      (TailSupValues C u hAbove)
      (limsup C u hAbove hBelow) :=
  Classical.choose_spec
    (C.exists_glb
      (TailSupValues C u hAbove)
      (tailSupValues_nonempty C u hAbove)
      (tailSupValues_bddBelow C hAbove hBelow))

/-- The limit inferior of a two-sided bounded sequence: the least upper
bound of the family of tail infima. Here it is `hAbove` that makes the value
exist, by bounding that family from above through
`tailInfValues_bddAbove`. -/
noncomputable def liminf
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) : alpha :=
  Classical.choose
    (C.exists_lub
      (TailInfValues C u hBelow)
      (tailInfValues_nonempty C u hBelow)
      (tailInfValues_bddAbove C hAbove hBelow))

/-- The specification of `liminf`: a least upper bound of the family of
tail infima. -/
theorem liminf_is_lub
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    IsLeastUpperBound C.field.le
      (TailInfValues C u hBelow)
      (liminf C u hAbove hBelow) :=
  Classical.choose_spec
    (C.exists_lub
      (TailInfValues C u hBelow)
      (tailInfValues_nonempty C u hBelow)
      (tailInfValues_bddAbove C hAbove hBelow))

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
