import Tengoku.Tautology.Tautology.RealSequence.Limsup.CompleteCore
import Tengoku.Tautology.Tautology.RealSequence.Mul
import Tengoku.Tautology.Tautology.RealBootstrap.SupremumTools

/-!
# Upper and lower limits under multiplication

The two product estimates -- `limsup (u * v)` is at most the product of the
upper limits, and the product of the lower limits is at most `liminf (u * v)`
-- both under an eventual nonnegativity hypothesis, which is what keeps the
inequalities from flipping.

The proofs deliberately leave the epsilon characterisations of
`Tautology.RealSequence.Limsup` aside. Instead they show the sequence of tail
suprema converges to the upper limit and then apply ordinary limit algebra to
the product, which is why this module depends on `Tautology.RealSequence.Mul`.
Monotonicity of the tail suprema in the truncation index is the bridge.

## Position and role

Implementation module, the last of the limsup cluster. Completeness enters only
through the constructions it imports from
`Tautology.RealSequence.Limsup.CompleteCore`.
-/

namespace Tautology
namespace IsOrderedFieldBaseLike

variable {alpha : Type}
variable (F : IsOrderedFieldBaseLike alpha)

/-- `u` is nonnegative from some index on. The side condition under which the
product inequalities of this module hold: multiplication is monotone in each
factor only on the nonnegative side, which is where every proof below
consumes the two nonnegativity hypotheses. -/
def EventuallyNonnegative (u : Nat -> alpha) : Prop :=
  Eventually (fun n : Nat => F.le F.zero (u n))

end IsOrderedFieldBaseLike

namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Shrinking the tail can only lower its supremum: for `N <= M`, the
supremum over the smaller tail from `M` is at most the supremum over the
tail from `N`. One of the two halves from which the convergence of the tail
suprema is later read off. -/
theorem tailSup_mono {u : Nat -> alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    {N M : Nat}
    (hNM : N <= M) :
    C.field.le (tailSup C u hAbove M) (tailSup C u hAbove N) := by
  exact
    IsOrderedFieldBaseLike.lub_mono C.field
      (S := IsOrderedFieldBaseLike.TailValues u M)
      (T := IsOrderedFieldBaseLike.TailValues u N)
      (fun x hx =>
        match hx with
        | Exists.intro n hn =>
            Exists.intro n
              (And.intro (Nat.le_trans hNM hn.left) hn.right))
      (tailSup_is_lub C u hAbove M)
      (tailSup_is_lub C u hAbove N)

/-- Enlarging the cutoff can only raise the tail infimum -- the order
preserving mirror of `tailSup_mono`. -/
theorem tailInf_mono {u : Nat -> alpha}
    (hBelow : C.field.SeqBoundedBelow u)
    {N M : Nat}
    (hNM : N <= M) :
    C.field.le (tailInf C u hBelow N) (tailInf C u hBelow M) := by
  exact
    IsOrderedFieldBaseLike.glb_mono C.field
      (S := IsOrderedFieldBaseLike.TailValues u M)
      (T := IsOrderedFieldBaseLike.TailValues u N)
      (fun x hx =>
        match hx with
        | Exists.intro n hn =>
            Exists.intro n
              (And.intro (Nat.le_trans hNM hn.left) hn.right))
      (tailInf_is_glb C u hBelow M)
      (tailInf_is_glb C u hBelow N)

theorem limsup_le_tailSup
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat) :
    C.field.le (limsup C u hAbove hBelow)
      (tailSup C u hAbove N) :=
  (limsup_is_glb C u hAbove hBelow).left
    (tailSup C u hAbove N) (Exists.intro N rfl)

theorem tailInf_le_liminf
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat) :
    C.field.le (tailInf C u hBelow N)
      (liminf C u hAbove hBelow) :=
  (liminf_is_lub C u hAbove hBelow).left
    (tailInf C u hBelow N) (Exists.intro N rfl)

/-- The tail suprema converge to the limsup. The proof is monotone
convergence by hand from the greatest-lower-bound property: some tail
supremum eventually drops under `L + eps`, `tailSup_mono` pulls all later
ones down with it, and `limsup_le_tailSup` keeps every one above `L - eps`,
with no Archimedean assumption entering. It is the route by which limit
algebra reaches limsups in the two main theorems below. -/
theorem tailSup_tendsto_limsup
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.SeqTendsto
      (fun N : Nat => tailSup C u hAbove N)
      (limsup C u hAbove hBelow) := by
  let F := C.field
  intro eps heps
  let L := limsup C u hAbove hBelow
  have hLlt : F.lt L (F.add L eps) := by
    have h := IsOrderedFieldBaseLike.add_lt_add_left F heps L
    rwa [F.add_zero] at h
  cases IsOrderedFieldBaseLike.exists_gt_of_glb_lt F
      (limsup_is_glb C u hAbove hBelow) hLlt with
  | intro s hs =>
      cases hs.left with
      | intro N0 hN0 =>
          refine Exists.intro N0 ?_
          intro N hN
          have hlower_le :
              F.le L (tailSup C u hAbove N) :=
            limsup_le_tailSup C u hAbove hBelow N
          have hleft :
              F.lt (F.sub L eps) (tailSup C u hAbove N) :=
            IsOrderedFieldBaseLike.lt_of_lt_of_le F
              (IsOrderedFieldBaseLike.sub_lt_self_of_pos F heps)
              hlower_le
          have hmono :
              F.le (tailSup C u hAbove N)
                (tailSup C u hAbove N0) :=
            tailSup_mono C hAbove hN
          have hupper :
              F.lt (tailSup C u hAbove N) (F.add L eps) := by
            have htail_lt : F.lt (tailSup C u hAbove N0) (F.add L eps) := by
              have hsright := hs.right
              rwa [hN0] at hsright
            exact IsOrderedFieldBaseLike.lt_of_le_of_lt F hmono htail_lt
          exact IsOrderedFieldBaseLike.abs_sub_lt_of_bounds F hleft hupper

/-- The mirror convergence: the tail infima rise to the liminf, by the same
least-upper-bound bookkeeping with no Archimedean assumption. -/
theorem tailInf_tendsto_liminf
    (u : Nat -> alpha)
    (hAbove : C.field.SeqBoundedAbove u)
    (hBelow : C.field.SeqBoundedBelow u) :
    C.field.SeqTendsto
      (fun N : Nat => tailInf C u hBelow N)
      (liminf C u hAbove hBelow) := by
  let F := C.field
  intro eps heps
  let l := liminf C u hAbove hBelow
  have hsub_lt_l : F.lt (F.sub l eps) l :=
    IsOrderedFieldBaseLike.sub_lt_self_of_pos F heps
  cases IsOrderedFieldBaseLike.exists_lt_of_lt_lub F
      (liminf_is_lub C u hAbove hBelow) hsub_lt_l with
  | intro s hs =>
      cases hs.left with
      | intro N0 hN0 =>
          refine Exists.intro N0 ?_
          intro N hN
          have hmono :
              F.le (tailInf C u hBelow N0)
                (tailInf C u hBelow N) :=
            tailInf_mono C hBelow hN
          have hleft :
              F.lt (F.sub l eps) (tailInf C u hBelow N) := by
            have htail_lt : F.lt (F.sub l eps) (tailInf C u hBelow N0) := by
              have hsright := hs.right
              rwa [hN0] at hsright
            exact IsOrderedFieldBaseLike.lt_of_lt_of_le F htail_lt hmono
          have hupper_le :
              F.le (tailInf C u hBelow N) l :=
            tailInf_le_liminf C u hAbove hBelow N
          have hl_lt_add : F.lt l (F.add l eps) := by
            have h := IsOrderedFieldBaseLike.add_lt_add_left F heps l
            rwa [F.add_zero] at h
          have hupper :
              F.lt (tailInf C u hBelow N) (F.add l eps) :=
            IsOrderedFieldBaseLike.lt_of_le_of_lt F hupper_le hl_lt_add
          exact IsOrderedFieldBaseLike.abs_sub_lt_of_bounds F hleft hupper

theorem tailSup_nonneg_of_tail_nonneg
    {u : Nat -> alpha}
    (hAbove : C.field.SeqBoundedAbove u)
    (N : Nat)
    (hNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (u n)) :
    C.field.le C.field.zero (tailSup C u hAbove N) := by
  let F := C.field
  have hmem : IsOrderedFieldBaseLike.TailValues u N (u N) :=
    Exists.intro N (And.intro (Nat.le_refl N) rfl)
  have hu_le : F.le (u N) (tailSup C u hAbove N) :=
    IsOrderedFieldBaseLike.le_lub_of_mem F
      (tailSup_is_lub C u hAbove N) hmem
  exact F.le_trans (hNonneg N (Nat.le_refl N)) hu_le

theorem tailInf_nonneg_of_tail_nonneg
    {u : Nat -> alpha}
    (hBelow : C.field.SeqBoundedBelow u)
    (N : Nat)
    (hNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (u n)) :
    C.field.le C.field.zero (tailInf C u hBelow N) := by
  let F := C.field
  apply IsOrderedFieldBaseLike.le_glb_of_lower F
    (tailInf_is_glb C u hBelow N)
  intro x hx
  cases hx with
  | intro n hn =>
      rw [hn.right]
      exact hNonneg n hn.left

/-- With both tails nonnegative, the tail supremum of the pointwise product
is at most the product of the tail suprema. The proof is a pointwise
domination composed through the two monotone multiplications, one per
factor, and it is where the nonnegativity hypotheses are consumed. -/
theorem tailSup_mul_le_mul_tailSup_of_tail_nonneg
    {u v : Nat -> alpha}
    (hUAbove : C.field.SeqBoundedAbove u)
    (hVAbove : C.field.SeqBoundedAbove v)
    (hMulAbove :
      C.field.SeqBoundedAbove
        (fun n : Nat => C.field.mul (u n) (v n)))
    (N : Nat)
    (hUNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (u n))
    (hVNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (v n)) :
    C.field.le
      (tailSup C (fun n : Nat => C.field.mul (u n) (v n)) hMulAbove N)
      (C.field.mul (tailSup C u hUAbove N) (tailSup C v hVAbove N)) := by
  let F := C.field
  apply IsOrderedFieldBaseLike.lub_le_of_upper F
    (tailSup_is_lub C
      (fun n : Nat => F.mul (u n) (v n)) hMulAbove N)
  intro x hx
  cases hx with
  | intro n hn =>
      rw [hn.right]
      have hu_le : F.le (u n) (tailSup C u hUAbove N) :=
        IsOrderedFieldBaseLike.le_lub_of_mem F
          (tailSup_is_lub C u hUAbove N)
          (Exists.intro n (And.intro hn.left rfl))
      have hv_le : F.le (v n) (tailSup C v hVAbove N) :=
        IsOrderedFieldBaseLike.le_lub_of_mem F
          (tailSup_is_lub C v hVAbove N)
          (Exists.intro n (And.intro hn.left rfl))
      have hu_nonneg : F.le F.zero (u n) := hUNonneg n hn.left
      have hv_nonneg : F.le F.zero (v n) := hVNonneg n hn.left
      have hSu_nonneg : F.le F.zero (tailSup C u hUAbove N) :=
        F.le_trans hu_nonneg hu_le
      have hstep1 :
          F.le (F.mul (u n) (v n))
            (F.mul (tailSup C u hUAbove N) (v n)) :=
        IsOrderedFieldBaseLike.mul_le_mul_nonneg_right F hu_le hv_nonneg
      have hstep2 :
          F.le (F.mul (tailSup C u hUAbove N) (v n))
            (F.mul (tailSup C u hUAbove N) (tailSup C v hVAbove N)) :=
        IsOrderedFieldBaseLike.mul_le_mul_nonneg_left F hv_le hSu_nonneg
      exact F.le_trans hstep1 hstep2

/-- The mirror estimate on the liminf side: with nonnegative tails, the
product of the tail infima is at most the tail infimum of the pointwise
product. -/
theorem mul_tailInf_le_tailInf_mul_of_tail_nonneg
    {u v : Nat -> alpha}
    (hUBelow : C.field.SeqBoundedBelow u)
    (hVBelow : C.field.SeqBoundedBelow v)
    (hMulBelow :
      C.field.SeqBoundedBelow
        (fun n : Nat => C.field.mul (u n) (v n)))
    (N : Nat)
    (hUNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (u n))
    (hVNonneg : forall n : Nat, N <= n -> C.field.le C.field.zero (v n)) :
    C.field.le
      (C.field.mul (tailInf C u hUBelow N) (tailInf C v hVBelow N))
      (tailInf C (fun n : Nat => C.field.mul (u n) (v n)) hMulBelow N) := by
  let F := C.field
  apply IsOrderedFieldBaseLike.le_glb_of_lower F
    (tailInf_is_glb C
      (fun n : Nat => F.mul (u n) (v n)) hMulBelow N)
  intro x hx
  cases hx with
  | intro n hn =>
      rw [hn.right]
      have hIu_le : F.le (tailInf C u hUBelow N) (u n) :=
        IsOrderedFieldBaseLike.glb_le_of_mem F
          (tailInf_is_glb C u hUBelow N)
          (Exists.intro n (And.intro hn.left rfl))
      have hIv_le : F.le (tailInf C v hVBelow N) (v n) :=
        IsOrderedFieldBaseLike.glb_le_of_mem F
          (tailInf_is_glb C v hVBelow N)
          (Exists.intro n (And.intro hn.left rfl))
      have hu_nonneg : F.le F.zero (u n) := hUNonneg n hn.left
      have hIu_nonneg : F.le F.zero (tailInf C u hUBelow N) :=
        tailInf_nonneg_of_tail_nonneg C hUBelow N hUNonneg
      have hIv_nonneg : F.le F.zero (tailInf C v hVBelow N) :=
        tailInf_nonneg_of_tail_nonneg C hVBelow N hVNonneg
      have hstep1 :
          F.le (F.mul (tailInf C u hUBelow N) (tailInf C v hVBelow N))
            (F.mul (u n) (tailInf C v hVBelow N)) :=
        IsOrderedFieldBaseLike.mul_le_mul_nonneg_right F hIu_le hIv_nonneg
      have hstep2 :
          F.le (F.mul (u n) (tailInf C v hVBelow N))
            (F.mul (u n) (v n)) :=
        IsOrderedFieldBaseLike.mul_le_mul_nonneg_left F hIv_le hu_nonneg
      exact F.le_trans hstep1 hstep2

theorem eventually_tailSup_mul_le_mul_tailSup
    {u v : Nat -> alpha}
    (hUNonneg : C.field.EventuallyNonnegative u)
    (hVNonneg : C.field.EventuallyNonnegative v)
    (hUAbove : C.field.SeqBoundedAbove u)
    (hVAbove : C.field.SeqBoundedAbove v)
    (hMulAbove :
      C.field.SeqBoundedAbove
        (fun n : Nat => C.field.mul (u n) (v n))) :
    Eventually
      (fun N : Nat =>
        C.field.le
          (tailSup C
            (fun n : Nat => C.field.mul (u n) (v n)) hMulAbove N)
          (C.field.mul (tailSup C u hUAbove N)
            (tailSup C v hVAbove N))) := by
  cases hUNonneg with
  | intro Nu hNu =>
      cases hVNonneg with
      | intro Nv hNv =>
          refine Exists.intro (Nat.max Nu Nv) ?_
          intro N hN
          exact tailSup_mul_le_mul_tailSup_of_tail_nonneg C
            hUAbove hVAbove hMulAbove N
            (fun n hn =>
              hNu n
                (Nat.le_trans (Nat.le_trans (Nat.le_max_left Nu Nv) hN) hn))
            (fun n hn =>
              hNv n
                (Nat.le_trans (Nat.le_trans (Nat.le_max_right Nu Nv) hN) hn))

theorem eventually_mul_tailInf_le_tailInf_mul
    {u v : Nat -> alpha}
    (hUNonneg : C.field.EventuallyNonnegative u)
    (hVNonneg : C.field.EventuallyNonnegative v)
    (hUBelow : C.field.SeqBoundedBelow u)
    (hVBelow : C.field.SeqBoundedBelow v)
    (hMulBelow :
      C.field.SeqBoundedBelow
        (fun n : Nat => C.field.mul (u n) (v n))) :
    Eventually
      (fun N : Nat =>
        C.field.le
          (C.field.mul (tailInf C u hUBelow N)
            (tailInf C v hVBelow N))
          (tailInf C
            (fun n : Nat => C.field.mul (u n) (v n)) hMulBelow N)) := by
  cases hUNonneg with
  | intro Nu hNu =>
      cases hVNonneg with
      | intro Nv hNv =>
          refine Exists.intro (Nat.max Nu Nv) ?_
          intro N hN
          exact mul_tailInf_le_tailInf_mul_of_tail_nonneg C
            hUBelow hVBelow hMulBelow N
            (fun n hn =>
              hNu n
                (Nat.le_trans (Nat.le_trans (Nat.le_max_left Nu Nv) hN) hn))
            (fun n hn =>
              hNv n
                (Nat.le_trans (Nat.le_trans (Nat.le_max_right Nu Nv) hN) hn))

/-- Main theorem: for eventually nonnegative sequences, the limsup of the
pointwise product is at most the product of the limsups. The route runs by
convergence rather than by epsilons -- the three limsups become limits via
`tailSup_tendsto_limsup`, the two factor limits multiply by `seqTendsto_mul` of
`Tautology.RealSequence.Mul`, and `seqTendsto_le_of_eventually_le` of
`Tautology.RealSequence.Order` carries the eventual tail-level inequality to
the limit. -/
theorem limsup_mul_nonneg_le_mul_limsup
    {u v : Nat -> alpha}
    (hUNonneg : C.field.EventuallyNonnegative u)
    (hVNonneg : C.field.EventuallyNonnegative v)
    (hUAbove : C.field.SeqBoundedAbove u)
    (hUBelow : C.field.SeqBoundedBelow u)
    (hVAbove : C.field.SeqBoundedAbove v)
    (hVBelow : C.field.SeqBoundedBelow v)
    (hMulAbove :
      C.field.SeqBoundedAbove
        (fun n : Nat => C.field.mul (u n) (v n)))
    (hMulBelow :
      C.field.SeqBoundedBelow
        (fun n : Nat => C.field.mul (u n) (v n))) :
    C.field.le
      (limsup C
        (fun n : Nat => C.field.mul (u n) (v n)) hMulAbove hMulBelow)
      (C.field.mul (limsup C u hUAbove hUBelow)
        (limsup C v hVAbove hVBelow)) := by
  let F := C.field
  apply IsOrderedFieldBaseLike.seqTendsto_le_of_eventually_le F
  · exact tailSup_tendsto_limsup C
      (fun n : Nat => F.mul (u n) (v n)) hMulAbove hMulBelow
  · exact IsOrderedFieldBaseLike.seqTendsto_mul F
      (tailSup_tendsto_limsup C u hUAbove hUBelow)
      (tailSup_tendsto_limsup C v hVAbove hVBelow)
  · exact eventually_tailSup_mul_le_mul_tailSup C
      hUNonneg hVNonneg hUAbove hVAbove hMulAbove

/-- Main theorem on the liminf side: for eventually nonnegative sequences,
the product of the liminfs is at most the liminf of the pointwise product,
by the same convergence route through the tail infima. -/
theorem mul_liminf_le_liminf_mul_nonneg
    {u v : Nat -> alpha}
    (hUNonneg : C.field.EventuallyNonnegative u)
    (hVNonneg : C.field.EventuallyNonnegative v)
    (hUAbove : C.field.SeqBoundedAbove u)
    (hUBelow : C.field.SeqBoundedBelow u)
    (hVAbove : C.field.SeqBoundedAbove v)
    (hVBelow : C.field.SeqBoundedBelow v)
    (hMulAbove :
      C.field.SeqBoundedAbove
        (fun n : Nat => C.field.mul (u n) (v n)))
    (hMulBelow :
      C.field.SeqBoundedBelow
        (fun n : Nat => C.field.mul (u n) (v n))) :
    C.field.le
      (C.field.mul (liminf C u hUAbove hUBelow)
        (liminf C v hVAbove hVBelow))
      (liminf C
        (fun n : Nat => C.field.mul (u n) (v n)) hMulAbove hMulBelow) := by
  let F := C.field
  apply IsOrderedFieldBaseLike.seqTendsto_le_of_eventually_le F
  · exact IsOrderedFieldBaseLike.seqTendsto_mul F
      (tailInf_tendsto_liminf C u hUAbove hUBelow)
      (tailInf_tendsto_liminf C v hVAbove hVBelow)
  · exact tailInf_tendsto_liminf C
      (fun n : Nat => F.mul (u n) (v n)) hMulAbove hMulBelow
  · exact eventually_mul_tailInf_le_tailInf_mul C
      hUNonneg hVNonneg hUBelow hVBelow hMulBelow

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
