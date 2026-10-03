import Tengoku.Tautology.Tautology.Nat.Least
import Tengoku.Tautology.Tautology.RealBootstrap.Archimedean
import Tengoku.Tautology.Tautology.RealBootstrap.InternalRat

/-!
# Between any two points there is an internal rational

Density, and the ceiling statement it rests on. Given a positive gap, the
Archimedean property supplies a denominator fine enough that some multiple of
`1 / n` lands inside; the least such multiple is found with `Nat.least`, which
is why the file reaches down to `Tautology.Nat.Least` for a search principle
rather than using a minimisation argument of its own.

Two declarations only, but they are what makes the rationals usable as a
countable skeleton of the line: the countable interval basis of
`Tautology.RealTopology.RationalBasis`, and hence the Lindelöf property and the
upper cardinality bound, all pass through this file.

## Position and role

Implementation module at complete-field level -- it consumes the Archimedean
property derived in `Tautology.RealBootstrap.Archimedean`.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
variable (C : IsDedekindCompleteOrderedFieldBaseLike alpha)

/-- Every element is topped by an internal integer within one unit: some z
with a < z <= a + 1. The proof shifts by a natural exceeding `-a`, which is
where completeness enters through `exists_nat_gt`, and takes the least
natural above the shift before shifting back. -/
theorem exists_internalInt_ceiling (a : alpha) :
    Exists (fun z : alpha =>
      And (IsOrderedFieldBaseLike.InternalInt C.field z)
        (And (C.field.le z (C.field.add a C.field.one))
          (C.field.lt a z))) := by
  classical
  let F := C.field
  let nat := IsOrderedFieldBaseLike.nat F
  cases exists_nat_gt C (F.neg a) with
  | intro N hNeg =>
      let nN := nat N
      let shift := F.add a nN
      have hShiftPos : F.lt F.zero shift := by
        have h := IsOrderedFieldBaseLike.add_lt_add_right F hNeg a
        change F.lt (F.add (F.neg a) a) (F.add nN a) at h
        rwa [F.neg_add, F.add_comm nN a] at h
      have hAbove : Exists (fun k : Nat => F.lt shift (nat k)) :=
        exists_nat_gt C shift
      let p : Nat -> Prop := fun k => F.lt shift (nat k)
      let K := Tautology.Nat.least p hAbove
      have hK : p K := Tautology.Nat.least_spec p hAbove
      have hKmin : forall k : Nat, p k -> K <= k := by
        intro k hk
        exact Tautology.Nat.least_min p hAbove hk
      have hKne : Not (K = 0) := by
        intro hK0
        have hbad : F.lt shift F.zero := by
          have hK' := hK
          change F.lt shift (nat K) at hK'
          rw [hK0] at hK'
          change F.lt shift (IsOrderedFieldBaseLike.nat F 0) at hK'
          rwa [IsOrderedFieldBaseLike.nat_zero F] at hK'
        exact (IsOrderedFieldBaseLike.lt_asymm F hShiftPos) hbad
      have hKpos : 0 < K := Nat.pos_of_ne_zero hKne
      let k : Nat := K - 1
      have hk_succ : k + 1 = K := by
        dsimp [k]
        omega
      let z := F.sub (nat K) nN
      have hprev_not : Not (p k) := by
        intro hk
        have hmin := hKmin k hk
        dsimp [k] at hmin
        omega
      have hprev_le_shift : F.le (nat k) shift := by
        by_cases hle : F.le (nat k) shift
        · exact hle
        · cases F.le_total shift (nat k) with
          | inl hshift =>
              have hlt : p k :=
                IsOrderedFieldBaseLike.lt_of_le_of_not_le F
                  hshift hle
              exact False.elim (hprev_not hlt)
          | inr hle' =>
              exact hle'
      have hz_int : IsOrderedFieldBaseLike.InternalInt F z := by
        dsimp [z]
        refine Exists.intro (nat K) ?_
        refine Exists.intro nN ?_
        exact And.intro
          (IsOrderedFieldBaseLike.internalNat_of_nat F K)
          (And.intro
            (IsOrderedFieldBaseLike.internalNat_of_nat F N)
            rfl)
      have hshift_sub :
          F.add shift (F.neg nN) = a := by
        change F.add (F.add a nN) (F.neg nN) = a
        exact IsOrderedFieldBaseLike.add_neg_cancel_right F a nN
      have ha_lt_z : F.lt a z := by
        have h := IsOrderedFieldBaseLike.add_lt_add_right F hK
          (F.neg nN)
        change F.lt (F.add shift (F.neg nN))
          (F.add (nat K) (F.neg nN)) at h
        rwa [
          hshift_sub,
          <- F.sub_eq_add_neg (nat K) nN
        ] at h
      have hz_le_a1 : F.le z (F.add a F.one) := by
        have hprev_sub : F.le (F.sub (nat k) nN) a := by
          have h := F.add_le_add_right hprev_le_shift (F.neg nN)
          change F.le (F.add (nat k) (F.neg nN))
            (F.add shift (F.neg nN)) at h
          rwa [
            hshift_sub,
            <- F.sub_eq_add_neg (nat k) nN
          ] at h
        have hprev_sub_one :
            F.le (F.add (F.sub (nat k) nN) F.one)
              (F.add a F.one) :=
          F.add_le_add_right hprev_sub F.one
        have hleft :
            z = F.add (F.sub (nat k) nN) F.one := by
          dsimp [z]
          calc
            F.sub (nat K) nN =
                F.sub (nat (k + 1)) nN := by
                  rw [hk_succ]
            _ = F.add (nat (k + 1)) (F.neg nN) := by
                  rw [F.sub_eq_add_neg]
            _ = F.add
                  (F.add (IsOrderedFieldBaseLike.nat F k) F.one)
                  (F.neg nN) := by
                  change
                    F.add (IsOrderedFieldBaseLike.nat F (k + 1))
                      (F.neg nN) =
                    F.add
                      (F.add (IsOrderedFieldBaseLike.nat F k) F.one)
                      (F.neg nN)
                  rw [IsOrderedFieldBaseLike.nat_succ F k]
            _ = F.add (nat k) (F.add F.one (F.neg nN)) := by
                  rw [F.add_assoc]
            _ = F.add (nat k) (F.add (F.neg nN) F.one) := by
                  rw [F.add_comm F.one (F.neg nN)]
            _ = F.add (F.add (nat k) (F.neg nN)) F.one := by
                  rw [<- F.add_assoc]
            _ = F.add (F.sub (nat k) nN) F.one := by
                  rw [F.sub_eq_add_neg]
        rwa [hleft]
      refine Exists.intro z ?_
      exact And.intro hz_int (And.intro hz_le_a1 ha_lt_z)

/-- Between any two field elements lies an internal rational. The proof
picks n with `1 < n * (y - x)`, scales the interval by n, takes the ceiling
of the scaled left endpoint and divides it back by n. -/
theorem exists_internalRat_between {x y : alpha}
    (hxy : C.field.lt x y) :
    Exists (fun q : alpha =>
      And (IsOrderedFieldBaseLike.InternalRat C.field q)
        (And (C.field.lt x q) (C.field.lt q y))) := by
  let F := C.field
  let nat := IsOrderedFieldBaseLike.nat F
  have hdelta : F.lt F.zero (F.sub y x) :=
    IsOrderedFieldBaseLike.sub_pos_of_lt F hxy
  cases exists_nat_pos_mul_gt_one C hdelta with
  | intro n hgap =>
      have hn_ne : Not (n = 0) := by
        intro hn0
        subst hn0
        have hbad : F.lt F.one F.zero := by
          change F.lt F.one (F.mul (nat 0) (F.sub y x)) at hgap
          change F.lt F.one
            (F.mul (IsOrderedFieldBaseLike.nat F 0) (F.sub y x)) at hgap
          rwa [
            IsOrderedFieldBaseLike.nat_zero F,
            IsOrderedFieldBaseLike.zero_mul F
          ] at hgap
        exact
          (IsOrderedFieldBaseLike.lt_asymm F
            (IsOrderedFieldBaseLike.zero_lt_one F)) hbad
      let nval := nat n
      let a := F.mul nval x
      have hn_pos : F.lt F.zero nval :=
        IsOrderedFieldBaseLike.nat_pos_of_ne_zero F hn_ne
      have hn_nat_ne : Not (nval = F.zero) :=
        IsOrderedFieldBaseLike.nat_ne_zero_of_ne_zero F hn_ne
      have hinv_pos : F.lt F.zero (F.inv nval) :=
        IsOrderedFieldBaseLike.inv_pos F hn_pos
      cases exists_internalInt_ceiling C a with
      | intro z hz =>
          let q := F.mul z (F.inv nval)
          have hq_rat : IsOrderedFieldBaseLike.InternalRat F q := by
            dsimp [q]
            refine Exists.intro z ?_
            refine Exists.intro nval ?_
            exact And.intro hz.left
              (And.intro
                (IsOrderedFieldBaseLike.internalNat_of_nat F n)
                (And.intro hn_nat_ne rfl))
          have hxq : F.lt x q := by
            have hmul :=
              IsOrderedFieldBaseLike.mul_lt_mul_pos_right F
                hz.right.right hinv_pos
            have hleft :
                F.mul a (F.inv nval) = x := by
              dsimp [a]
              calc
                F.mul (F.mul nval x) (F.inv nval) =
                    F.mul (F.mul x nval) (F.inv nval) := by
                      rw [F.mul_comm nval x]
                _ = x :=
                  IsOrderedFieldBaseLike.mul_mul_inv_cancel_right
                    F x hn_nat_ne
            change F.lt (F.mul a (F.inv nval)) q at hmul
            rwa [hleft] at hmul
          have hqy : F.lt q y := by
            have hgap' : F.lt (F.add a F.one) (F.mul nval y) := by
              have h :=
                IsOrderedFieldBaseLike.add_lt_add_left F hgap a
              have hright :
                  F.add a (F.mul nval (F.sub y x)) =
                    F.mul nval y := by
                dsimp [a]
                rw [IsOrderedFieldBaseLike.mul_sub_eq_mul_sub F nval y x]
                rw [F.add_comm (F.mul nval x)
                  (F.sub (F.mul nval y) (F.mul nval x))]
                exact
                  IsOrderedFieldBaseLike.sub_add_cancel F
                    (F.mul nval y) (F.mul nval x)
              change F.lt (F.add a F.one)
                (F.add a (F.mul nval (F.sub y x))) at h
              rwa [hright] at h
            have hz_lt_ny : F.lt z (F.mul nval y) :=
              IsOrderedFieldBaseLike.lt_of_le_of_lt F hz.right.left hgap'
            have hmul :=
              IsOrderedFieldBaseLike.mul_lt_mul_pos_right F
                hz_lt_ny hinv_pos
            have hright :
                F.mul (F.mul nval y) (F.inv nval) = y := by
              calc
                F.mul (F.mul nval y) (F.inv nval) =
                    F.mul (F.mul y nval) (F.inv nval) := by
                      rw [F.mul_comm nval y]
                _ = y :=
                  IsOrderedFieldBaseLike.mul_mul_inv_cancel_right
                    F y hn_nat_ne
            change F.lt q (F.mul (F.mul nval y) (F.inv nval)) at hmul
            rwa [hright] at hmul
          refine Exists.intro q ?_
          exact And.intro hq_rat (And.intro hxq hqy)

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
