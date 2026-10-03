module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.AddOrd
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.MulNonneg

/-!
# Distributivity, nonnegative case

Distributivity for nonnegative cuts, proved directly from the member
description of `Dedekind.MulNonneg` before any sign analysis is available.

The general case in `Dedekind.MulDistrib` is obtained from this one by cases,
so it has to come first -- the same staging as multiplication itself.

## Position in the development

Above `Dedekind.MulNonneg` and `Dedekind.AddOrd`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

/-- A rational `t` below a product `a * b` of members, with `a` strictly
positive, lies below some member of the product cut. When `b > 0` the witness
is a rational between `t` and the product; when `b <= 0` the product is
nonpositive and the negative clause of membership absorbs `t` instead. This
is the slack absorber on which the forward inclusion of distributivity runs. -/
theorem exists_lt_mem_mulNonneg_of_lt_mul {x y : Cut} {h0x : 0 <= x} {h0y : 0 <= y}
    {a b t : Rat} (hxa : x.mem a) (ha : 0 < a) (hyb : y.mem b)
    (ht : t < a * b) :
    Exists (fun p => And ((mulNonneg x y h0x h0y).mem p) (t < p)) := by
  by_cases hb : 0 < b
  · cases Tautology.RealBasic.ModuleBackend.Rat.exists_between ht with
    | intro p hp =>
        exact Exists.intro p
          (And.intro
            (Or.inr
              (Exists.intro a
                (And.intro hxa
                  (And.intro ha
                    (Exists.intro b
                      (And.intro hyb
                        (And.intro hb hp.right)))))))
            hp.left)
  · have hb0 : b <= 0 := _root_.Rat.not_lt.mp hb
    have hab0 : a * b <= 0 := by
      have h :=
        _root_.Rat.mul_le_mul_of_nonneg_left (a := b) (b := 0) (c := a)
          hb0 (_root_.Rat.le_of_lt ha)
      rw [_root_.Rat.mul_zero] at h
      exact h
    have ht0 : t < 0 :=
      Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le ht hab0
    cases Tautology.RealBasic.ModuleBackend.Rat.exists_between ht0 with
    | intro p hp =>
        exact Exists.intro p (And.intro (Or.inl hp.right) hp.left)

private theorem mem_add_of_lt_sum {y z : Cut} {b c s : Rat}
    (hyb : y.mem b) (hzc : z.mem c) (hs : s < b + c) :
    (y + z).mem s := by
  have hleft : s - c < b :=
    (_root_.Rat.sub_lt_iff (a := s) (b := b) (c := c)).mpr hs
  have heq : (s - c) + c = s := by
    rw [_root_.Rat.sub_eq_add_neg]
    rw [_root_.Rat.add_assoc]
    rw [_root_.Rat.neg_add_cancel]
    rw [_root_.Rat.add_zero]
  exact Exists.intro (s - c)
    (And.intro (y.downward hleft hyb)
      (Exists.intro c (And.intro hzc heq.symm)))

/-- A rational strictly below a member `b` of `y` belongs to `y + z`
whenever `z` is nonnegative: the slack `s - b` is negative, hence a member of
`z`, and `b + (s - b) = s`. -/
theorem mem_add_of_left_slack {y z : Cut} (h0z : 0 <= z) {b s : Rat}
    (hyb : y.mem b) (hsb : s < b) : (y + z).mem s := by
  have hdiff : s - b < 0 := by
    apply (_root_.Rat.sub_lt_iff (a := s) (b := 0) (c := b)).mpr
    rw [_root_.Rat.zero_add]
    exact hsb
  have hzc : z.mem (s - b) :=
    h0z (s - b) ((Cut.mem_zero (q := s - b)).mpr hdiff)
  have heq : b + (s - b) = s := by
    rw [_root_.Rat.sub_eq_add_neg]
    rw [_root_.Rat.add_comm s (-b)]
    rw [← _root_.Rat.add_assoc]
    rw [_root_.Rat.add_neg_cancel]
    rw [_root_.Rat.zero_add]
  exact Exists.intro b
    (And.intro hyb
      (Exists.intro (s - b) (And.intro hzc heq.symm)))

/-- The mirror of `mem_add_of_left_slack`: a rational strictly below a member
of `z` belongs to `y + z` whenever `y` is nonnegative. -/
theorem mem_add_of_right_slack {y z : Cut} (h0y : 0 <= y) {c s : Rat}
    (hzc : z.mem c) (hsc : s < c) : (y + z).mem s := by
  have hdiff : s - c < 0 := by
    apply (_root_.Rat.sub_lt_iff (a := s) (b := 0) (c := c)).mpr
    rw [_root_.Rat.zero_add]
    exact hsc
  have hyb : y.mem (s - c) :=
    h0y (s - c) ((Cut.mem_zero (q := s - c)).mpr hdiff)
  have heq : (s - c) + c = s := by
    rw [_root_.Rat.sub_eq_add_neg]
    rw [_root_.Rat.add_assoc]
    rw [_root_.Rat.neg_add_cancel]
    rw [_root_.Rat.add_zero]
  exact Exists.intro (s - c)
    (And.intro hyb
      (Exists.intro c (And.intro hzc heq.symm)))

/-- Distributivity on the left for nonnegative cuts. This is the double
member inclusion in which distributivity is actually proved: each direction
dismantles a sum of products and rebuilds it around a rational chosen
strictly in between, using the slack and density lemmas above. -/
theorem mulNonneg_add_left (x y z : Cut) (h0x : 0 <= x) (h0y : 0 <= y)
    (h0z : 0 <= z) :
    mulNonneg x (y + z) h0x (add_nonneg h0y h0z) =
      mulNonneg x y h0x h0y + mulNonneg x z h0x h0z := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    have h0xy : 0 <= mulNonneg x y h0x h0y := zero_le_mulNonneg x y h0x h0y
    have h0xz : 0 <= mulNonneg x z h0x h0z := zero_le_mulNonneg x z h0x h0z
    have h0rhs : 0 <= mulNonneg x y h0x h0y + mulNonneg x z h0x h0z :=
      add_nonneg h0xy h0xz
    cases hq with
    | inl hq0 =>
        exact h0rhs q ((Cut.mem_zero (q := q)).mpr hq0)
    | inr hpos =>
        cases hpos with
        | intro a ha =>
            cases ha.right.right with
            | intro s hs =>
                cases hs.left with
                | intro b hb =>
                    cases hb.right with
                    | intro c hc =>
                        have hqsum : q < a * b + a * c := by
                          have hqraw : q < a * (b + c) :=
                            by
                              rw [← hc.right]
                              exact hs.right.right
                          rw [_root_.Rat.mul_add] at hqraw
                          exact hqraw
                        have hleft_target : q - a * c < a * b :=
                          (_root_.Rat.sub_lt_iff
                            (a := q) (b := a * b) (c := a * c)).mpr
                            hqsum
                        cases exists_lt_mem_mulNonneg_of_lt_mul
                            (x := x) (y := y) (h0x := h0x) (h0y := h0y)
                            ha.left ha.right.left hb.left hleft_target with
                        | intro p hp =>
                            have hq_p_ac : q < p + a * c :=
                              (_root_.Rat.sub_lt_iff
                                (a := q) (b := p) (c := a * c)).mp
                                hp.right
                            have hq_sub_p : q - p < a * c := by
                              apply
                                (_root_.Rat.sub_lt_iff
                                  (a := q) (b := a * c) (c := p)).mpr
                              have hq_ac_p : q < a * c + p := by
                                rw [_root_.Rat.add_comm]
                                exact hq_p_ac
                              exact hq_ac_p
                            cases exists_lt_mem_mulNonneg_of_lt_mul
                                (x := x) (y := z) (h0x := h0x) (h0y := h0z)
                                ha.left ha.right.left hc.left hq_sub_p with
                            | intro r hr =>
                                have hrExact :
                                    (mulNonneg x z h0x h0z).mem (q - p) :=
                                  (mulNonneg x z h0x h0z).downward
                                    hr.right hr.left
                                have heq : p + (q - p) = q := by
                                  rw [_root_.Rat.sub_eq_add_neg]
                                  rw [_root_.Rat.add_comm q (-p)]
                                  rw [← _root_.Rat.add_assoc]
                                  rw [_root_.Rat.add_neg_cancel]
                                  rw [_root_.Rat.zero_add]
                                exact Exists.intro p
                                  (And.intro hp.left
                                    (Exists.intro (q - p)
                                      (And.intro hrExact heq.symm)))
  · intro hq
    cases hq with
    | intro p hp =>
        cases hp.right with
        | intro r hr =>
            by_cases hq0 : q < 0
            · exact Or.inl hq0
            · have h0q : 0 <= q := _root_.Rat.not_lt.mp hq0
              cases hp.left with
              | inl hp0 =>
                  cases hr.left with
                  | inl hr0 =>
                      have hprp : p + r < r := by
                        have h :=
                          (_root_.Rat.add_lt_add_right
                            (a := p) (b := 0) (c := r)).mpr hp0
                        rw [_root_.Rat.zero_add] at h
                        exact h
                      have hpr0 : p + r < 0 :=
                        Tautology.RealBasic.ModuleBackend.Rat.lt_trans hprp hr0
                      have hqneg : q < 0 := by
                        rw [hr.right]
                        exact hpr0
                      exact False.elim ((_root_.Rat.not_lt.mpr h0q) hqneg)
                  | inr hrpos =>
                      cases hrpos with
                      | intro a ha =>
                          cases ha.right.right with
                          | intro c hc =>
                              have hprr : p + r < r := by
                                have h :=
                                  (_root_.Rat.add_lt_add_right
                                    (a := p) (b := 0) (c := r)).mpr hp0
                                rw [_root_.Rat.zero_add] at h
                                exact h
                              have hqac : q < a * c :=
                                Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                  (by
                                    rw [hr.right]
                                    exact hprr)
                                  hc.right.right
                              cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_of_lt_mul_left
                                  (q := q) (a := a) (t := c) h0q ha.right.left hqac with
                              | intro s hs =>
                                  exact Or.inr
                                    (Exists.intro a
                                      (And.intro ha.left
                                        (And.intro ha.right.left
                                          (Exists.intro s
                                            (And.intro
                                              (mem_add_of_right_slack h0y hc.left
                                                hs.right.right)
                                              (And.intro hs.left hs.right.left))))))
              | inr hppos =>
                  cases hppos with
                  | intro a1 ha1 =>
                      cases ha1.right.right with
                      | intro b hb =>
                          cases hr.left with
                          | inl hr0 =>
                              have hprp : p + r < p := by
                                have h :=
                                  (_root_.Rat.add_lt_add_left
                                    (a := r) (b := 0) (c := p)).mpr hr0
                                rw [_root_.Rat.add_zero] at h
                                exact h
                              have hqab : q < a1 * b :=
                                Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                  (by
                                    rw [hr.right]
                                    exact hprp)
                                  hb.right.right
                              cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_of_lt_mul_left
                                  (q := q) (a := a1) (t := b) h0q
                                  ha1.right.left hqab with
                              | intro s hs =>
                                  exact Or.inr
                                    (Exists.intro a1
                                      (And.intro ha1.left
                                        (And.intro ha1.right.left
                                          (Exists.intro s
                                            (And.intro
                                              (mem_add_of_left_slack h0z hb.left
                                                hs.right.right)
                                              (And.intro hs.left hs.right.left))))))
                          | inr hrpos =>
                              cases hrpos with
                              | intro a2 ha2 =>
                                  cases ha2.right.right with
                                  | intro c hc =>
                                      cases Cut.exists_mem_gt_of_mem_of_mem
                                          ha1.left ha2.left with
                                      | intro a ha =>
                                          have h0a : 0 < a :=
                                            Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                              ha1.right.left ha.right.left
                                          have hpb : p < a * b := by
                                            have hmul : a1 * b < a * b :=
                                              _root_.Rat.mul_lt_mul_of_pos_right
                                                (a := a1) (b := a) (c := b)
                                                ha.right.left hb.right.left
                                            exact Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                              hb.right.right hmul
                                          have hrc : r < a * c := by
                                            have hmul : a2 * c < a * c :=
                                              _root_.Rat.mul_lt_mul_of_pos_right
                                                (a := a2) (b := a) (c := c)
                                                ha.right.right hc.right.left
                                            exact Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                              hc.right.right hmul
                                          have hpqsum : p + r < a * b + a * c :=
                                            Tautology.RealBasic.ModuleBackend.Rat.add_lt_add hpb hrc
                                          have hqsum : q < a * (b + c) := by
                                            have hqsum' : q < a * b + a * c :=
                                              by
                                                rw [hr.right]
                                                exact hpqsum
                                            rw [_root_.Rat.mul_add]
                                            exact hqsum'
                                          cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_of_lt_mul_left
                                              (q := q) (a := a) (t := b + c)
                                              h0q h0a hqsum with
                                          | intro s hs =>
                                              exact Or.inr
                                                (Exists.intro a
                                                  (And.intro ha.left
                                                    (And.intro h0a
                                                      (Exists.intro s
                                                        (And.intro
                                                          (mem_add_of_lt_sum
                                                            hb.left hc.left
                                                            hs.right.right)
                                                          (And.intro hs.left
                                                            hs.right.left))))))

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
