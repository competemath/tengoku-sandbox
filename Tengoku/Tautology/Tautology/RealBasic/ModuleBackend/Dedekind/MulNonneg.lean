module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Sign
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Rat

/-!
# Multiplication, nonnegative case first

Multiplication of two nonnegative cuts: a rational belongs to the product
when it is negative, or a product of nonnegative members of each factor.

**Multiplication has to be defined in the nonnegative case first, and this is
the file that does it.** The pointwise recipe that works for addition fails
here -- products of members of two arbitrary cuts do not form a downward
closed set, because multiplying by a negative reverses the order. Restricting
to nonnegatives makes the recipe correct, and `Dedekind.Mul` then extends it
by sign analysis. The clause "or the rational is negative" is what keeps the
member set downward closed at the bottom.

This staging is the main reason the Dedekind backend needs twenty-one files
while its order and its completeness together take one, `Dedekind.Order`.

## Position in the development

Above `Dedekind.Sign`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

/-- The positive part of the member description of a product: `q` lies below
a product `a * b` of members of `x` and `y`, both strictly positive. Kept as
a separate predicate so that `mulNonneg` can adjoin the negative rationals
around it. -/
def posMulMem (x y : Cut) (q : Rat) : Prop :=
  Exists (fun a => And (x.mem a) (And (0 < a)
    (Exists (fun b => And (y.mem b) (And (0 < b) (q < a * b))))))

/-- Product of two nonnegative cuts: a rational belongs when it is negative
or when `posMulMem x y` holds. The `q < 0` disjunct supplies the members when
a factor is zero and there are no positive products to name. -/
def mulNonneg (x y : Cut) (h0x : 0 <= x) (h0y : 0 <= y) : Cut where
  mem q := Or (q < 0) (posMulMem x y q)
  nonempty :=
    Exists.intro (0 - 1)
      (Or.inl (Tautology.RealBasic.ModuleBackend.Rat.sub_one_lt 0))
  proper := by
    cases x.proper with
    | intro ux hux =>
        cases y.proper with
        | intro uy huy =>
            refine Exists.intro (ux * uy) ?_
            intro hq
            cases hq with
            | inl hlt0 =>
                have hux0 : 0 <= ux := Cut.nonneg_of_nonneg_cut_not_mem h0x hux
                have huy0 : 0 <= uy := Cut.nonneg_of_nonneg_cut_not_mem h0y huy
                have hmul0 : 0 <= ux * uy := _root_.Rat.mul_nonneg hux0 huy0
                exact _root_.Rat.lt_irrefl
                  (Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le hlt0 hmul0)
            | inr hpos =>
                cases hpos with
                | intro a ha =>
                    cases ha.right.right with
                    | intro b hb =>
                        have haux : a <= ux := Cut.le_of_mem_of_not_mem ha.left hux
                        have hbuy : b <= uy := Cut.le_of_mem_of_not_mem hb.left huy
                        have huxpos : 0 < ux :=
                          Cut.pos_of_pos_mem_of_not_mem ha.left ha.right.left hux
                        have hab_bound : a * b <= ux * uy :=
                          Tautology.RealBasic.ModuleBackend.Rat.mul_le_mul_of_le_of_le_of_pos_of_pos
                            haux hbuy hb.right.left huxpos
                        exact _root_.Rat.lt_irrefl
                          (Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le
                            hb.right.right hab_bound)
  downward := by
    intro p q hpq hq
    cases hq with
    | inl hq0 =>
        exact Or.inl (Tautology.RealBasic.ModuleBackend.Rat.lt_trans hpq hq0)
    | inr hpos =>
        cases hpos with
        | intro a ha =>
            cases ha.right.right with
            | intro b hb =>
                exact Or.inr
                  (Exists.intro a
                    (And.intro ha.left
                      (And.intro ha.right.left
                        (Exists.intro b
                          (And.intro hb.left
                            (And.intro hb.right.left
                              (Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                hpq hb.right.right)))))))
  no_greatest := by
    intro q hq
    cases hq with
    | inl hq0 =>
        cases Tautology.RealBasic.ModuleBackend.Rat.exists_between hq0 with
        | intro r hr =>
            exact Exists.intro r (And.intro (Or.inl hr.right) hr.left)
    | inr hpos =>
        cases hpos with
        | intro a ha =>
            cases ha.right.right with
            | intro b hb =>
                cases Tautology.RealBasic.ModuleBackend.Rat.exists_between
                    hb.right.right with
                | intro r hr =>
                    exact Exists.intro r
                      (And.intro
                        (Or.inr
                          (Exists.intro a
                            (And.intro ha.left
                              (And.intro ha.right.left
                                (Exists.intro b
                                  (And.intro hb.left
                                    (And.intro hb.right.left hr.right)))))))
                        hr.left)

/-- The product cut does not depend on which nonnegativity proofs are passed
to it: its member description mentions only `x` and `y`. Sign-reduction
proofs in later files rewrite a product through `mul_of_nonneg_of_nonneg`
with whatever nonnegativity derivations they have at hand, and this lemma
reconciles the resulting terms. -/
theorem mulNonneg_proof_irrel (x y : Cut)
    (h0x h0x' : 0 <= x) (h0y h0y' : 0 <= y) :
    mulNonneg x y h0x h0y = mulNonneg x y h0x' h0y' := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    exact hq
  · intro hq
    exact hq

theorem posMulMem_comm {x y : Cut} {q : Rat} :
    posMulMem x y q -> posMulMem y x q := by
  intro hq
  cases hq with
  | intro a ha =>
      cases ha.right.right with
      | intro b hb =>
          have hqba : q < b * a := by
            rw [_root_.Rat.mul_comm]
            exact hb.right.right
          exact Exists.intro b
            (And.intro hb.left
              (And.intro hb.right.left
                (Exists.intro a
                  (And.intro ha.left
                    (And.intro ha.right.left hqba)))))

theorem mulNonneg_comm (x y : Cut) (h0x : 0 <= x) (h0y : 0 <= y) :
    mulNonneg x y h0x h0y = mulNonneg y x h0y h0x := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 => exact Or.inl hq0
    | inr hpos => exact Or.inr (posMulMem_comm hpos)
  · intro hq
    cases hq with
    | inl hq0 => exact Or.inl hq0
    | inr hpos => exact Or.inr (posMulMem_comm hpos)

theorem zero_le_mulNonneg (x y : Cut) (h0x : 0 <= x) (h0y : 0 <= y) :
    0 <= mulNonneg x y h0x h0y := by
  intro q hq0
  exact Or.inl ((Cut.mem_zero (q := q)).mp hq0)

theorem mulNonneg_zero_left (y : Cut) (h0y : 0 <= y) :
    mulNonneg 0 y (Cut.le_refl 0) h0y = 0 := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact (Cut.mem_zero (q := q)).mpr hq0
    | inr hpos =>
        cases hpos with
        | intro a ha =>
            have ha0 : a < 0 := (Cut.mem_zero (q := a)).mp ha.left
            exact False.elim
              (_root_.Rat.lt_irrefl
                (Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                  ha.right.left ha0))
  · intro hq0
    exact Or.inl ((Cut.mem_zero (q := q)).mp hq0)

theorem mulNonneg_one_left (x : Cut) (h0x : 0 <= x) :
    mulNonneg 1 x Cut.zero_le_one h0x = x := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact h0x q ((Cut.mem_zero (q := q)).mpr hq0)
    | inr hpos =>
        cases hpos with
        | intro a ha =>
            cases ha.right.right with
            | intro b hb =>
                have ha1 : a < 1 := (Cut.mem_one (q := a)).mp ha.left
                have hab_lt_b : a * b < b :=
                  Tautology.RealBasic.ModuleBackend.Rat.mul_lt_of_lt_one_of_pos
                    ha1 hb.right.left
                exact x.downward
                  (Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                    hb.right.right hab_lt_b)
                  hb.left
  · intro hxq
    by_cases hq0 : q < 0
    · exact Or.inl hq0
    · have h0q : 0 <= q := _root_.Rat.not_lt.mp hq0
      cases x.no_greatest hxq with
      | intro r hr =>
          have h0r : 0 < r :=
            Tautology.RealBasic.ModuleBackend.Rat.lt_of_le_of_lt h0q hr.right
          cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_one_mul_gt
              h0q hr.right with
          | intro a ha =>
              exact Or.inr
                (Exists.intro a
                  (And.intro ((Cut.mem_one (q := a)).mpr ha.right.left)
                    (And.intro ha.left
                      (Exists.intro r
                        (And.intro hr.left
                          (And.intro h0r ha.right.right))))))

theorem mulNonneg_one_right (x : Cut) (h0x : 0 <= x) :
    mulNonneg x 1 h0x Cut.zero_le_one = x := by
  rw [mulNonneg_comm x 1 h0x Cut.zero_le_one]
  exact mulNonneg_one_left x h0x

/-- Associativity for nonnegative factors, proved by double member inclusion:
each direction takes a product of members and re-splits it around a rational
chosen strictly between the target and a product. This is where the work of
associativity actually lives; `Dedekind.MulAssoc` reduces the general case to
it. -/
theorem mulNonneg_assoc (x y z : Cut) (h0x : 0 <= x) (h0y : 0 <= y) (h0z : 0 <= z) :
    mulNonneg (mulNonneg x y h0x h0y) z
        (zero_le_mulNonneg x y h0x h0y) h0z =
      mulNonneg x (mulNonneg y z h0y h0z) h0x
        (zero_le_mulNonneg y z h0y h0z) := by
  apply Cut.ext
  intro q
  constructor
  · intro hq
    cases hq with
    | inl hq0 =>
        exact Or.inl hq0
    | inr hpos =>
        by_cases hq0 : q < 0
        · exact Or.inl hq0
        · have h0q : 0 <= q := _root_.Rat.not_lt.mp hq0
          cases hpos with
          | intro p hp =>
              cases hp.right.right with
              | intro c hc =>
                  have hpxy : posMulMem x y p := by
                    cases hp.left with
                    | inl hp0 =>
                        exact False.elim
                          (_root_.Rat.lt_irrefl
                            (Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                              hp.right.left hp0))
                    | inr hpxy =>
                        exact hpxy
                  cases hpxy with
                  | intro a ha =>
                      cases ha.right.right with
                      | intro b hb =>
                          have hpabc : p * c < (a * b) * c :=
                            _root_.Rat.mul_lt_mul_of_pos_right
                              (a := p) (b := a * b) (c := c)
                              hb.right.right hc.right.left
                          have hqabc : q < a * (b * c) := by
                            have hqabc' : q < (a * b) * c :=
                              Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                hc.right.right hpabc
                            rw [_root_.Rat.mul_assoc] at hqabc'
                            exact hqabc'
                          cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_of_lt_mul_left
                              (q := q) (a := a) (t := b * c)
                              h0q ha.right.left hqabc with
                          | intro d hd =>
                              have hdyz : (mulNonneg y z h0y h0z).mem d :=
                                Or.inr
                                  (Exists.intro b
                                    (And.intro hb.left
                                      (And.intro hb.right.left
                                        (Exists.intro c
                                          (And.intro hc.left
                                            (And.intro hc.right.left
                                              hd.right.right))))))
                              exact Or.inr
                                (Exists.intro a
                                  (And.intro ha.left
                                    (And.intro ha.right.left
                                      (Exists.intro d
                                        (And.intro hdyz
                                          (And.intro hd.left
                                            hd.right.left))))))
  · intro hq
    cases hq with
    | inl hq0 =>
        exact Or.inl hq0
    | inr hpos =>
        by_cases hq0 : q < 0
        · exact Or.inl hq0
        · have h0q : 0 <= q := _root_.Rat.not_lt.mp hq0
          cases hpos with
          | intro a ha =>
              cases ha.right.right with
              | intro p hp =>
                  have hpyz : posMulMem y z p := by
                    cases hp.left with
                    | inl hp0 =>
                        exact False.elim
                          (_root_.Rat.lt_irrefl
                            (Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                              hp.right.left hp0))
                    | inr hpyz =>
                        exact hpyz
                  cases hpyz with
                  | intro b hb =>
                      cases hb.right.right with
                      | intro c hc =>
                          have hapbc : a * p < a * (b * c) :=
                            _root_.Rat.mul_lt_mul_of_pos_left
                              (a := p) (b := b * c) (c := a)
                              hc.right.right ha.right.left
                          have hqab_c : q < (a * b) * c := by
                            have hqabc : q < a * (b * c) :=
                              Tautology.RealBasic.ModuleBackend.Rat.lt_trans
                                hp.right.right hapbc
                            rw [← _root_.Rat.mul_assoc] at hqabc
                            exact hqabc
                          cases Tautology.RealBasic.ModuleBackend.Rat.exists_pos_lt_of_lt_mul_right
                              (q := q) (t := a * b) (c := c)
                              h0q hc.right.left hqab_c with
                          | intro d hd =>
                              have hdxy : (mulNonneg x y h0x h0y).mem d :=
                                Or.inr
                                  (Exists.intro a
                                    (And.intro ha.left
                                      (And.intro ha.right.left
                                        (Exists.intro b
                                          (And.intro hb.left
                                            (And.intro hb.right.left
                                              hd.right.right))))))
                              exact Or.inr
                                (Exists.intro d
                                  (And.intro hdxy
                                    (And.intro hd.left
                                      (Exists.intro c
                                        (And.intro hc.left
                                          (And.intro hc.right.left
                                            hd.right.left))))))

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
