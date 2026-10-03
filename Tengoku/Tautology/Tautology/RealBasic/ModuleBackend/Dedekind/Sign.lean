module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Order
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Rat

/-!
# Positive, negative, zero

The trichotomy for cuts, and the predicates the multiplication files split on.

Isolating this before multiplication is what makes the case analysis below
manageable: `Dedekind.MulNonneg` can then assume nonnegativity as a hypothesis
rather than rediscovering the trichotomy inside every proof.

## Position in the development

Above `Dedekind.Order`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

theorem zero_le_one : (0 : Cut) <= 1 := by
  intro q hq0
  have hq0Rat : q < 0 := (Cut.mem_zero (q := q)).mp hq0
  have h01Rat : (0 : Rat) <= 1 := by decide
  exact (Cut.mem_one (q := q)).mpr
    (Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le hq0Rat h01Rat)

theorem zero_lt_one : (0 : Cut) < 1 := by
  apply lt_of_le_of_not_le
  · exact zero_le_one
  · intro h10
    have h0mem1 : (1 : Cut).mem 0 := (Cut.mem_one (q := 0)).mpr (by decide)
    have h0mem0 : (0 : Cut).mem 0 := h10 0 h0mem1
    have h00 : (0 : Rat) < 0 := (Cut.mem_zero (q := 0)).mp h0mem0
    exact _root_.Rat.lt_irrefl h00

theorem zero_ne_one : (0 : Cut) ≠ 1 := by
  intro h01
  have hlt : (1 : Cut) < 1 := by
    simpa [h01] using zero_lt_one
  exact Cut.lt_irrefl 1 hlt

theorem nonneg_of_nonneg_cut_not_mem {x : Cut} {u : Rat}
    (h0x : 0 <= x)
    (hu : Not (x.mem u)) :
    0 <= u := by
  by_cases hu0 : u < 0
  · exact False.elim (hu (h0x u ((Cut.mem_zero (q := u)).mpr hu0)))
  · exact _root_.Rat.not_lt.mp hu0

theorem pos_of_pos_mem_of_not_mem {x : Cut} {a u : Rat}
    (ha : x.mem a)
    (hapos : 0 < a)
    (hu : Not (x.mem u)) :
    0 < u :=
  Tautology.RealBasic.ModuleBackend.Rat.lt_of_lt_of_le hapos
    (Cut.le_of_mem_of_not_mem ha hu)

/-- A positive cut contains a strictly positive rational. The witness comes
from the failure of `x <= 0` and is then pushed strictly above zero with
`no_greatest`, because the rational that directly witnesses the failure may
be zero. -/
theorem exists_pos_mem_of_pos {x : Cut} (hx : 0 < x) :
    Exists (fun a => And (x.mem a) (0 < a)) := by
  have hnot : Not (x <= 0) := hx.right
  have hnot_forall : Not (forall q : Rat, x.mem q -> (0 : Cut).mem q) := hnot
  cases Classical.not_forall.mp hnot_forall with
  | intro q hq_not_imp =>
      have hq_pair : And (x.mem q) (Not ((0 : Cut).mem q)) :=
        Classical.not_imp.mp hq_not_imp
      cases x.no_greatest hq_pair.left with
      | intro r hr =>
          have hq_nonneg : 0 <= q := by
            have hnlt : Not (q < 0) := by
              intro hq0
              exact hq_pair.right ((Cut.mem_zero (q := q)).mpr hq0)
            exact _root_.Rat.not_lt.mp hnlt
          exact Exists.intro r
            (And.intro hr.left
              (Tautology.RealBasic.ModuleBackend.Rat.lt_of_le_of_lt
                hq_nonneg hr.right))

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
