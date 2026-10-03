module

import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Order
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Dedekind.Neg
import all Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Rat

/-!
# The Archimedean property

One theorem: for every cut there is a rational above it. It comes almost
immediately from properness -- a cut omits some rational, and that rational
bounds it -- which is why the file is a single line of substance.

Its position is what to notice. Archimedes is needed as early as
`Dedekind.AddInv`, before any multiplication exists, so it sits near the
bottom of the backend rather than among the later results.

## Position in the development

Above `Dedekind.Order` and `Dedekind.Neg`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend
namespace Dedekind
namespace Cut

/-- Members and nonmembers of a cut can be found arbitrarily close: for
every positive rational `ε` there is a member `a` and a nonmember `b` with
`b - a < ε`. The proof walks up from a member in steps of `ε / 2` and
contradicts properness once the walk passes a nonmember; the walk always gets
there because the rationals are Archimedean. -/
theorem exists_inner_outer_gap_lt (x : Cut) {ε : Rat} (hε : 0 < ε) :
    Exists (fun a => And (x.mem a)
      (Exists (fun b => And (Not (x.mem b)) (b - a < ε)))) := by
  apply Classical.byContradiction
  intro hnone
  cases x.nonempty with
  | intro a0 ha0 =>
      cases x.proper with
      | intro b0 hb0 =>
          let δ : Rat := ε / 2
          have hδpos : 0 < δ := Tautology.RealBasic.ModuleBackend.Rat.half_pos hε
          have hδlt : δ < ε := Tautology.RealBasic.ModuleBackend.Rat.half_lt hε
          have hstep : forall a, x.mem a -> x.mem (a + δ) := by
            intro a ha
            by_cases hmem : x.mem (a + δ)
            · exact hmem
            · have hgap : (a + δ) - a < ε := by
                have hcancel : (a + δ) - a = δ := by
                  rw [_root_.Rat.add_comm]
                  rw [_root_.Rat.add_sub_cancel]
                rw [hcancel]
                exact hδlt
              exact False.elim
                (hnone
                  (Exists.intro a
                    (And.intro ha
                      (Exists.intro (a + δ)
                        (And.intro hmem hgap)))))
          have hsteps :
              forall n, x.mem (Tautology.RealBasic.ModuleBackend.Rat.step a0 δ n) := by
            intro n
            induction n with
            | zero =>
                exact ha0
            | succ n ih =>
                exact hstep
                  (Tautology.RealBasic.ModuleBackend.Rat.step a0 δ n) ih
          cases Tautology.RealBasic.ModuleBackend.Rat.exists_step_gt a0 b0 δ hδpos with
          | intro n hbn =>
              exact hb0 (x.downward hbn (hsteps n))

end Cut
end Dedekind
end ModuleBackend
end RealBasic
end Tautology
