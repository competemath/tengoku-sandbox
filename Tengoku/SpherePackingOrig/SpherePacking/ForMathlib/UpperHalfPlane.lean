module

public import Tengoku

/-!
# The Upper Half-Plane

Auxiliary lemmas about the upper half-plane.
-/

@[expose] public section

-- Probably put it at LinearAlgebra/Matrix/SpecialLinearGroup.lean

theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  simp [S]
  fin_cases i <;> fin_cases j <;> simp
  first
    | (all_goals grind; done; trace "PORTFOLIO-OK grind")
    | (all_goals simp_all; done; trace "PORTFOLIO-OK simp_all")
    | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")
    | (all_goals omega; done; trace "PORTFOLIO-OK omega")
    | (all_goals norm_num; done; trace "PORTFOLIO-OK norm_num")
    | (all_goals positivity; done; trace "PORTFOLIO-OK positivity")
    | (all_goals linarith; done; trace "PORTFOLIO-OK linarith")
    | (all_goals decide; done; trace "PORTFOLIO-OK decide")
    | (all_goals tauto; done; trace "PORTFOLIO-OK tauto")
