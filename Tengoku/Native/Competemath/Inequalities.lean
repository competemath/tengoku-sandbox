/-
Authors: CompeteMath
-/
import Tengoku

namespace Native.Competemath.P156

/-- competemath.com problem 156. -/
theorem ten_tangents_later : (∀ a x : ℝ, x^3 - 2026*x - ((3*a^2 - 2026)*(x - a) + (a^3 - 2026*a)) = (x - a)^2 * (x + 2*a)) ∧ (-2 : ℤ)^10 = 1024 := ⟨fun a x => by ring, by norm_num⟩

end Native.Competemath.P156
