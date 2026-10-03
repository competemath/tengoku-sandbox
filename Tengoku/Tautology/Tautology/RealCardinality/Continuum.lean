import Tengoku.Tautology.Tautology.RealCardinality.ContinuumUpper
import Tengoku.Tautology.Tautology.RealCardinality.ContinuumLower

/-!
# Exactly continuum many points

The confluence of the region: `continuumLowerBound` and `continuumUpperBound`
are combined through Cantor--Bernstein (`continuumSized_iff_bounds` of
`Tautology.Foundation.Cardinal`) into the statement that a Dedekind-complete
ordered field has exactly the cardinality of the continuum.

## Position and role

Implementation module with a single theorem and no construction of its own; it
exists so that the two halves have a named meeting point. Like both halves it
speaks of an arbitrary complete ordered field -- the specialisation to the
selected carrier is `RealTheory.continuumSized` in
`Tautology.RealTheory.Cardinality`.

Note what this does not say. That the field is uncountable is proved separately
in `Uncountable`, by an argument that needs no cardinal arithmetic; this file
does not derive one from the other.
-/

namespace Tautology
namespace IsDedekindCompleteOrderedFieldBaseLike

variable {alpha : Type}
/-- Any Dedekind-complete ordered field has exactly the cardinality of the
continuum: `continuumLowerBound` supplies an injection of binary sequences
into the field, `continuumUpperBound` an injection the other way, and
Cantor--Bernstein (`continuumSized_iff_bounds`) merges the two into an
equipotence. Like its two halves this holds for every complete field, not
just the carrier selected for the real line. -/
theorem continuumSized
    (C : IsDedekindCompleteOrderedFieldBaseLike alpha) :
    Foundation.Cardinal.ContinuumSized alpha :=
  (Foundation.Cardinal.continuumSized_iff_bounds).mpr
    (And.intro
      (continuumLowerBound C)
      (continuumUpperBound C))

end IsDedekindCompleteOrderedFieldBaseLike
end Tautology
