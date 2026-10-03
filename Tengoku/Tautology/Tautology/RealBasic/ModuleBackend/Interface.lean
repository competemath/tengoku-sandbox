module

public import Tengoku.Tautology.Tautology.Foundation.OrderField

/-!
# The only thing the valve lets through

`Selection` has three fields: a `String`, a `Type`, and a proof that the type
is a Dedekind complete ordered field. That is the entire public surface of the
backend subtree, and everything above the valve sees this and nothing else.

The narrowness is the experiment. Sixty-four files beside this one construct
three complete real number systems -- Dedekind cuts, Eudoxus
almost-homomorphisms, Cauchy sequences -- and none of their internals can be
named from above: not a cut, not a quotient, not an equivalence class. What
crosses the boundary is a carrier together with the fact that it satisfies the
axioms, which is exactly what a consumer of the reals should need.

**The sealing is enforced by the compiler, not by convention.** This file and
its neighbours are declared with Lean 4's module system, and what is not marked
`public` does not leave. A library that merely documented the boundary would
leave the claim untested; here an attempt to reach past it fails to compile.

The `name` field looks decorative and is not. It is what makes the choice of
construction readable as data rather than recoverable only by tracing imports,
the same device used at the two route selection points and in the elementary
valve room.

## Position in the development

Above `Tautology.Foundation.OrderField`, which supplies
`IsDedekindCompleteOrderedFieldBaseLike`. Every backend module is above this
one, and `Tautology.RealBasic.ValveRoom` consumes it.

## Role

Interface, and the valve boundary itself.
-/

namespace Tautology
namespace RealBasic
namespace ModuleBackend

/-- One construction of the real numbers as data: a `name` identifying it, the
`Carrier` it lives on, and the proof `completeField` that this carrier is a
Dedekind complete ordered field. A consumer of the reals needs nothing else,
and above the valve nothing else is reachable. -/
public structure Selection where
  name : String
  Carrier : Type
  completeField : IsDedekindCompleteOrderedFieldBaseLike Carrier

end ModuleBackend
end RealBasic
end Tautology
