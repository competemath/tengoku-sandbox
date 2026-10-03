import Tengoku.Tautology.Tautology.RealBasic.ModuleBackend.Interface

/-!
# The selection type, above the valve

`Selection` re-exported under `RealBasic.Backend`, so the modules just outside
the sealed subtree can name the type without importing the module-system
files directly.

One `abbrev`, and it is the first name on the outside of the boundary.
Everything above works with this type and never with what produced it.

## Position in the development

Directly above `Tautology.RealBasic.ModuleBackend`.

## Role

Implementation.
-/

namespace Tautology
namespace RealBasic
namespace Backend

/-- The selection type re-exported above the seal: the first name on the
outside of the boundary, and the one the modules here name the type
through. -/
abbrev Selection := ModuleBackend.Selection

end Backend
end RealBasic
end Tautology
