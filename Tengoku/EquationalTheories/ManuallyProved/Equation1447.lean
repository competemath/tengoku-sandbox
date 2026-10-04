-- Tengoku.EquationalTheories.ManuallyProved.Equation1447: verified translations of equational_theories/ManuallyProved/Equation1447.lean (1 theorem)
import Tengoku.Seed.Logic.Function.Defs
import Tengoku.Seed.Data.Set.Basic
import Tengoku.Seed.Data.Real.Sqrt
import Tengoku.Seed.Topology.Instances.AddCircle.Real
import Lean.Elab.Exception
import Lean.Elab.Declaration
import Lean.Util.CollectAxioms
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Tengoku.Seed.Data.FunLike.Basic
import Tengoku.Seed.Logic.Equiv.Basic
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.Seed.Data.List.NodupEquivFin
import Tengoku.Seed.Data.Set.Defs
import Lean
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

-- This file mechanizes the construction described in:
-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/713.2C.201289.2C.201447/near/482236139








namespace Equation1447

section Construction

universe u

-- Select a surjective map `S : M → M` as the candidate squaring map
variable {M : Type u} (S : M → M)

-- with the property that S, S^2, S^3 have no fixed points
def no_fixed_points : Prop := ∀ (m : M), S m ≠ m ∧ S (S m) ≠ m ∧ S (S (S m)) ≠ m

variable (hnofix : no_fixed_points S)

include hnofix

def square_roots (x : M) : Set M := { y : M | S y = x }

notation "√" => square_roots

omit hnofix in

lemma square_roots_elem_iff_square_root (x y : M) :
  y ∈ square_roots S x ↔ S y = x
:= Set.mem_setOf

end Construction
end Equation1447

end EquationalTheories
