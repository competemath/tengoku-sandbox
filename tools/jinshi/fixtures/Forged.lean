/-
Jinshi fixture: a proof that never met the kernel. `debug.skipKernelTC` makes `addDecl` skip the kernel, and with it this module puts
`forged : False := True.intro`, an ill-typed term, into the environment; the module compiles and `#print axioms` shows nothing. The
replay examinations (leanchecker, lean4lean) must refuse this module: that is what they are for. Nothing of the tree may ever contain
this (the content lint refuses `run_cmd` and the option); it is a test of the test.
-/
-- jinshi: only decide
import Lean
open Lean Elab Command

namespace JinshiFixtures

run_cmd liftCoreM do
  let decl := Declaration.thmDecl { name := `JinshiFixtures.forged, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
  withOptions (fun o => o.setBool `debug.skipKernelTC true) (addDecl decl)

theorem honest_beside_forged : True := trivial

end JinshiFixtures
