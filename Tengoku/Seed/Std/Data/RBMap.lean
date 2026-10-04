/-
Changed for Tengoku: copied from Batteries (leanprover-community/batteries at d54dddc581e0); import paths rewritten.
-/
module -- deprecated_module: ignore

public import Tengoku.Seed.Std.Data.RBMap.Basic
public import Tengoku.Seed.Std.Data.RBMap.Depth
public import Tengoku.Seed.Std.Data.RBMap.Lemmas
public import Tengoku.Seed.Std.Data.RBMap.Alter
public import Tengoku.Seed.Std.Data.RBMap.WF

deprecated_module "it is recommended to use Std.TreeMap instead" (since := "2026-05-14")
