module

public import Tengoku
public import Tengoku.Std
public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq

public section

scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]
