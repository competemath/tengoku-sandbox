/-
Changed for Tengoku: copied from ProofWidgets (leanprover-community/ProofWidgets4 at a8acbfd87375); import paths rewritten.
-/
module

public import Tengoku.Seed.Widgets.Component.Panel.Basic

public meta section

namespace ProofWidgets

/-- Display the goal type using known `Expr` presenters. -/
@[widget_module]
def GoalTypePanel : Component PanelWidgetProps where
  javascript := include_str ".." / ".." / ".." / "widget" / "js" / "goalTypePanel.js"

end ProofWidgets
