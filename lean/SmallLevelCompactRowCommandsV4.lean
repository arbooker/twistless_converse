module
public meta import Lean.Elab.Tactic
public meta import QuantitativeArithmeticCompactCommandsV1

/-! Reduce a selected row definition without exposing certificate-language
keywords such as row and count to importing mathematical chapters. -/
public meta section
open Lean Meta Elab Command Tactic

elab "reduce_compact_row " "at " h:ident : tactic => withMainContext do
  let fvar ← getFVarId h
  let some (_, lhs, rhs) := (← whnf (← fvar.getType)).eq?
    | throwError "Expected an equality for the selected row"
  let selected ← whnfCore (← unfoldDefinition lhs)
  let goal ← (← getMainGoal).changeLocalDecl fvar (← mkEq selected rhs)
  replaceMainGoal [goal]

