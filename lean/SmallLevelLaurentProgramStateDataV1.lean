module
public meta import QuantitativeArithmeticLaurentProgramDataV4
public meta section
open Lean Meta Elab Term
/-- Produce candidate state data only; callers separately prove every transition. -/
syntax (name := laurentProgramState) "program_state% " "(" term ")" "(" term ")" : term
@[term_elab laurentProgramState]
unsafe def elabLaurentProgramState : TermElab
  | `(term| program_state% ($rows) ($program)), _ => do
      let rows ← elabTermAndSynthesize rows none
      let program ← elabTermAndSynthesize program none
      let rows ← withTransparency .all <| reduce (← instantiateMVars rows)
      let program ← withTransparency .all <| reduce (← instantiateMVars program)
      let result ← mkAppM ``QuantitativeArithmeticLaurentProgram.Compute.run #[rows, program]
      let quoted ← mkAppM ``Lean.toExpr #[result]
      evalExpr Expr (mkConst ``Lean.Expr) quoted (safety := .unsafe)
  | _, _ => throwUnsupportedSyntax
