module
public meta import Lean
public meta import QuantitativeArithmeticLaurentProgramComputeV4

/-! Regenerate intermediate certificate data rather than printing it twice.
Input lists may be noncomputable definitions containing literal rational data;
reduce those definitions before executing the data producer. This elaborator
returns only a list expression, never a proof or a mathematical axiom. -/
public meta section
open Lean Meta Elab Term

syntax (name := laurentProgramResults)
  "program_results% " "(" term ")" "(" term ")" "(" term ")" : term

@[term_elab laurentProgramResults]
unsafe def elabLaurentProgramResults : TermElab
  | `(term| program_results% ($rows) ($program) ($indices)), _ => do
      let rows ← elabTermAndSynthesize rows none
      let program ← elabTermAndSynthesize program none
      let indices ← elabTermAndSynthesize indices none
      let rows ← withTransparency .all <| reduce (← instantiateMVars rows)
      let program ← withTransparency .all <| reduce (← instantiateMVars program)
      let indices ← withTransparency .all <| reduce (← instantiateMVars indices)
      let result ← mkAppM ``QuantitativeArithmeticLaurentProgram.Compute.outputs
        #[rows, program, indices]
      let quoted ← mkAppM ``Lean.toExpr #[result]
      evalExpr Expr (mkConst ``Lean.Expr) quoted (safety := .unsafe)
  | _, _ => throwUnsupportedSyntax

syntax (name := laurentRegisterState)
  "register_state% " "(" term ")" "(" term ")" : term

@[term_elab laurentRegisterState]
unsafe def elabLaurentRegisterState : TermElab
  | `(term| register_state% ($rows) ($program)), _ => do
      let rows ← elabTermAndSynthesize rows none
      let program ← elabTermAndSynthesize program none
      let rows ← withTransparency .all <| reduce (← instantiateMVars rows)
      let program ← withTransparency .all <| reduce (← instantiateMVars program)
      let result ← mkAppM ``QuantitativeArithmeticLaurentRegisterProgram.Compute.run #[rows, program]
      let quoted ← mkAppM ``Lean.toExpr #[result]
      evalExpr Expr (mkConst ``Lean.Expr) quoted (safety := .unsafe)
  | _, _ => throwUnsupportedSyntax
