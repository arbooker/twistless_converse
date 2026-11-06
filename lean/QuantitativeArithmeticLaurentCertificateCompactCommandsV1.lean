module
public meta import Lean.Elab.Command
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Scalar certificate elaboration without retaining editor information for
the generated tactic scripts. The resulting theorem types and kernel-checked
proofs are the ordinary `field_simp`/`ring` proofs. Synchronous elaboration
keeps large certificate families from accumulating pending elaborator tasks. -/

public meta section
open Lean Elab Command

elab "certify_laurent_identity_compact " name:ident " : " identity:term
    " using " "[" weights:ident,* "]" : command => do
  let some statement := identity.raw.reprint
    | throwError "Cannot print the supplied Laurent identity"
  let names := String.intercalate " " (weights.getElems.toList.map fun w => w.getId.toString)
  let source := s!"theorem {name.getId.toString}
    (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    {statement} := by
    unfold {names}
    field_simp [hx,hy,hz,hw]
    ring"
  match Parser.runParserCategory (← getEnv) `command source with
  | .error message => throwError "Laurent certificate: {message}"
  | .ok declaration =>
    withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
      withEnableInfoTree false <| elabCommand declaration
