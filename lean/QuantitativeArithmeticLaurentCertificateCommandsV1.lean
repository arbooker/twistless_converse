module
public meta import Lean.Elab.Command
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! Two declaration templates for scalar Laurent certificates.

The input consists of the actual weight names and polynomial identities.
These commands only construct ordinary theorem declarations. Analyticity is
proved by `fun_prop`; the identities are proved by `field_simp` and `ring`.
Every generated proof is checked by the Lean kernel. Neither the generator
nor the supplied identity is a trusted mathematical input.

Keeping the original scalar interfaces makes this consolidation independent
of the consumers' simplification and definitional-equality behavior.
-/

public meta section
open Lean Elab Command

private def elaborateLaurentCertificate (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error message => throwError "Laurent certificate: {message}"
  | .ok declaration => elabCommand declaration

/-- Derive the common analytic statement for each named six-parameter weight.
Only the first four parameters vary with the complex argument. -/
elab "derive_weight_analytic " "[" weights:ident,* "]" : command => do
  for weight in weights.getElems do
    let name := weight.getId.toString
    elaborateLaurentCertificate s!"theorem {name}_analytic
      (X Y Z W : ℂ → ℂ) (a b s : ℂ)
      (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
      (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
      (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0) :
      AnalyticAt ℂ (fun t => {name} (X t) (Y t) (Z t) (W t) a b) s := by
      unfold {name}
      fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])"

/-- Verify an explicit Laurent identity for all nonzero first four parameters.
The `using` list names the scalar weight definitions to unfold. -/
elab "certify_laurent_identity " name:ident " : " identity:term
    " using " "[" weights:ident,* "]" : command => do
  let some statement := identity.raw.reprint
    | throwError "Cannot print the supplied Laurent identity"
  let names := String.intercalate " " (weights.getElems.toList.map fun w => w.getId.toString)
  elaborateLaurentCertificate s!"theorem {name.getId.toString}
    (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) :
    {statement} := by
    unfold {names}
    field_simp [hx,hy,hz,hw]
    ring"
