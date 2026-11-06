module
public meta import Lean.Elab.Command
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public meta section
open Lean Elab Command
/-- Check a block of polynomial coefficients directly from the coefficient lists.
The command generates ordinary theorems and standard kernel-checked ring proofs. -/
elab "certify_coefficient_block " params:bracketedBinder " for " cert:term
    " indices " firstIndex:num " through " lastIndex:num
    " unfolding " "[" definitions:ident,* "]" : command => do
  let some binders := params.raw.reprint | throwError "Missing coefficient binders"
  let some expression := cert.raw.reprint | throwError "Missing coefficient expression"
  let names := definitions.getElems.toList.map (fun d => d.getId.toString)
  for i in [firstIndex.getNat:lastIndex.getNat + 1] do
    let name := s!"coefficient_{i}"
    let nested := (← getEnv).contains (Name.str (← getCurrNamespace) s!"inner_eval_{i}")
    let selected := if nested then names.filter (fun n => n == "certificate" || n.startsWith "coefficients") else names
    let defs := String.intercalate ", " selected
    let finish := if nested then
      s!"rw [←inner_eval_{i}]; exact evaluate_zero a _ (inner_zero_{i} y z w b u)"
      else s!"simp only [{defs}]; ring"
    let source := s!"theorem {name} {binders} : ({expression})[{i}]? = some 0 := by
      change some _ = some (0 : ℂ)
      apply congrArg some
      {finish}"
    for declaration in [source, s!"#print axioms {name}"] do
      match Parser.runParserCategory (← getEnv) `command declaration with
      | .error message => throwError "Coefficient certificate: {message}"
      | .ok stx =>
        withScope (fun scope => { scope with opts := ((scope.opts.setBool `Elab.async false).setBool `linter.unusedTactic false).setBool `linter.unusedSimpArgs false }) <|
          withEnableInfoTree false <| elabCommand stx

/-- Check a certificate declaration without retaining editor-only data. -/
elab "compact_certificate_declaration " proofDecl:command : command => do
  withScope (fun scope => { scope with opts :=
    (((scope.opts.setBool `Elab.async false).setBool `linter.unusedTactic false).setBool `linter.unusedSimpArgs false).setBool `linter.unreachableTactic false }) <|
    withEnableInfoTree false <| elabCommand proofDecl
end
