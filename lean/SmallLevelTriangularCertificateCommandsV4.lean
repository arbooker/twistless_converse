module
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination

/-! Compact certificates for triangular elimination in a finite rational system.
Each entry records the selected row, pivot column, earlier zero coordinates,
and the exact linear combination. The command emits an ordinary theorem proved
by `linear_combination`; it neither assumes nor externally certifies its result.
The row expression is read from its definition, rather than copied into every
pivot proof. Generated declarations retain their original public names. -/
public meta section
open Lean Meta Elab Command Tactic

/- Reduce only the selected row's outer match. Recursive simplification of the
whole row definition also descends into its arithmetic and exhausted the
recursion limit. The replacement hypothesis is checked definitionally equal. -/
elab "reduce_triangular_row " "at " h:ident : tactic => withMainContext do
  let fvar ← getFVarId h
  let some (_, lhs, rhs) := (← whnf (← fvar.getType)).eq?
    | throwError "Expected an equality for the selected row"
  let selected ← whnfCore (← unfoldDefinition lhs)
  let goal ← (← getMainGoal).changeLocalDecl fvar (← mkEq selected rhs)
  replaceMainGoal [goal]

elab "certify_triangular_pivot " name:ident " in " rows:ident
    " dimension " dimension:num " row " row:num
    " using " "[" predecessors:num,* "]"
    " proves " "(" conclusion:term ")"
    " combination " "(" combination:term ")" : command => do
  let pieces := name.getId.toString.splitOn "_"
  unless pieces.length ≥ 2 do
    throwError "Expected a pivot name ending in its index"
  let family := String.intercalate "_" (pieces.take (pieces.length - 1))
  let some expression := combination.raw.reprint
    | throwError "Cannot print the linear-combination certificate"
  let some goal := conclusion.raw.reprint
    | throwError "Cannot print the pivot conclusion"
  let earlier := String.intercalate "\n" <|
    predecessors.getElems.toList.map fun i =>
      s!"  have p{i.getNat} := {family}_{i.getNat} w hw"
  let source := s!"theorem {name.getId.toString}
    (w : Fin {dimension.getNat} → ℂ) (hw : ∀ i, {rows.getId.toString} w i = 0) :
    {goal} := by
  have h := hw {row.getNat}
  reduce_triangular_row at h
{earlier}
  linear_combination {expression}"
  match Parser.runParserCategory (← getEnv) `command source with
  | .error message => throwError "Triangular certificate: {message}"
  | .ok declaration =>
    withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
      withEnableInfoTree false <| elabCommand declaration

/-! Homogeneous families reuse the inhomogeneous certificates. The ordinary
specialization lemma compares the identity at v with the identity at zero.
This command only supplies parameter binders and legacy theorem names; Lean
infers the conclusion from that proof and audits every emitted declaration. -/
/-- Recover the proposition of a checked certificate expression when generating
an ordinary theorem header; the downstream batch checks the original types. -/
elab "certificate_type% " value:term : term => do
  let proof ← Term.elabTerm value none
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.inferType proof

elab "specialize_homogeneous_pivots " sourceNamespace:ident
    " in " rows:ident " dimension " vectorSize:num " count " pivotCount:num
    " zero_rows " zeroRows:ident " via " specialization:ident : command => do
  for i in [:pivotCount.getNat] do
    let name := s!"pivot_{i}"
    let declaration := s!"theorem {name}
        (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
        (v : Fin {vectorSize.getNat} → ℂ)
        (hv : ∀ i, {rows.getId.toString} X Y Z W a b v i = 0) :
      certificate_type% ({specialization.getId.toString}
        ({sourceNamespace.getId.toString}.{name} X Y Z W a b hX hY hZ hW)
        ({zeroRows.getId.toString} X Y Z W a b)
        (by simp only [Pi.zero_apply, mul_zero, add_zero]) v hv) :=
      {specialization.getId.toString}
        ({sourceNamespace.getId.toString}.{name} X Y Z W a b hX hY hZ hW)
        ({zeroRows.getId.toString} X Y Z W a b)
        (by simp only [Pi.zero_apply, mul_zero, add_zero]) v hv"
    for source in [declaration, s!"#print axioms {name}"] do
      match Parser.runParserCategory (← getEnv) `command source with
      | .error message => throwError "Homogeneous specialization: {message}"
      | .ok stx =>
        withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
          withEnableInfoTree false <| elabCommand stx

/- Elaborate a large existing algebra proof without retaining editor details. -/
elab "compact_elimination_proof " proofDecl:command : command => do
  if let some source := proofDecl.raw.reprint then
    let output ← IO.getStderr
    output.putStrLn (String.ofList (((source.splitOn "\n").head!).toList.take 120))
    output.flush
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
    withEnableInfoTree false <| elabCommand proofDecl
