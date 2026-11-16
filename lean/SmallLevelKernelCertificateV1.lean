module
public meta import Lean.Elab.Tactic.Decide
public meta import Lean.Elab.Tactic.ElabTerm

public meta section
open Lean Meta Elab Tactic

private def recordPhase (phase : String) : TacticM Unit := do
  if let some path ← IO.getEnv "ASTRA_KERNEL_PROGRESS" then
    let status ← IO.FS.readFile "/proc/self/status"
    let memory := (status.splitOn "\n").filter fun line =>
      line.startsWith "VmRSS:" || line.startsWith "VmHWM:"
    let declaration ← match (← IO.getEnv "ASTRA_CERTIFICATE_PROGRESS") with
      | some progress => IO.FS.readFile progress
      | none => pure ""
    IO.FS.withFile path .append fun handle =>
      handle.putStrLn (phase ++ "\n" ++ String.intercalate "\n" memory ++ "\n" ++ declaration)

/-- Check a closed certificate with the ordinary kernel, without retrying a
failed kernel reduction in the elaborator to construct a diagnostic. On large
certificates that retry can itself consume the entire memory budget. -/
elab "kernel_certificate" : tactic => do
  closeMainGoalUsing `kernel_certificate fun expectedType _ => do
    recordPhase "preparing closed proposition"
    let expectedType ← instantiateMVars expectedType
    if expectedType.hasFVar || expectedType.hasMVar then
      throwError "kernel_certificate requires a closed proposition"
    recordPhase "constructing decidable instance"
    let pf ← mkDecideProof expectedType
    let levelsInType := (collectLevelParams {} expectedType).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    recordPhase "ordinary kernel check"
    let lemmaName ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels expectedType pf
    recordPhase "ordinary kernel check passed"
    return mkConst lemmaName (lemmaLevels.map .param)

end
