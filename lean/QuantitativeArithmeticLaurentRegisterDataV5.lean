module
public meta import Lean
public meta import QuantitativeArithmeticLaurentProgramComputeV4

/-! Register-state data generation without compiling a large quoted expression.
The decoder reads constructor-normalized input data. The result is only a
candidate: the unchanged `verifyRun_sound` certificates check every state in
the ordinary kernel. No proof is produced by this elaborator. -/
public meta section
open Lean Meta Elab Term
open QuantitativeArithmeticSevenLaurentRows

namespace QuantitativeArithmeticLaurentRegisterData

private def phase (label : String) : MetaM Unit := do
  if let some path ← IO.getEnv "ASTRA_REGISTER_PROGRESS" then
    let status ← IO.FS.readFile "/proc/self/status"
    let memory := (status.splitOn "\n").filter fun line =>
      line.startsWith "VmRSS:" || line.startsWith "VmHWM:"
    IO.FS.withFile path .append fun handle =>
      handle.putStrLn (label ++ "\n" ++ String.intercalate "\n" memory)

private def natural (e : Expr) : MetaM Nat := do
  let some n ← getNatValue? e | throwError "Expected a reduced natural number"
  return n

private def integer (e : Expr) : MetaM Int := do
  let e := e.consumeMData
  if e.isAppOfArity ``Int.ofNat 1 then
    return .ofNat (← natural e.getAppArgs[0]!)
  if e.isAppOfArity ``Int.negSucc 1 then
    return .negSucc (← natural e.getAppArgs[0]!)
  throwError "Expected a reduced integer constructor"

private def product (e : Expr) : MetaM (Expr × Expr) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``Prod.mk 4 do
    throwError "Expected a reduced product constructor"
  return (e.getAppArgs[2]!, e.getAppArgs[3]!)

private def rational (e : Expr) : MetaM Rat := do
  let e := e.consumeMData
  unless e.isAppOfArity ``Rat.mk' 4 do
    throwError "Expected a reduced rational constructor"
  let n ← integer e.getAppArgs[0]!
  let d ← natural e.getAppArgs[1]!
  if d == 0 then throwError "Zero denominator in register data"
  return Rat.divInt n (.ofNat d)

private partial def list {α : Type} (read : Expr → MetaM α) (e : Expr) : MetaM (List α) := do
  let e := e.consumeMData
  if e.isAppOfArity ``List.nil 1 then return []
  unless e.isAppOfArity ``List.cons 3 do
    throwError "Expected a reduced list constructor"
  let head ← read e.getAppArgs[1]!
  let tail ← list read e.getAppArgs[2]!
  return head :: tail

private def exponent (e : Expr) : MetaM Exponent := do
  let (x, e) ← product e
  let (y, e) ← product e
  let (z, e) ← product e
  let (w, e) ← product e
  let (a, e) ← product e
  let (b, c) ← product e
  return (← integer x, ← integer y, ← integer z, ← integer w,
    ← natural a, ← natural b, ← natural c)

private def entry (e : Expr) : MetaM QuantitativeArithmeticSevenLaurentRows.Term := do
  let (r, e) ← product e
  let (j, powers) ← product e
  return (← rational r, ← natural j, ← exponent powers)

private def instruction (e : Expr) : MetaM QuantitativeArithmeticLaurentRegisterProgram.Instruction := do
  let e := e.consumeMData
  unless e.isAppOfArity ``QuantitativeArithmeticLaurentRegisterProgram.Instruction.mk 4 do
    throwError "Expected a reduced register instruction"
  return ⟨← natural e.getAppArgs[0]!, ← natural e.getAppArgs[1]!,
    ← natural e.getAppArgs[2]!, ← list entry e.getAppArgs[3]!⟩

elab "register_state_compact% " "(" rows:term ")" "(" program:term ")" : term => do
  phase "elaborating register inputs"
  let rows ← elabTermAndSynthesize rows none
  let program ← elabTermAndSynthesize program none
  phase "reducing register inputs"
  let rows ← withTransparency .all <| reduce (← instantiateMVars rows)
  let program ← withTransparency .all <| reduce (← instantiateMVars program)
  phase "decoding register inputs"
  let rows ← list (list entry) rows
  let program ← list instruction program
  phase "computing candidate register state"
  let result := QuantitativeArithmeticLaurentRegisterProgram.Compute.run rows program
  phase "quoting candidate register state"
  let result := toExpr result
  phase "candidate register state ready for kernel certification"
  return result

end QuantitativeArithmeticLaurentRegisterData
end
