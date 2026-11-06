module
public meta import Lean.Elab.Tactic
public import Mathlib.Tactic

/-! Shared normalization for explicit Laurent source-row certificates.
The surrounding theorem supplies X,Y,Z,W,a,b,v and nonzero hypotheses
hX,hY,hZ,hW. Each invocation retains its original row-specific definitional
identities; the common routine clears denominators and checks the resulting
polynomial equality. No certificate is accepted without an ordinary Lean proof.
Policies distinguish the existing four-prime and level-26 normalizations. -/
public meta section
open Lean Elab Tactic

elab "match_laurent_source " part:ident " at " offset:num
    " policy " policy:ident " using " "[" reductions:term,* "]" : tactic => do
  let normalization ← match policy.getId.toString with
    | "fourPrime" => pure "gridWordSign,gridBaseSign,SmallLevelFourPrimeRates.monomial,gridSample,gridIndex,primeParameter,primeEigenvalue,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ"
    | "level26" | "level26Optional" => pure "gridWordSign,gridBaseSign,monomial,gridSample,gridIndex,primeParameter,primeEigenvalue,Finset.sum_range_succ"
    | _ => throwError "Unknown Laurent source normalization policy"
  let clearing := if policy.getId.toString == "level26Optional" then
    "(try field_simp [hX,hY,hZ,hW])" else "field_simp [hX,hY,hZ,hW]"
  let args ← reductions.getElems.toList.mapM fun t =>
    match t.raw.reprint with
    | some s => pure s
    | none => throwError "Cannot print a source-row reduction"
  let source := s!"change {part.getId.toString} X Y Z W a b v {offset.getNat} = _\n  simp only [{String.intercalate "," args}]\n  norm_num [{part.getId.toString},{normalization}] <;> {clearing} <;> ring_nf <;> simp_all"
  match Parser.runParserCategory (← getEnv) `tactic ("first |\n  " ++ source) with
  | .error message => throwError "Laurent source certificate: {message}"
  | .ok proof => evalTactic proof
