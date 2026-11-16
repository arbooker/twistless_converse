module
public import QuantitativeArithmeticLaurentProgramTheoryV4
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticLaurentProgram
open QuantitativeArithmeticSevenLaurentRows

theorem run_append (rows : List Poly) (first second : List Instruction) :
    run rows (first ++ second) = run (run rows first) second := by
  induction first generalizing rows with
  | nil => rfl
  | cons instruction rest ih => exact ih (step rows instruction)

theorem run_append_of_results {rows middle last : List Poly}
    {first second : List Instruction}
    (hfirst : run rows first = middle) (hsecond : run middle second = last) :
    run rows (first ++ second) = last :=
  (run_append rows first second).trans
    ((congrArg (fun state => run state second) hfirst).trans hsecond)

theorem outputs_of_run_result {rows last result : List Poly}
    {code : List Instruction} {indices : List ℕ}
    (hrun : run rows code = last)
    (hfinal : indices.map (rowAt last) = result) :
    outputs rows code indices = result :=
  (congrArg (fun state => indices.map (rowAt state)) hrun).trans hfinal

#print axioms run_append
#print axioms run_append_of_results
#print axioms outputs_of_run_result
end QuantitativeArithmeticLaurentProgram
end
