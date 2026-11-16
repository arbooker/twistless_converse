module
public import QuantitativeArithmeticLaurentRegisterProgramTheoryV4
set_option synthInstance.maxSize 2048
@[expose] public noncomputable section
namespace QuantitativeArithmeticLaurentRegisterProgram
open QuantitativeArithmeticSevenLaurentRows

/-- Compose two already verified pieces of a register program. -/
theorem run_append_of_results {rows middle last : List Poly}
    {first second : List Instruction}
    (hfirst : run rows first = middle) (hsecond : run middle second = last) :
    run rows (first ++ second) = last :=
  (run_append rows first second).trans
    ((congrArg (fun state => run state second) hfirst).trans hsecond)

/-- Check the final output once, after establishing the complete run result. -/
theorem verify_of_run_result {rows last result : List Poly}
    {code : List Instruction} {indices : List ℕ}
    (hrun : run rows code = last)
    (hfinal : verify last [] indices result = true) :
    verify rows code indices result = true := by
  unfold verify
  apply decide_eq_true
  unfold outputs
  rw [hrun]
  exact verify_sound hfinal

#print axioms run_append_of_results
#print axioms verify_of_run_result
end QuantitativeArithmeticLaurentRegisterProgram
end
