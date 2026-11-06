module
public import QuantitativeArithmeticSmallLevelTwentySevenStagedReconstructionV1
public import QuantitativeArithmeticSmallLevelTwentySevenObservationTheoryV4
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSevenLaurentRows Matrix


theorem observation_rows (i : Fin 321) :
    inputs (1100+i.val)=liftRationalRow (QuantitativeArithmeticSmallLevelTwentySevenObservation.basis i.val) := by
  fin_cases i <;> rfl

theorem outputMatrix_eq_basis (x y z w a b c : ℂ) :
    outputMatrix x y z w a b c=QuantitativeArithmeticSmallLevelTwentySevenObservation.basisMatrix := by
  funext i j
  change coefficient x y z w a b c (inputs (1100+i.val)) j.val=_
  rw [observation_rows,coefficient_lift]
  rfl

theorem staged_basis_reconstruction (x y z w a b c : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hp : ∀ n, n<871 → stageLead x y z w a b c n≠0) :
    stagedLeftMatrix x y z w a b c*sourceMatrix x y z w a b c=QuantitativeArithmeticSmallLevelTwentySevenObservation.basisMatrix := by
  rw [staged_matrix_identity x y z w a b c hx hy hz hw hp,outputMatrix_eq_basis]
#print axioms observation_rows
#print axioms staged_basis_reconstruction
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
