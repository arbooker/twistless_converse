module
public import QuantitativeArithmeticSmallLevelThirtyThreeSourceWordsV1
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix

theorem source_nonaffine (i : Fin 223) : sourceMatrix i 1 0 ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem source_det_pos (i : Fin 223) : 0 < (sourceMatrix i).det := by
  fin_cases i <;> decide +kernel

#print axioms source_nonaffine
#print axioms source_det_pos
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
