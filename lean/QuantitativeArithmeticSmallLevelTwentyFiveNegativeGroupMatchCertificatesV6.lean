module
public import QuantitativeArithmeticSmallLevelTwentyFiveNegativeExtraMinusOneRowsTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.NegativeExtraMinusOneRows
open QuantitativeArithmeticSevenLaurentRows
certificate_batch {
compact_certificate theorem groups222_L_match_compact : group222_568Raw=left222 := by rfl
#print axioms groups222_L_match_compact
compact_certificate theorem groups222_R_match_compact : group222_735Raw=reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right222) := by decide +kernel
#print axioms groups222_R_match_compact
compact_certificate theorem groups222_special_match_compact : mixed222node108Ops=group222_568Special ++ group222_735Special := by decide +kernel
#print axioms groups222_special_match_compact
}
end QuantitativeArithmeticSmallLevelTwentyFive.NegativeExtraMinusOneRows
end
