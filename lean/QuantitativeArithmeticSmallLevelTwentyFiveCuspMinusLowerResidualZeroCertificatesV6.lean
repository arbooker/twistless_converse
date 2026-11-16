module
public import QuantitativeArithmeticSmallLevelTwentyFiveCuspMinusLowerResidualTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import SmallLevelCertificateBatchCommandV1
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.CuspMinusLowerResidual
open QuantitativeArithmeticSevenLaurentRows
certificate_batch {
compact_certificate theorem upper_checked_0_compact : substitute upperSource (upperOperation 0)=upperResidual 0 := by
  simp only [← substituteCompute_eq]
  decide +kernel
#print axioms upper_checked_0_compact
compact_certificate theorem lower_checked_0_compact : substitute lowerSource (lowerOperation 0)=lowerResidual 0 := by
  simp only [← substituteCompute_eq]
  decide +kernel
#print axioms lower_checked_0_compact
compact_certificate theorem first_checked_0_compact : substitute (fun j => substitute CuspMinusLaurent.basis (rawJet j)) (lowerOperation 0)=firstResidual 0 := by
  simp only [← substituteCompute_eq]
  decide +kernel
#print axioms first_checked_0_compact
}
end QuantitativeArithmeticSmallLevelTwentyFive.CuspMinusLowerResidual
end
