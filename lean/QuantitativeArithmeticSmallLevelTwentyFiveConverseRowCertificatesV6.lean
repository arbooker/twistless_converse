module
public import QuantitativeArithmeticSmallLevelTwentyFiveOriginalFirstJetTheoryV4
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import SmallLevelCertificateBatchCommandV1
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
@[expose] public noncomputable section
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
certificate_batch {
namespace QuantitativeArithmeticSmallLevelTwentyFive.OriginalFirstJet
compact_certificate theorem left147_support_compact : ∀ t ∈ left147,t.2.1<4518 := by decide +kernel
#print axioms left147_support_compact

compact_certificate theorem left147_jet_support_compact : ∀ t ∈ left147,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left147_jet_support_compact

compact_certificate theorem right147_support_compact : ∀ t ∈ right147,t.2.1<4518 := by decide +kernel
#print axioms right147_support_compact

compact_certificate theorem lower147_operations_compact : lower147node12Ops=left147 := by decide +kernel
#print axioms lower147_operations_compact

compact_certificate theorem mixed147_operations_compact : mixed147node58Ops=left147 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right147) := by decide +kernel
#print axioms mixed147_operations_compact

compact_certificate theorem mixed147_result_compact : mixed147node58Result=result147 := by decide +kernel
#print axioms mixed147_result_compact

compact_certificate theorem left201_support_compact : ∀ t ∈ left201,t.2.1<4518 := by decide +kernel
#print axioms left201_support_compact

compact_certificate theorem left201_jet_support_compact : ∀ t ∈ left201,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left201_jet_support_compact

compact_certificate theorem right201_support_compact : ∀ t ∈ right201,t.2.1<4518 := by decide +kernel
#print axioms right201_support_compact

compact_certificate theorem lower201_operations_compact : lower201node18Ops=left201 := by decide +kernel
#print axioms lower201_operations_compact

compact_certificate theorem mixed201_operations_compact : mixed201node78Ops=left201 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right201) := by decide +kernel
#print axioms mixed201_operations_compact

compact_certificate theorem mixed201_result_compact : mixed201node78Result=result201 := by decide +kernel
#print axioms mixed201_result_compact

end QuantitativeArithmeticSmallLevelTwentyFive.OriginalFirstJet
}
end
