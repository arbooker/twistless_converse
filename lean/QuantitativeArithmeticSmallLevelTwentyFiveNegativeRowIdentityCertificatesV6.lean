module
public import QuantitativeArithmeticSmallLevelTwentyFiveNegativeNonzeroTwoRowsTheoryV4
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
namespace QuantitativeArithmeticSmallLevelTwentyFive.NegativeNonzeroTwoRows
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
certificate_batch {
compact_certificate theorem leading6_support_compact : ∀ t ∈ leading6node42Ops,t.2.1<4518 := by decide +kernel
#print axioms leading6_support_compact

compact_certificate theorem leading85_support_compact : ∀ t ∈ leading85node40Ops,t.2.1<4518 := by decide +kernel
#print axioms leading85_support_compact

compact_certificate theorem leading117_support_compact : ∀ t ∈ leading117node50Ops,t.2.1<4518 := by decide +kernel
#print axioms leading117_support_compact

compact_certificate theorem leading158_support_compact : ∀ t ∈ leading158node88Ops,t.2.1<4518 := by decide +kernel
#print axioms leading158_support_compact

compact_certificate theorem leading175_support_compact : ∀ t ∈ leading175node54Ops,t.2.1<4518 := by decide +kernel
#print axioms leading175_support_compact

compact_certificate theorem leading222_support_compact : ∀ t ∈ leading222node134Ops,t.2.1<4518 := by decide +kernel
#print axioms leading222_support_compact

compact_certificate theorem left85_support_compact : ∀ t ∈ left85,t.2.1<4518 := by decide +kernel
#print axioms left85_support_compact

compact_certificate theorem left85_jet_support_compact : ∀ t ∈ left85,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left85_jet_support_compact

compact_certificate theorem right85_support_compact : ∀ t ∈ right85,t.2.1<4518 := by decide +kernel
#print axioms right85_support_compact

compact_certificate theorem lower85_operations_compact : left85=lowerPoly leading85node40Ops := by decide +kernel
#print axioms lower85_operations_compact

compact_certificate theorem lower85_result_compact : lowerResult85=lowerPoly leading85node40Result := by decide +kernel
#print axioms lower85_result_compact

compact_certificate theorem mixed85_operations_compact : mixed85node84Ops=left85 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right85) := by decide +kernel
#print axioms mixed85_operations_compact

compact_certificate theorem mixed85_result_compact : mixed85node84Result=result85 := by decide +kernel
#print axioms mixed85_result_compact

compact_certificate theorem left117_support_compact : ∀ t ∈ left117,t.2.1<4518 := by decide +kernel
#print axioms left117_support_compact

compact_certificate theorem left117_jet_support_compact : ∀ t ∈ left117,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left117_jet_support_compact

compact_certificate theorem right117_support_compact : ∀ t ∈ right117,t.2.1<4518 := by decide +kernel
#print axioms right117_support_compact

compact_certificate theorem lower117_operations_compact : left117=lowerPoly leading117node50Ops := by decide +kernel
#print axioms lower117_operations_compact

compact_certificate theorem lower117_result_compact : lowerResult117=lowerPoly leading117node50Result := by decide +kernel
#print axioms lower117_result_compact

compact_certificate theorem mixed117_operations_compact : mixed117node110Ops=left117 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right117) := by decide +kernel
#print axioms mixed117_operations_compact

compact_certificate theorem mixed117_result_compact : mixed117node110Result=result117 := by decide +kernel
#print axioms mixed117_result_compact

compact_certificate theorem left158_support_compact : ∀ t ∈ left158,t.2.1<4518 := by decide +kernel
#print axioms left158_support_compact

compact_certificate theorem left158_jet_support_compact : ∀ t ∈ left158,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left158_jet_support_compact

compact_certificate theorem right158_support_compact : ∀ t ∈ right158,t.2.1<4518 := by decide +kernel
#print axioms right158_support_compact

compact_certificate theorem lower158_operations_compact : left158=lowerPoly leading158node88Ops := by decide +kernel
#print axioms lower158_operations_compact

compact_certificate theorem lower158_result_compact : lowerResult158=lowerPoly leading158node88Result := by decide +kernel
#print axioms lower158_result_compact

compact_certificate theorem mixed158_operations_compact : mixed158node180Ops=left158 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right158) := by decide +kernel
#print axioms mixed158_operations_compact

compact_certificate theorem mixed158_result_compact : mixed158node180Result=result158 := by decide +kernel
#print axioms mixed158_result_compact

compact_certificate theorem left175_support_compact : ∀ t ∈ left175,t.2.1<4518 := by decide +kernel
#print axioms left175_support_compact

compact_certificate theorem left175_jet_support_compact : ∀ t ∈ left175,t.2.1 ∈ jetIndices := by decide +kernel
#print axioms left175_jet_support_compact

compact_certificate theorem right175_support_compact : ∀ t ∈ right175,t.2.1<4518 := by decide +kernel
#print axioms right175_support_compact

compact_certificate theorem lower175_operations_compact : left175=lowerPoly leading175node54Ops := by decide +kernel
#print axioms lower175_operations_compact

compact_certificate theorem lower175_result_compact : lowerResult175=lowerPoly leading175node54Result := by decide +kernel
#print axioms lower175_result_compact

compact_certificate theorem mixed175_operations_compact : mixed175node112Ops=left175 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right175) := by decide +kernel
#print axioms mixed175_operations_compact

compact_certificate theorem mixed175_result_compact : mixed175node112Result=result175 := by decide +kernel
#print axioms mixed175_result_compact
}
end QuantitativeArithmeticSmallLevelTwentyFive.NegativeNonzeroTwoRows
end
