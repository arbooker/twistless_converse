module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveFactoredJetTheoryV4

set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

set_option Elab.async false

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## TwentyFiveFactoredJetIdentity -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
compact_certificate theorem left278_support : ∀ t ∈ left278,t.2.1<4518 := by decide +kernel
 theorem left278_jet_support : ∀ t ∈ left278,t.2.1 ∈ jetIndices := by decide +kernel
 theorem right278_support : ∀ t ∈ right278,t.2.1<4518 := by decide +kernel
 theorem lower278_operations : lower278node12Ops=left278 := by decide +kernel
 theorem lower278_result : lower278node12Result=lowerResult278 := by decide +kernel
 theorem mixed278_operations : mixed278node32Ops=left278 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right278) := by decide +kernel
 theorem mixed278_result : mixed278node32Result=result278 := by decide +kernel
compact_certificate theorem left226_support : ∀ t ∈ left226,t.2.1<4518 := by decide +kernel
 theorem left226_jet_support : ∀ t ∈ left226,t.2.1 ∈ jetIndices := by decide +kernel
 theorem right226_support : ∀ t ∈ right226,t.2.1<4518 := by decide +kernel
 theorem lower226_operations : lower226node14Ops=left226 := by decide +kernel
 theorem lower226_result : lower226node14Result=lowerResult226 := by decide +kernel
 theorem mixed226_operations : mixed226node38Ops=left226 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right226) := by decide +kernel
 theorem mixed226_result : mixed226node38Result=result226 := by decide +kernel
compact_certificate theorem left392_support : ∀ t ∈ left392,t.2.1<4518 := by decide +kernel
 theorem left392_jet_support : ∀ t ∈ left392,t.2.1 ∈ jetIndices := by decide +kernel
 theorem right392_support : ∀ t ∈ right392,t.2.1<4518 := by decide +kernel
 theorem lower392_operations : lower392node30Ops=left392 := by decide +kernel
 theorem lower392_result : lower392node30Result=lowerResult392 := by decide +kernel
 theorem mixed392_operations : mixed392node74Ops=left392 ++
    reindex (fun j => j+4518) (shift (-1) (0,0,0,0,0,0,0) right392) := by decide +kernel
 theorem mixed392_result : mixed392node74Result=result392 := by decide +kernel
end QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet
end
end

#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left278_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left278_jet_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.right278_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower278_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower278_result
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed278_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed278_result
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left226_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left226_jet_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.right226_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower226_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower226_result
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed226_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed226_result
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left392_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.left392_jet_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.right392_support
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower392_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.lower392_result
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed392_operations
#print axioms QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet.mixed392_result
