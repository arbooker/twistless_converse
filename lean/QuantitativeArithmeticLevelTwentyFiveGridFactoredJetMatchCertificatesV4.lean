module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveFactoredJetTheoryV4
public import QuantitativeArithmeticLevelTwentyFiveGridFirstJetCertificatesV4

set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

set_option Elab.async false

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## TwentyFiveFactoredJetMatch -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet
compact_certificate def commonIndices : List ℕ := [2,5,7,10,13,15,16,17,24,27,28,30,35,36,38,40,41,43,46,51,52,53,54,55,58,70,71,76,82,84,86,87,89,92,93,94,96,99,100,102,103,104,106,107,108,110,112,113,114,121,122,124,125,127,128,132,135,335,404,420,429,436,448,450,454,2513,2526,2527,2530,2532,2533,2537,2538,2568,2590,2598,2609,2610,2620,2621,2622,2625,2626,2627,2633,2731,2736,2737,2738,2761,2812,2813,2826,3221,3224,3227,3239,3240,3264,3290,3292,3306,3411,3415,3467,3509,3586,3590,3614,3649,3663,3761,3782,3790,3796,3824,4041,4306]
compact_certificate theorem common_match : ∀ i ∈ commonIndices,jetInput i=OriginalFirstJet.jetInput i := by decide +kernel
compact_certificate theorem common_support : ∀ i ∈ commonIndices,i ∈ OriginalFirstJet.jetIndices := by decide +kernel
compact_certificate theorem jet_match_33 : jetInput 33=OriginalCertificates.actualJet 33 := by decide +kernel
compact_certificate theorem jet_match_47 : jetInput 47=OriginalCertificates.actualJet 47 := by decide +kernel
compact_certificate theorem jet_match_49 : jetInput 49=OriginalCertificates.actualJet 49 := by decide +kernel
compact_certificate theorem jet_match_57 : jetInput 57=OriginalCertificates.actualJet 57 := by decide +kernel
compact_certificate theorem jet_match_60 : jetInput 60=OriginalCertificates.actualJet 60 := by decide +kernel
compact_certificate theorem jet_match_95 : jetInput 95=OriginalCertificates.actualJet 95 := by decide +kernel
compact_certificate theorem jet_match_126 : jetInput 126=OriginalCertificates.actualJet 126 := by decide +kernel
compact_certificate theorem jet_match_260 : jetInput 260=OriginalCertificates.actualJet 260 := by decide +kernel
compact_certificate theorem jet_match_342 : jetInput 342=OriginalCertificates.actualJet 342 := by decide +kernel
compact_certificate theorem jet_match_2539 : jetInput 2539=OriginalCertificates.actualJet 2539 := by decide +kernel
compact_certificate theorem jet_match_2540 : jetInput 2540=OriginalCertificates.actualJet 2540 := by decide +kernel
compact_certificate theorem jet_match_2764 : jetInput 2764=OriginalCertificates.actualJet 2764 := by decide +kernel
compact_certificate theorem jet_match_2934 : jetInput 2934=OriginalCertificates.actualJet 2934 := by decide +kernel
compact_certificate theorem jet_match_3017 : jetInput 3017=OriginalCertificates.actualJet 3017 := by decide +kernel
compact_certificate theorem jet_match_4441 : jetInput 4441=OriginalCertificates.actualJet 4441 := by decide +kernel
compact_certificate theorem jet_match (i : ℕ) (hi : i ∈ jetIndices) : jetInput i=OriginalCertificates.actualJet i := by
  by_cases hc : i ∈ commonIndices
  · exact (common_match i hc).trans (OriginalFirstJet.jet_match i (common_support i hc))
  have he : i ∈ [33,47,49,57,60,95,126,260,342,2539,2540,2764,2934,3017,4441] := by
    have hall : ∀ j ∈ jetIndices,j ∈ commonIndices ∨ j ∈ [33,47,49,57,60,95,126,260,342,2539,2540,2764,2934,3017,4441] := by decide +kernel
    exact (hall i hi).resolve_left hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact jet_match_33
  · exact jet_match_47
  · exact jet_match_49
  · exact jet_match_57
  · exact jet_match_60
  · exact jet_match_95
  · exact jet_match_126
  · exact jet_match_260
  · exact jet_match_342
  · exact jet_match_2539
  · exact jet_match_2540
  · exact jet_match_2764
  · exact jet_match_2934
  · exact jet_match_3017
  · exact jet_match_4441

#print axioms jet_match
end QuantitativeArithmeticSmallLevelTwentyFive.FactoredJet
end
end
