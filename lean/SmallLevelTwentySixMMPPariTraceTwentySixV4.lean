module
public import SmallLevelTwentySixMMPPariTraceTwentySixTablesV4
public import SmallLevelTwentySixMMPPariTraceIndexFamilyDataV4
public meta import SmallLevelPolynomialCertificateCommandsV4
public import SmallLevelPolynomialCoefficientCertificateTheoryV4
public import SmallLevelPolynomialZeroPrefixV1
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
section
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate

compact_certificate_declaration theorem inner_zero_0 (y z w b u : ℂ) : ∀ v∈innerCertificate0 y z w b u,v=0 := by
  apply zero_of_getElem? _ 14 (inner_length_0 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_0_0 y z w b u
  · exact coefficient_0_1 y z w b u
  · exact coefficient_0_2 y z w b u
  · exact coefficient_0_3 y z w b u
  · exact coefficient_0_4 y z w b u
  · exact coefficient_0_5 y z w b u
  · exact coefficient_0_6 y z w b u
  · exact coefficient_0_7 y z w b u
  · exact coefficient_0_8 y z w b u
  · exact coefficient_0_9 y z w b u
  · exact coefficient_0_10 y z w b u
  · exact coefficient_0_11 y z w b u
  · exact coefficient_0_12 y z w b u
  · exact coefficient_0_13 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 0 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_1 (y z w b u : ℂ) : ∀ v∈innerCertificate1 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_1 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_1_0 y z w b u
  · exact coefficient_1_1 y z w b u
  · exact coefficient_1_2 y z w b u
  · exact coefficient_1_3 y z w b u
  · exact coefficient_1_4 y z w b u
  · exact coefficient_1_5 y z w b u
  · exact coefficient_1_6 y z w b u
  · exact coefficient_1_7 y z w b u
  · exact coefficient_1_8 y z w b u
  · exact coefficient_1_9 y z w b u
  · exact coefficient_1_10 y z w b u
  · exact coefficient_1_11 y z w b u
  · exact coefficient_1_12 y z w b u
  · exact coefficient_1_13 y z w b u
  · exact coefficient_1_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 1 through 1 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_2 (y z w b u : ℂ) : ∀ v∈innerCertificate2 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_2 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_2_0 y z w b u
  · exact coefficient_2_1 y z w b u
  · exact coefficient_2_2 y z w b u
  · exact coefficient_2_3 y z w b u
  · exact coefficient_2_4 y z w b u
  · exact coefficient_2_5 y z w b u
  · exact coefficient_2_6 y z w b u
  · exact coefficient_2_7 y z w b u
  · exact coefficient_2_8 y z w b u
  · exact coefficient_2_9 y z w b u
  · exact coefficient_2_10 y z w b u
  · exact coefficient_2_11 y z w b u
  · exact coefficient_2_12 y z w b u
  · exact coefficient_2_13 y z w b u
  · exact coefficient_2_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 2 through 2 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_3 (y z w b u : ℂ) : ∀ v∈innerCertificate3 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_3 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_3_0 y z w b u
  · exact coefficient_3_1 y z w b u
  · exact coefficient_3_2 y z w b u
  · exact coefficient_3_3 y z w b u
  · exact coefficient_3_4 y z w b u
  · exact coefficient_3_5 y z w b u
  · exact coefficient_3_6 y z w b u
  · exact coefficient_3_7 y z w b u
  · exact coefficient_3_8 y z w b u
  · exact coefficient_3_9 y z w b u
  · exact coefficient_3_10 y z w b u
  · exact coefficient_3_11 y z w b u
  · exact coefficient_3_12 y z w b u
  · exact coefficient_3_13 y z w b u
  · exact coefficient_3_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 3 through 3 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_4 (y z w b u : ℂ) : ∀ v∈innerCertificate4 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_4 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_4_0 y z w b u
  · exact coefficient_4_1 y z w b u
  · exact coefficient_4_2 y z w b u
  · exact coefficient_4_3 y z w b u
  · exact coefficient_4_4 y z w b u
  · exact coefficient_4_5 y z w b u
  · exact coefficient_4_6 y z w b u
  · exact coefficient_4_7 y z w b u
  · exact coefficient_4_8 y z w b u
  · exact coefficient_4_9 y z w b u
  · exact coefficient_4_10 y z w b u
  · exact coefficient_4_11 y z w b u
  · exact coefficient_4_12 y z w b u
  · exact coefficient_4_13 y z w b u
  · exact coefficient_4_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 4 through 4 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_5 (y z w b u : ℂ) : ∀ v∈innerCertificate5 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_5 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_5_0 y z w b u
  · exact coefficient_5_1 y z w b u
  · exact coefficient_5_2 y z w b u
  · exact coefficient_5_3 y z w b u
  · exact coefficient_5_4 y z w b u
  · exact coefficient_5_5 y z w b u
  · exact coefficient_5_6 y z w b u
  · exact coefficient_5_7 y z w b u
  · exact coefficient_5_8 y z w b u
  · exact coefficient_5_9 y z w b u
  · exact coefficient_5_10 y z w b u
  · exact coefficient_5_11 y z w b u
  · exact coefficient_5_12 y z w b u
  · exact coefficient_5_13 y z w b u
  · exact coefficient_5_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 5 through 5 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_6 (y z w b u : ℂ) : ∀ v∈innerCertificate6 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_6 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_6_0 y z w b u
  · exact coefficient_6_1 y z w b u
  · exact coefficient_6_2 y z w b u
  · exact coefficient_6_3 y z w b u
  · exact coefficient_6_4 y z w b u
  · exact coefficient_6_5 y z w b u
  · exact coefficient_6_6 y z w b u
  · exact coefficient_6_7 y z w b u
  · exact coefficient_6_8 y z w b u
  · exact coefficient_6_9 y z w b u
  · exact coefficient_6_10 y z w b u
  · exact coefficient_6_11 y z w b u
  · exact coefficient_6_12 y z w b u
  · exact coefficient_6_13 y z w b u
  · exact coefficient_6_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 6 through 6 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_7 (y z w b u : ℂ) : ∀ v∈innerCertificate7 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_7 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_7_0 y z w b u
  · exact coefficient_7_1 y z w b u
  · exact coefficient_7_2 y z w b u
  · exact coefficient_7_3 y z w b u
  · exact coefficient_7_4 y z w b u
  · exact coefficient_7_5 y z w b u
  · exact coefficient_7_6 y z w b u
  · exact coefficient_7_7 y z w b u
  · exact coefficient_7_8 y z w b u
  · exact coefficient_7_9 y z w b u
  · exact coefficient_7_10 y z w b u
  · exact coefficient_7_11 y z w b u
  · exact coefficient_7_12 y z w b u
  · exact coefficient_7_13 y z w b u
  · exact coefficient_7_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 7 through 7 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_8 (y z w b u : ℂ) : ∀ v∈innerCertificate8 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_8 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_8_0 y z w b u
  · exact coefficient_8_1 y z w b u
  · exact coefficient_8_2 y z w b u
  · exact coefficient_8_3 y z w b u
  · exact coefficient_8_4 y z w b u
  · exact coefficient_8_5 y z w b u
  · exact coefficient_8_6 y z w b u
  · exact coefficient_8_7 y z w b u
  · exact coefficient_8_8 y z w b u
  · exact coefficient_8_9 y z w b u
  · exact coefficient_8_10 y z w b u
  · exact coefficient_8_11 y z w b u
  · exact coefficient_8_12 y z w b u
  · exact coefficient_8_13 y z w b u
  · exact coefficient_8_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 8 through 8 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_9 (y z w b u : ℂ) : ∀ v∈innerCertificate9 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_9 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_9_0 y z w b u
  · exact coefficient_9_1 y z w b u
  · exact coefficient_9_2 y z w b u
  · exact coefficient_9_3 y z w b u
  · exact coefficient_9_4 y z w b u
  · exact coefficient_9_5 y z w b u
  · exact coefficient_9_6 y z w b u
  · exact coefficient_9_7 y z w b u
  · exact coefficient_9_8 y z w b u
  · exact coefficient_9_9 y z w b u
  · exact coefficient_9_10 y z w b u
  · exact coefficient_9_11 y z w b u
  · exact coefficient_9_12 y z w b u
  · exact coefficient_9_13 y z w b u
  · exact coefficient_9_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 9 through 9 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_10 (y z w b u : ℂ) : ∀ v∈innerCertificate10 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_10 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_10_0 y z w b u
  · exact coefficient_10_1 y z w b u
  · exact coefficient_10_2 y z w b u
  · exact coefficient_10_3 y z w b u
  · exact coefficient_10_4 y z w b u
  · exact coefficient_10_5 y z w b u
  · exact coefficient_10_6 y z w b u
  · exact coefficient_10_7 y z w b u
  · exact coefficient_10_8 y z w b u
  · exact coefficient_10_9 y z w b u
  · exact coefficient_10_10 y z w b u
  · exact coefficient_10_11 y z w b u
  · exact coefficient_10_12 y z w b u
  · exact coefficient_10_13 y z w b u
  · exact coefficient_10_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 10 through 10 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_11 (y z w b u : ℂ) : ∀ v∈innerCertificate11 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_11 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_11_0 y z w b u
  · exact coefficient_11_1 y z w b u
  · exact coefficient_11_2 y z w b u
  · exact coefficient_11_3 y z w b u
  · exact coefficient_11_4 y z w b u
  · exact coefficient_11_5 y z w b u
  · exact coefficient_11_6 y z w b u
  · exact coefficient_11_7 y z w b u
  · exact coefficient_11_8 y z w b u
  · exact coefficient_11_9 y z w b u
  · exact coefficient_11_10 y z w b u
  · exact coefficient_11_11 y z w b u
  · exact coefficient_11_12 y z w b u
  · exact coefficient_11_13 y z w b u
  · exact coefficient_11_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 11 through 11 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_12 (y z w b u : ℂ) : ∀ v∈innerCertificate12 y z w b u,v=0 := by
  apply zero_of_getElem? _ 15 (inner_length_12 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_12_0 y z w b u
  · exact coefficient_12_1 y z w b u
  · exact coefficient_12_2 y z w b u
  · exact coefficient_12_3 y z w b u
  · exact coefficient_12_4 y z w b u
  · exact coefficient_12_5 y z w b u
  · exact coefficient_12_6 y z w b u
  · exact coefficient_12_7 y z w b u
  · exact coefficient_12_8 y z w b u
  · exact coefficient_12_9 y z w b u
  · exact coefficient_12_10 y z w b u
  · exact coefficient_12_11 y z w b u
  · exact coefficient_12_12 y z w b u
  · exact coefficient_12_13 y z w b u
  · exact coefficient_12_14 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 12 through 12 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_13 (y z w b u : ℂ) : ∀ v∈innerCertificate13 y z w b u,v=0 := by
  apply zero_of_getElem? _ 14 (inner_length_13 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_13_0 y z w b u
  · exact coefficient_13_1 y z w b u
  · exact coefficient_13_2 y z w b u
  · exact coefficient_13_3 y z w b u
  · exact coefficient_13_4 y z w b u
  · exact coefficient_13_5 y z w b u
  · exact coefficient_13_6 y z w b u
  · exact coefficient_13_7 y z w b u
  · exact coefficient_13_8 y z w b u
  · exact coefficient_13_9 y z w b u
  · exact coefficient_13_10 y z w b u
  · exact coefficient_13_11 y z w b u
  · exact coefficient_13_12 y z w b u
  · exact coefficient_13_13 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 13 through 13 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_14 (y z w b u : ℂ) : ∀ v∈innerCertificate14 y z w b u,v=0 := by
  apply zero_of_getElem? _ 14 (inner_length_14 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_14_0 y z w b u
  · exact coefficient_14_1 y z w b u
  · exact coefficient_14_2 y z w b u
  · exact coefficient_14_3 y z w b u
  · exact coefficient_14_4 y z w b u
  · exact coefficient_14_5 y z w b u
  · exact coefficient_14_6 y z w b u
  · exact coefficient_14_7 y z w b u
  · exact coefficient_14_8 y z w b u
  · exact coefficient_14_9 y z w b u
  · exact coefficient_14_10 y z w b u
  · exact coefficient_14_11 y z w b u
  · exact coefficient_14_12 y z w b u
  · exact coefficient_14_13 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 14 through 14 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_15 (y z w b u : ℂ) : ∀ v∈innerCertificate15 y z w b u,v=0 := by
  apply zero_of_getElem? _ 13 (inner_length_15 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_15_0 y z w b u
  · exact coefficient_15_1 y z w b u
  · exact coefficient_15_2 y z w b u
  · exact coefficient_15_3 y z w b u
  · exact coefficient_15_4 y z w b u
  · exact coefficient_15_5 y z w b u
  · exact coefficient_15_6 y z w b u
  · exact coefficient_15_7 y z w b u
  · exact coefficient_15_8 y z w b u
  · exact coefficient_15_9 y z w b u
  · exact coefficient_15_10 y z w b u
  · exact coefficient_15_11 y z w b u
  · exact coefficient_15_12 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 15 through 15 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_16 (y z w b u : ℂ) : ∀ v∈innerCertificate16 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_16 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_16_0 y z w b u
  · exact coefficient_16_1 y z w b u
  · exact coefficient_16_2 y z w b u
  · exact coefficient_16_3 y z w b u
  · exact coefficient_16_4 y z w b u
  · exact coefficient_16_5 y z w b u
  · exact coefficient_16_6 y z w b u
  · exact coefficient_16_7 y z w b u
  · exact coefficient_16_8 y z w b u
  · exact coefficient_16_9 y z w b u
  · exact coefficient_16_10 y z w b u
  · exact coefficient_16_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 16 through 16 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_17 (y z w b u : ℂ) : ∀ v∈innerCertificate17 y z w b u,v=0 := by
  apply zero_of_getElem? _ 12 (inner_length_17 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_17_0 y z w b u
  · exact coefficient_17_1 y z w b u
  · exact coefficient_17_2 y z w b u
  · exact coefficient_17_3 y z w b u
  · exact coefficient_17_4 y z w b u
  · exact coefficient_17_5 y z w b u
  · exact coefficient_17_6 y z w b u
  · exact coefficient_17_7 y z w b u
  · exact coefficient_17_8 y z w b u
  · exact coefficient_17_9 y z w b u
  · exact coefficient_17_10 y z w b u
  · exact coefficient_17_11 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 17 through 17 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_18 (y z w b u : ℂ) : ∀ v∈innerCertificate18 y z w b u,v=0 := by
  apply zero_of_getElem? _ 11 (inner_length_18 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_18_0 y z w b u
  · exact coefficient_18_1 y z w b u
  · exact coefficient_18_2 y z w b u
  · exact coefficient_18_3 y z w b u
  · exact coefficient_18_4 y z w b u
  · exact coefficient_18_5 y z w b u
  · exact coefficient_18_6 y z w b u
  · exact coefficient_18_7 y z w b u
  · exact coefficient_18_8 y z w b u
  · exact coefficient_18_9 y z w b u
  · exact coefficient_18_10 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 18 through 18 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_19 (y z w b u : ℂ) : ∀ v∈innerCertificate19 y z w b u,v=0 := by
  apply zero_of_getElem? _ 11 (inner_length_19 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_19_0 y z w b u
  · exact coefficient_19_1 y z w b u
  · exact coefficient_19_2 y z w b u
  · exact coefficient_19_3 y z w b u
  · exact coefficient_19_4 y z w b u
  · exact coefficient_19_5 y z w b u
  · exact coefficient_19_6 y z w b u
  · exact coefficient_19_7 y z w b u
  · exact coefficient_19_8 y z w b u
  · exact coefficient_19_9 y z w b u
  · exact coefficient_19_10 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 19 through 19 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_20 (y z w b u : ℂ) : ∀ v∈innerCertificate20 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_20 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_20_0 y z w b u
  · exact coefficient_20_1 y z w b u
  · exact coefficient_20_2 y z w b u
  · exact coefficient_20_3 y z w b u
  · exact coefficient_20_4 y z w b u
  · exact coefficient_20_5 y z w b u
  · exact coefficient_20_6 y z w b u
  · exact coefficient_20_7 y z w b u
  · exact coefficient_20_8 y z w b u
  · exact coefficient_20_9 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 20 through 20 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_21 (y z w b u : ℂ) : ∀ v∈innerCertificate21 y z w b u,v=0 := by
  apply zero_of_getElem? _ 10 (inner_length_21 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_21_0 y z w b u
  · exact coefficient_21_1 y z w b u
  · exact coefficient_21_2 y z w b u
  · exact coefficient_21_3 y z w b u
  · exact coefficient_21_4 y z w b u
  · exact coefficient_21_5 y z w b u
  · exact coefficient_21_6 y z w b u
  · exact coefficient_21_7 y z w b u
  · exact coefficient_21_8 y z w b u
  · exact coefficient_21_9 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 21 through 21 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_22 (y z w b u : ℂ) : ∀ v∈innerCertificate22 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_22 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_22_0 y z w b u
  · exact coefficient_22_1 y z w b u
  · exact coefficient_22_2 y z w b u
  · exact coefficient_22_3 y z w b u
  · exact coefficient_22_4 y z w b u
  · exact coefficient_22_5 y z w b u
  · exact coefficient_22_6 y z w b u
  · exact coefficient_22_7 y z w b u
  · exact coefficient_22_8 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 22 through 22 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_23 (y z w b u : ℂ) : ∀ v∈innerCertificate23 y z w b u,v=0 := by
  apply zero_of_getElem? _ 9 (inner_length_23 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_23_0 y z w b u
  · exact coefficient_23_1 y z w b u
  · exact coefficient_23_2 y z w b u
  · exact coefficient_23_3 y z w b u
  · exact coefficient_23_4 y z w b u
  · exact coefficient_23_5 y z w b u
  · exact coefficient_23_6 y z w b u
  · exact coefficient_23_7 y z w b u
  · exact coefficient_23_8 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 23 through 23 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_24 (y z w b u : ℂ) : ∀ v∈innerCertificate24 y z w b u,v=0 := by
  apply zero_of_getElem? _ 8 (inner_length_24 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_24_0 y z w b u
  · exact coefficient_24_1 y z w b u
  · exact coefficient_24_2 y z w b u
  · exact coefficient_24_3 y z w b u
  · exact coefficient_24_4 y z w b u
  · exact coefficient_24_5 y z w b u
  · exact coefficient_24_6 y z w b u
  · exact coefficient_24_7 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 24 through 24 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_25 (y z w b u : ℂ) : ∀ v∈innerCertificate25 y z w b u,v=0 := by
  apply zero_of_getElem? _ 7 (inner_length_25 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_25_0 y z w b u
  · exact coefficient_25_1 y z w b u
  · exact coefficient_25_2 y z w b u
  · exact coefficient_25_3 y z w b u
  · exact coefficient_25_4 y z w b u
  · exact coefficient_25_5 y z w b u
  · exact coefficient_25_6 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 25 through 25 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_26 (y z w b u : ℂ) : ∀ v∈innerCertificate26 y z w b u,v=0 := by
  apply zero_of_getElem? _ 6 (inner_length_26 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_26_0 y z w b u
  · exact coefficient_26_1 y z w b u
  · exact coefficient_26_2 y z w b u
  · exact coefficient_26_3 y z w b u
  · exact coefficient_26_4 y z w b u
  · exact coefficient_26_5 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 26 through 26 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_27 (y z w b u : ℂ) : ∀ v∈innerCertificate27 y z w b u,v=0 := by
  apply zero_of_getElem? _ 5 (inner_length_27 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_27_0 y z w b u
  · exact coefficient_27_1 y z w b u
  · exact coefficient_27_2 y z w b u
  · exact coefficient_27_3 y z w b u
  · exact coefficient_27_4 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 27 through 27 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_28 (y z w b u : ℂ) : ∀ v∈innerCertificate28 y z w b u,v=0 := by
  apply zero_of_getElem? _ 4 (inner_length_28 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_28_0 y z w b u
  · exact coefficient_28_1 y z w b u
  · exact coefficient_28_2 y z w b u
  · exact coefficient_28_3 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 28 through 28 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_29 (y z w b u : ℂ) : ∀ v∈innerCertificate29 y z w b u,v=0 := by
  apply zero_of_getElem? _ 3 (inner_length_29 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_29_0 y z w b u
  · exact coefficient_29_1 y z w b u
  · exact coefficient_29_2 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 29 through 29 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_30 (y z w b u : ℂ) : ∀ v∈innerCertificate30 y z w b u,v=0 := by
  apply zero_of_getElem? _ 2 (inner_length_30 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_30_0 y z w b u
  · exact coefficient_30_1 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 30 through 30 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

compact_certificate_declaration theorem inner_zero_31 (y z w b u : ℂ) : ∀ v∈innerCertificate31 y z w b u,v=0 := by
  apply zero_of_getElem? _ 1 (inner_length_31 y z w b u)
  intro i
  fin_cases i
  · exact coefficient_31_0 y z w b u
certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 31 through 31 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, coefficients0, c1_0, c1_1, c1_2, c1_3, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace026
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace026
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 32 (certificate_length y z w a b u)
  intro i
  fin_cases i
  · exact coefficient_0 y z w a b u
  · exact coefficient_1 y z w a b u
  · exact coefficient_2 y z w a b u
  · exact coefficient_3 y z w a b u
  · exact coefficient_4 y z w a b u
  · exact coefficient_5 y z w a b u
  · exact coefficient_6 y z w a b u
  · exact coefficient_7 y z w a b u
  · exact coefficient_8 y z w a b u
  · exact coefficient_9 y z w a b u
  · exact coefficient_10 y z w a b u
  · exact coefficient_11 y z w a b u
  · exact coefficient_12 y z w a b u
  · exact coefficient_13 y z w a b u
  · exact coefficient_14 y z w a b u
  · exact coefficient_15 y z w a b u
  · exact coefficient_16 y z w a b u
  · exact coefficient_17 y z w a b u
  · exact coefficient_18 y z w a b u
  · exact coefficient_19 y z w a b u
  · exact coefficient_20 y z w a b u
  · exact coefficient_21 y z w a b u
  · exact coefficient_22 y z w a b u
  · exact coefficient_23 y z w a b u
  · exact coefficient_24 y z w a b u
  · exact coefficient_25 y z w a b u
  · exact coefficient_26 y z w a b u
  · exact coefficient_27 y z w a b u
  · exact coefficient_28 y z w a b u
  · exact coefficient_29 y z w a b u
  · exact coefficient_30 y z w a b u
  · exact coefficient_31 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace026
end
end
