module
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusKernelChecksChapterV1

public import QuantitativeArithmeticFiniteRangeCertificatesV1
public import QuantitativeArithmeticListBoundsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridDataTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModelTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public meta import QuantitativeArithmeticCompactCommandsV1
public meta import QuantitativeArithmeticCompactFactCommandsV1
public meta import QuantitativeArithmeticFiniteRangeCommandsV4

-- These editor-information linters are incompatible with compact_certificate.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusActualRowsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel

compact_certificate theorem all_actual_source (j : Fin 4600) :
    normalizedPoly (rawSourcePoly 1 (actual j.val))=source j.val := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawSourcePoly 1 (actual i))=source i
  have h : ∀ i<4600, P (i+0) := (finite_range% P 0 [
    384 => actual_source_chunk0,
    384 => actual_source_chunk1,
    384 => actual_source_chunk2,
    384 => actual_source_chunk3,
    384 => actual_source_chunk4,
    384 => actual_source_chunk5,
    384 => actual_source_chunk6,
    384 => actual_source_chunk7,
    384 => actual_source_chunk8,
    384 => actual_source_chunk9,
    384 => actual_source_chunk10,
    376 => actual_source_chunk11
  ])
  exact h j.val j.isLt
#print axioms all_actual_source
compact_certificate theorem all_actual_tail (j : Fin 4600) :
    normalizedPoly (rawTailPoly (actual j.val))=tail j.val := by
  let P : ℕ → Prop := fun i => normalizedPoly (rawTailPoly (actual i))=tail i
  have h : ∀ i<4600, P (i+0) := (finite_range% P 0 [
    384 => actual_tail_chunk0,
    384 => actual_tail_chunk1,
    384 => actual_tail_chunk2,
    384 => actual_tail_chunk3,
    384 => actual_tail_chunk4,
    384 => actual_tail_chunk5,
    384 => actual_tail_chunk6,
    384 => actual_tail_chunk7,
    384 => actual_tail_chunk8,
    384 => actual_tail_chunk9,
    384 => actual_tail_chunk10,
    376 => actual_tail_chunk11
  ])
  exact h j.val j.isLt
#print axioms all_actual_tail
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentBasisCertificateV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate theorem all_source_zero (i : Fin 4600) : substitute basis (source i.val)=[] := by
  let P : ℕ → Prop := fun j => substitute basis (source j)=[]
  have h : ∀ j<4600, P (j+0) := (finite_range% P 0 [
    32 => (fun i hi => source_zero_0 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_1 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_2 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_3 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_4 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_5 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_6 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_7 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_8 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_9 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_10 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_11 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_12 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_13 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_14 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_15 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_16 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_17 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_18 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_19 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_20 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_21 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_22 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_23 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_24 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_25 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_26 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_27 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_28 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_29 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_30 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_31 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_32 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_33 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_34 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_35 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_36 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_37 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_38 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_39 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_40 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_41 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_42 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_43 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_44 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_45 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_46 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_47 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_48 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_49 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_50 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_51 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_52 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_53 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_54 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_55 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_56 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_57 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_58 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_59 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_60 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_61 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_62 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_63 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_64 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_65 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_66 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_67 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_68 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_69 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_70 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_71 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_72 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_73 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_74 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_75 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_76 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_77 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_78 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_79 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_80 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_81 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_82 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_83 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_84 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_85 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_86 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_87 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_88 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_89 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_90 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_91 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_92 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_93 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_94 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_95 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_96 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_97 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_98 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_99 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_100 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_101 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_102 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_103 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_104 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_105 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_106 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_107 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_108 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_109 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_110 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_111 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_112 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_113 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_114 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_115 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_116 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_117 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_118 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_119 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_120 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_121 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_122 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_123 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_124 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_125 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_126 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_127 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_128 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_129 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_130 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_131 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_132 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_133 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_134 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_135 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_136 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_137 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_138 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_139 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_140 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_141 ⟨i,hi⟩),
    32 => (fun i hi => source_zero_142 ⟨i,hi⟩),
    24 => (fun i hi => source_zero_143 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h i.val i.isLt

compact_certificate theorem eval_source_zero (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (i : Fin 4600) :
    eval x y z w a b c (fun j => eval x y z w a b c v (basis j)) (source i.val)=0 :=
  substitution_zero x y z w a b c v hx hy hz hw basis (source i.val) (all_source_zero i)
#print axioms all_source_zero
#print axioms eval_source_zero
compact_certificate theorem all_tail_zero (i : Fin 4600) : substitute basis (tail i.val)=[] := by
  let P : ℕ → Prop := fun j => substitute basis (tail j)=[]
  have h : ∀ j<4600, P (j+0) := (finite_range% P 0 [
    32 => (fun i hi => tail_zero_0 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_1 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_2 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_3 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_4 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_5 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_6 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_7 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_8 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_9 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_10 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_11 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_12 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_13 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_14 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_15 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_16 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_17 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_18 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_19 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_20 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_21 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_22 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_23 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_24 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_25 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_26 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_27 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_28 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_29 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_30 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_31 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_32 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_33 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_34 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_35 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_36 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_37 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_38 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_39 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_40 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_41 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_42 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_43 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_44 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_45 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_46 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_47 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_48 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_49 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_50 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_51 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_52 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_53 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_54 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_55 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_56 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_57 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_58 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_59 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_60 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_61 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_62 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_63 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_64 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_65 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_66 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_67 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_68 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_69 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_70 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_71 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_72 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_73 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_74 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_75 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_76 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_77 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_78 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_79 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_80 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_81 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_82 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_83 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_84 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_85 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_86 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_87 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_88 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_89 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_90 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_91 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_92 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_93 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_94 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_95 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_96 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_97 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_98 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_99 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_100 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_101 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_102 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_103 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_104 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_105 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_106 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_107 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_108 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_109 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_110 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_111 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_112 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_113 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_114 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_115 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_116 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_117 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_118 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_119 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_120 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_121 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_122 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_123 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_124 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_125 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_126 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_127 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_128 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_129 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_130 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_131 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_132 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_133 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_134 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_135 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_136 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_137 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_138 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_139 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_140 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_141 ⟨i,hi⟩),
    32 => (fun i hi => tail_zero_142 ⟨i,hi⟩),
    24 => (fun i hi => tail_zero_143 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h i.val i.isLt

compact_certificate theorem eval_tail_zero (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0) (i : Fin 4600) :
    eval x y z w a b c (fun j => eval x y z w a b c v (basis j)) (tail i.val)=0 :=
  substitution_zero x y z w a b c v hx hy hz hw basis (tail i.val) (all_tail_zero i)
#print axioms all_tail_zero
#print axioms eval_tail_zero
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelOperationsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_operations_checked : ∀ i<982, substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i := by
  let P : ℕ → Prop := fun i => substitute (fun j => if j<4600 then source j else normal (j-4600)) (operations i)=normal i
  have h : ∀ i<982, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => operations_checked_0 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_1 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_2 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_3 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_4 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_5 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_6 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_7 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_8 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_9 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_10 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_11 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_12 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_13 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_14 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_15 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_16 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_17 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_18 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_19 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_20 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_21 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_22 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_23 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_24 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_25 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_26 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_27 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_28 ⟨i,hi⟩),
    32 => (fun i hi => operations_checked_29 ⟨i,hi⟩),
    22 => (fun i hi => operations_checked_30 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_operations_checked
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelPriorV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_operations_prior : ∀ i<982, ∀ t ∈ operations i, t.2.1<4600+i := by
  let P : ℕ → Prop := fun i => ∀ t ∈ operations i, t.2.1<4600+i
  have h : ∀ i<982, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => operations_prior_0 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_1 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_2 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_3 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_4 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_5 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_6 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_7 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_8 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_9 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_10 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_11 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_12 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_13 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_14 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_15 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_16 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_17 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_18 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_19 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_20 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_21 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_22 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_23 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_24 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_25 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_26 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_27 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_28 ⟨i,hi⟩),
    32 => (fun i hi => operations_prior_29 ⟨i,hi⟩),
    22 => (fun i hi => operations_prior_30 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_operations_prior
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelTriangularV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_triangular_checked : ∀ i<1050, mergeFuel 20000 [(1,coordinate i,(0,0,0,0,0,0,0))] (triTail i)=normal i := by
  let P : ℕ → Prop := fun i => mergeFuel 20000 [(1,coordinate i,(0,0,0,0,0,0,0))] (triTail i)=normal i
  have h : ∀ i<1050, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => triangular_checked_0 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_1 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_2 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_3 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_4 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_5 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_6 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_7 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_8 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_9 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_10 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_11 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_12 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_13 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_14 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_15 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_16 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_17 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_18 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_19 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_20 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_21 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_22 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_23 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_24 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_25 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_26 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_27 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_28 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_29 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_30 ⟨i,hi⟩),
    32 => (fun i hi => triangular_checked_31 ⟨i,hi⟩),
    26 => (fun i hi => triangular_checked_32 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_triangular_checked
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelTriangularPriorV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem all_triangular_prior : ∀ i<1050, ∀ t ∈ triTail i, t.2.1<1050 ∧ i<position t.2.1 := by
  let P : ℕ → Prop := fun i => ∀ t ∈ triTail i, t.2.1<1050 ∧ i<position t.2.1
  have h : ∀ i<1050, P (i+0) :=
    (finite_range% P 0 [
    32 => (fun i hi => triangular_prior_0 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_1 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_2 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_3 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_4 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_5 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_6 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_7 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_8 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_9 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_10 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_11 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_12 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_13 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_14 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_15 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_16 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_17 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_18 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_19 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_20 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_21 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_22 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_23 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_24 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_25 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_26 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_27 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_28 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_29 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_30 ⟨i,hi⟩),
    32 => (fun i hi => triangular_prior_31 ⟨i,hi⟩),
    26 => (fun i hi => triangular_prior_32 ⟨i,hi⟩)
  ])
  simpa only [Nat.add_zero] using h


#print axioms all_triangular_prior
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelCoordinatesBoundV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem coordinate_bound : ∀ i : Fin 1050, coordinate i.val<1050 := by
  have h : ∀ x∈coordinates, x<1050 := by decide +kernel
  intro i
  exact QuantitativeArithmeticListBounds.getD_of_forall (fun x : ℕ => x<1050) 0
    (by decide) coordinates h i.val

#print axioms coordinate_bound
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelPositionsBoundV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem position_bound : ∀ i : Fin 1050, position i.val<1050 := by
  have h : ∀ x∈positions, x<1050 := by decide +kernel
  intro i
  exact QuantitativeArithmeticListBounds.getD_of_forall (fun x : ℕ => x<1050) 0
    (by decide) positions h i.val

#print axioms position_bound
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelCoordinatesInverseV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem coordinate_position : ∀ i : Fin 1050, coordinate (position i.val)=i.val := by
  let P : ℕ → Prop := fun i => coordinate (position i)=i
  have h : ∀ i<1050, P (i+0) := (finite_range% P 0 [
    32 => (fun i hi => coordinate_position_part0 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part1 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part2 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part3 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part4 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part5 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part6 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part7 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part8 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part9 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part10 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part11 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part12 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part13 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part14 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part15 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part16 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part17 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part18 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part19 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part20 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part21 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part22 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part23 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part24 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part25 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part26 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part27 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part28 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part29 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part30 ⟨i,hi⟩),
    32 => (fun i hi => coordinate_position_part31 ⟨i,hi⟩),
    26 => (fun i hi => coordinate_position_part32 ⟨i,hi⟩)
  ])
  exact fun i => h i.val i.isLt
#print axioms coordinate_position
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelFreeRowsV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem free_rows : ∀ i : Fin 68,
    normal (i.val+982)=[(1,coordinate (i.val+982),(0,0,0,0,0,0,0))] := by decide +kernel


#print axioms free_rows
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentKernelCertificateV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem augmented_kernel (x y z w a b c : ℂ) (v : ℕ → ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hs : ∀ j<4600, eval x y z w a b c v (source j)=0)
    (hf : ∀ j : Fin 68, v (coordinate (j.val+982))=0) :
    ∀ j<1050, v j=0 := by
  have hn := forward_elimination x y z w a b c v hx hy hz hw 4600 982
    source normal operations all_operations_checked all_operations_prior hs
  have hnormal : ∀ i<1050, eval x y z w a b c v (normal i)=0 := by
    intro i hi
    by_cases h : i<982
    · exact hn i h
    · have he : i-982+982=i := by omega
      have hh := free_rows ⟨i-982,by omega⟩
      dsimp only at hh
      rw [he] at hh
      rw [hh]
      simpa [eval,monomial,he] using hf ⟨i-982,by omega⟩
  have ht : ∀ i : Fin 1050, v (coordinate i.val)+eval x y z w a b c v (triTail i.val)=0 := by
    intro i
    have hh := hnormal i.val i.isLt
    rw [← all_triangular_checked i.val i.isLt,eval_mergeFuel] at hh
    simpa [eval,monomial] using hh
  have hzall := triangular_kernel x y z w a b c v 1050
    (fun i => coordinate i.val) (fun i => triTail i.val) ht (by
      intro i t ht
      obtain ⟨hbound,higher⟩ := all_triangular_prior i.val i.isLt t ht
      refine ⟨⟨position t.2.1,position_bound ⟨t.2.1,hbound⟩⟩,higher,?_⟩
      exact (coordinate_position ⟨t.2.1,hbound⟩).symm)
  intro j hj
  have hh := hzall ⟨position j,position_bound ⟨j,hj⟩⟩
  simpa only [coordinate_position ⟨j,hj⟩] using hh
#print axioms augmented_kernel
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusLaurentGaugeCoordinatesV1 -/
section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open QuantitativeArithmeticSevenLaurentRows

compact_certificate theorem basis_free_coordinate : ∀ i : Fin 68,
    basis (coordinate (i.val+982))=[(1,i.val,(0,0,0,0,0,0,0))] := by decide +kernel

compact_certificate theorem basis_old_coordinate : ∀ i : Fin 150, basis (7*i.val)=[] := by decide +kernel

#print axioms basis_free_coordinate
#print axioms basis_old_coordinate
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxPlusContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

compact_certificate def freeCoordinate (j : Fin 68) : Fin 1050 :=
  ⟨coordinate (j.val+982),coordinate_bound ⟨j.val+982,by omega⟩⟩

compact_certificate theorem actual_augmented_kernel {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε s : ℂ) (hχ : ε*I^(2*m)=1) (v : Fin 1050 → ℂ)
    (hs : ∀ i : Fin 4600, sourceLeading (actual i.val) m f ε s v=0)
    (hfree : ∀ j : Fin 68, v (freeCoordinate j)=0) : v=0 := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p m s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  have phase : ε*I^(2*m)=((1:ℚ):ℂ) := by simpa using hχ
  have hk := augmented_kernel (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
    (periodicVector v) (hp 2 (by decide)) (hp 3 (by decide)) (hp 5 (by decide)) (hp 7 (by decide))
    (by
      intro i hi
      have he := eval_rawSourcePoly (actual i) hf ε s (1:ℚ) phase v
      rw [← eval_normalizedPoly _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
        (hp 5 (by decide)) (hp 7 (by decide)),all_actual_source ⟨i,hi⟩] at he
      exact he.trans (hs ⟨i,hi⟩))
    (by
      intro j
      change periodicVector v (freeCoordinate j).val=0
      rw [periodicVector_fin]
      exact hfree j)
  funext j
  simpa only [periodicVector_fin,Pi.zero_apply] using hk j.val j.isLt

/- Auxiliary continuation from the original Euler/Fricke input and the
already continued 150-grid; the free auxiliary twists are not continued. -/
compact_certificate theorem original_auxiliary_continuation {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=1)
    (BG : ℝ) (G0 : ℂ → Fin 150 → ℂ)
    (hG0 : ∀ j z, MeromorphicAt (fun w => G0 w j) z)
    (hG0F : ∀ z, BG<z.re → G0 z=QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z) :
    ∃ (B : ℝ) (G : ℂ → Fin 1050 → ℂ),
      (∀ j z, MeromorphicNFAt (fun w => G w j) z) ∧
      (∀ z, B<z.re → G z=physicalGauge basis freeCoordinate m f z (gridVector 1050 (2*m) f z)) ∧
      ∀ z, B<z.re → ∀ j : Fin 150, G z ⟨7*j.val,by omega⟩=
        QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z j := by
  apply quotient_continuation_of_certificates (fun i : Fin 4600 => actual i.val)
    freeCoordinate basis (fun i => source i.val) (fun i => tail i.val) (1:ℚ)
    basis_periodic (fun j => basis_free_coordinate j) basis_old_coordinate
    all_actual_source all_actual_tail all_source_zero all_tail_zero
    hm hf ε hε hlaw (by simpa using hχ)
    (fun s v hs hfree => actual_augmented_kernel hf ε s hχ v hs hfree)
    BG G0 hG0 hG0F

#print axioms actual_augmented_kernel
#print axioms original_auxiliary_continuation
end QuantitativeArithmeticSmallLevelTwentyFive.AuxPlusLaurent
end
end
end
