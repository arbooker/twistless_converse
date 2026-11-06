module
public import SmallLevelTwentySixMMPPariTraceTranslatedV4
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
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace032
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=164 := by
  norm_num [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace032
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace032
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 163 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, c0_32, c0_33, c0_34, c0_35, c0_36, c0_37, c0_38, c0_39, c0_40, c0_41, c0_42, c0_43, c0_44, c0_45, c0_46, c0_47, c0_48, c0_49, c0_50, c0_51, c0_52, c0_53, c0_54, c0_55, c0_56, c0_57, c0_58, c0_59, c0_60, c0_61, c0_62, c0_63, c0_64, c0_65, c0_66, c0_67, c0_68, c0_69, c0_70, c0_71, c0_72, c0_73, c0_74, c0_75, c0_76, c0_77, c0_78, c0_79, c0_80, c0_81, c0_82, c0_83, c0_84, c0_85, c0_86, c0_87, c0_88, c0_89, c0_90, c0_91, c0_92, c0_93, c0_94, c0_95, c0_96, c0_97, c0_98, c0_99, c0_100, c0_101, c0_102, c0_103, c0_104, c0_105, c0_106, c0_107, c0_108, c0_109, c0_110, c0_111, c0_112, c0_113, c0_114, c0_115, c0_116, c0_117, c0_118, c0_119, c0_120, c0_121, c0_122, c0_123, c0_124, c0_125, c0_126, c0_127, c0_128, c0_129, c0_130, c0_131, c0_132, c0_133, c0_134, c0_135, c0_136, c0_137, c0_138, c0_139, c0_140, c0_141, c0_142, c0_143, c0_144, c0_145, c0_146, c0_147, c0_148, c0_149, c0_150, c0_151, c0_152, c0_153, c0_154, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13, c2_14, c2_15, c2_16, c2_17, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27, c2_28, c2_29, c2_30, c2_31, c2_32, c2_33, c2_34, c2_35, c2_36, c2_37, c2_38, c2_39, c2_40, c2_41, c2_42, c2_43, c2_44, c2_45, c2_46, c2_47, c2_48, c2_49, c2_50, c2_51, c2_52, c2_53, c2_54, c2_55, c2_56, c2_57, c2_58, c2_59, c2_60, c2_61, c2_62, c2_63, c2_64, c2_65, c2_66, c2_67, c2_68, c2_69, c2_70, c2_71, c2_72, c2_73, c2_74, c2_75, c2_76, c2_77, c2_78, c2_79, c2_80, c2_81, c2_82, c2_83, c2_84, c2_85, c2_86, c2_87, c2_88, c2_89, c2_90, c2_91, c2_92, c2_93, c2_94, c2_95, c2_96, c2_97, c2_98, c2_99, c2_100, c2_101, c2_102, c2_103, c2_104, c2_105, c2_106, c2_107, c2_108, c2_109, c2_110, c2_111, c2_112, c2_113, c2_114, c2_115, c2_116, c2_117, c2_118, c2_119, c2_120, c2_121, c2_122, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27, c3_28, c3_29, c3_30, c3_31, c3_32, c3_33, c3_34, c3_35, c3_36, c3_37, c3_38, c3_39, c3_40, c3_41, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, c4_33, c4_34, c4_35, c4_36, c4_37, c4_38, c4_39, c4_40, c4_41, c4_42, c4_43, c4_44, c4_45, c4_46, c4_47, c4_48, c4_49, c4_50, c4_51, c4_52, c4_53, c4_54, c4_55, c4_56, c4_57, c4_58, c4_59, c4_60, c4_61, c4_62, c4_63, c4_64, c4_65, c4_66, c4_67, c4_68, c4_69, c4_70, c4_71, c4_72, c4_73, c4_74, c4_75, c4_76, c4_77, c4_78, c4_79, c4_80, c4_81, c4_82, c4_83, c4_84, c4_85, c4_86, c4_87, c4_88, c4_89, c4_90, c4_91, c4_92, c4_93, c4_94, c4_95, c4_96, c4_97, c4_98, c4_99, c4_100, c4_101, c4_102, c4_103, c4_104, c4_105, c4_106, c4_107, c4_108, c4_109, c4_110, c4_111, c4_112, c4_113, c4_114, c4_115, c4_116, c4_117, c4_118, c4_119, c4_120, c4_121, c4_122, c4_123, c4_124, c4_125, c4_126, c4_127, c4_128, c4_129, c4_130, c4_131, c4_132, c4_133, c4_134, c4_135, c4_136, c4_137, c4_138, c4_139, c4_140, c4_141, c4_142, c4_143, c4_144, c4_145, c4_146, c4_147, c4_148, c4_149, c4_150, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace032
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace032
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 164 (certificate_length y z w a b u)
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
  · exact coefficient_32 y z w a b u
  · exact coefficient_33 y z w a b u
  · exact coefficient_34 y z w a b u
  · exact coefficient_35 y z w a b u
  · exact coefficient_36 y z w a b u
  · exact coefficient_37 y z w a b u
  · exact coefficient_38 y z w a b u
  · exact coefficient_39 y z w a b u
  · exact coefficient_40 y z w a b u
  · exact coefficient_41 y z w a b u
  · exact coefficient_42 y z w a b u
  · exact coefficient_43 y z w a b u
  · exact coefficient_44 y z w a b u
  · exact coefficient_45 y z w a b u
  · exact coefficient_46 y z w a b u
  · exact coefficient_47 y z w a b u
  · exact coefficient_48 y z w a b u
  · exact coefficient_49 y z w a b u
  · exact coefficient_50 y z w a b u
  · exact coefficient_51 y z w a b u
  · exact coefficient_52 y z w a b u
  · exact coefficient_53 y z w a b u
  · exact coefficient_54 y z w a b u
  · exact coefficient_55 y z w a b u
  · exact coefficient_56 y z w a b u
  · exact coefficient_57 y z w a b u
  · exact coefficient_58 y z w a b u
  · exact coefficient_59 y z w a b u
  · exact coefficient_60 y z w a b u
  · exact coefficient_61 y z w a b u
  · exact coefficient_62 y z w a b u
  · exact coefficient_63 y z w a b u
  · exact coefficient_64 y z w a b u
  · exact coefficient_65 y z w a b u
  · exact coefficient_66 y z w a b u
  · exact coefficient_67 y z w a b u
  · exact coefficient_68 y z w a b u
  · exact coefficient_69 y z w a b u
  · exact coefficient_70 y z w a b u
  · exact coefficient_71 y z w a b u
  · exact coefficient_72 y z w a b u
  · exact coefficient_73 y z w a b u
  · exact coefficient_74 y z w a b u
  · exact coefficient_75 y z w a b u
  · exact coefficient_76 y z w a b u
  · exact coefficient_77 y z w a b u
  · exact coefficient_78 y z w a b u
  · exact coefficient_79 y z w a b u
  · exact coefficient_80 y z w a b u
  · exact coefficient_81 y z w a b u
  · exact coefficient_82 y z w a b u
  · exact coefficient_83 y z w a b u
  · exact coefficient_84 y z w a b u
  · exact coefficient_85 y z w a b u
  · exact coefficient_86 y z w a b u
  · exact coefficient_87 y z w a b u
  · exact coefficient_88 y z w a b u
  · exact coefficient_89 y z w a b u
  · exact coefficient_90 y z w a b u
  · exact coefficient_91 y z w a b u
  · exact coefficient_92 y z w a b u
  · exact coefficient_93 y z w a b u
  · exact coefficient_94 y z w a b u
  · exact coefficient_95 y z w a b u
  · exact coefficient_96 y z w a b u
  · exact coefficient_97 y z w a b u
  · exact coefficient_98 y z w a b u
  · exact coefficient_99 y z w a b u
  · exact coefficient_100 y z w a b u
  · exact coefficient_101 y z w a b u
  · exact coefficient_102 y z w a b u
  · exact coefficient_103 y z w a b u
  · exact coefficient_104 y z w a b u
  · exact coefficient_105 y z w a b u
  · exact coefficient_106 y z w a b u
  · exact coefficient_107 y z w a b u
  · exact coefficient_108 y z w a b u
  · exact coefficient_109 y z w a b u
  · exact coefficient_110 y z w a b u
  · exact coefficient_111 y z w a b u
  · exact coefficient_112 y z w a b u
  · exact coefficient_113 y z w a b u
  · exact coefficient_114 y z w a b u
  · exact coefficient_115 y z w a b u
  · exact coefficient_116 y z w a b u
  · exact coefficient_117 y z w a b u
  · exact coefficient_118 y z w a b u
  · exact coefficient_119 y z w a b u
  · exact coefficient_120 y z w a b u
  · exact coefficient_121 y z w a b u
  · exact coefficient_122 y z w a b u
  · exact coefficient_123 y z w a b u
  · exact coefficient_124 y z w a b u
  · exact coefficient_125 y z w a b u
  · exact coefficient_126 y z w a b u
  · exact coefficient_127 y z w a b u
  · exact coefficient_128 y z w a b u
  · exact coefficient_129 y z w a b u
  · exact coefficient_130 y z w a b u
  · exact coefficient_131 y z w a b u
  · exact coefficient_132 y z w a b u
  · exact coefficient_133 y z w a b u
  · exact coefficient_134 y z w a b u
  · exact coefficient_135 y z w a b u
  · exact coefficient_136 y z w a b u
  · exact coefficient_137 y z w a b u
  · exact coefficient_138 y z w a b u
  · exact coefficient_139 y z w a b u
  · exact coefficient_140 y z w a b u
  · exact coefficient_141 y z w a b u
  · exact coefficient_142 y z w a b u
  · exact coefficient_143 y z w a b u
  · exact coefficient_144 y z w a b u
  · exact coefficient_145 y z w a b u
  · exact coefficient_146 y z w a b u
  · exact coefficient_147 y z w a b u
  · exact coefficient_148 y z w a b u
  · exact coefficient_149 y z w a b u
  · exact coefficient_150 y z w a b u
  · exact coefficient_151 y z w a b u
  · exact coefficient_152 y z w a b u
  · exact coefficient_153 y z w a b u
  · exact coefficient_154 y z w a b u
  · exact coefficient_155 y z w a b u
  · exact coefficient_156 y z w a b u
  · exact coefficient_157 y z w a b u
  · exact coefficient_158 y z w a b u
  · exact coefficient_159 y z w a b u
  · exact coefficient_160 y z w a b u
  · exact coefficient_161 y z w a b u
  · exact coefficient_162 y z w a b u
  · exact coefficient_163 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace032
end
end

