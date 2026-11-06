module
public import SmallLevelTwentySixMMPPariTraceThirtyTwoV4
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

namespace SmallLevelTwentySixMMPPariTrace033
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_length (y z w a b u : ℂ) : (certificate y z w a b u).length=209 := by
  norm_num (config := {maxSteps := 1000000}) [certificate,add,multiply,scale,coefficients0,coefficients1,coefficients2,coefficients3,coefficients4,coefficients5,coefficients6]

end SmallLevelTwentySixMMPPariTrace033
end

section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixMMPPariTrace033
open SmallLevelPolynomialCoefficientCertificate

certify_coefficient_block (y z w a b u : ℂ) for (certificate y z w a b u)
  indices 0 through 208 unfolding [c0_0, c0_1, c0_2, c0_3, c0_4, c0_5, c0_6, c0_7, c0_8, c0_9, c0_10, c0_11, c0_12, c0_13, c0_14, c0_15, c0_16, c0_17, c0_18, c0_19, c0_20, c0_21, c0_22, c0_23, c0_24, c0_25, c0_26, c0_27, c0_28, c0_29, c0_30, c0_31, c0_32, c0_33, c0_34, c0_35, c0_36, c0_37, c0_38, c0_39, c0_40, c0_41, c0_42, c0_43, c0_44, c0_45, c0_46, c0_47, c0_48, c0_49, c0_50, c0_51, c0_52, c0_53, c0_54, c0_55, c0_56, c0_57, c0_58, c0_59, c0_60, c0_61, c0_62, c0_63, c0_64, c0_65, c0_66, c0_67, c0_68, c0_69, c0_70, c0_71, c0_72, c0_73, c0_74, c0_75, c0_76, c0_77, c0_78, c0_79, c0_80, c0_81, c0_82, c0_83, c0_84, c0_85, coefficients0, c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7, c1_8, c1_9, c1_10, c1_11, c1_12, c1_13, c1_14, c1_15, c1_16, c1_17, c1_18, c1_19, c1_20, c1_21, c1_22, c1_23, c1_24, c1_25, c1_26, c1_27, c1_28, c1_29, c1_30, c1_31, c1_32, c1_33, c1_34, c1_35, c1_36, c1_37, c1_38, c1_39, c1_40, c1_41, c1_42, c1_43, c1_44, c1_45, c1_46, c1_47, c1_48, c1_49, c1_50, c1_51, c1_52, c1_53, c1_54, c1_55, c1_56, c1_57, c1_58, c1_59, c1_60, c1_61, c1_62, c1_63, c1_64, c1_65, c1_66, c1_67, c1_68, c1_69, c1_70, c1_71, c1_72, c1_73, c1_74, c1_75, c1_76, c1_77, c1_78, c1_79, c1_80, c1_81, c1_82, c1_83, c1_84, c1_85, c1_86, c1_87, c1_88, c1_89, c1_90, c1_91, c1_92, c1_93, c1_94, c1_95, c1_96, c1_97, c1_98, c1_99, c1_100, c1_101, c1_102, c1_103, c1_104, c1_105, c1_106, c1_107, c1_108, c1_109, c1_110, c1_111, c1_112, c1_113, c1_114, c1_115, c1_116, c1_117, c1_118, c1_119, c1_120, c1_121, c1_122, c1_123, coefficients1, c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10, c2_11, c2_12, c2_13, c2_14, c2_15, c2_16, c2_17, c2_18, c2_19, c2_20, c2_21, c2_22, c2_23, c2_24, c2_25, c2_26, c2_27, c2_28, c2_29, c2_30, c2_31, c2_32, c2_33, c2_34, c2_35, c2_36, c2_37, c2_38, c2_39, c2_40, c2_41, c2_42, c2_43, c2_44, c2_45, c2_46, c2_47, c2_48, c2_49, c2_50, c2_51, c2_52, c2_53, c2_54, c2_55, c2_56, c2_57, c2_58, coefficients2, c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27, c3_28, c3_29, c3_30, c3_31, c3_32, c3_33, c3_34, c3_35, c3_36, c3_37, c3_38, c3_39, c3_40, c3_41, c3_42, c3_43, c3_44, c3_45, c3_46, c3_47, c3_48, c3_49, c3_50, c3_51, c3_52, c3_53, c3_54, c3_55, c3_56, c3_57, c3_58, c3_59, c3_60, c3_61, c3_62, c3_63, c3_64, c3_65, c3_66, c3_67, c3_68, c3_69, c3_70, c3_71, c3_72, c3_73, c3_74, c3_75, c3_76, c3_77, c3_78, c3_79, c3_80, c3_81, c3_82, c3_83, c3_84, c3_85, c3_86, c3_87, c3_88, c3_89, c3_90, c3_91, c3_92, c3_93, c3_94, c3_95, c3_96, c3_97, c3_98, c3_99, c3_100, c3_101, c3_102, c3_103, c3_104, c3_105, c3_106, c3_107, c3_108, c3_109, c3_110, c3_111, c3_112, c3_113, c3_114, c3_115, c3_116, c3_117, c3_118, c3_119, c3_120, c3_121, c3_122, c3_123, c3_124, c3_125, c3_126, c3_127, c3_128, c3_129, c3_130, c3_131, c3_132, c3_133, c3_134, c3_135, c3_136, c3_137, c3_138, c3_139, c3_140, c3_141, c3_142, c3_143, c3_144, c3_145, c3_146, c3_147, c3_148, c3_149, c3_150, coefficients3, c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, c4_33, c4_34, c4_35, c4_36, c4_37, c4_38, c4_39, c4_40, c4_41, c4_42, c4_43, c4_44, c4_45, c4_46, c4_47, c4_48, c4_49, c4_50, c4_51, c4_52, c4_53, c4_54, c4_55, c4_56, c4_57, c4_58, c4_59, c4_60, c4_61, c4_62, c4_63, c4_64, coefficients4, coefficients5, coefficients6, certificate]

end SmallLevelTwentySixMMPPariTrace033
end

section
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelTwentySixMMPPariTrace033
open SmallLevelPolynomialCoefficientCertificate
compact_certificate_declaration theorem certificate_zero (y z w a b u : ℂ) : ∀ v∈certificate y z w a b u,v=0 := by
  apply zero_of_getElem? _ 209 (certificate_length y z w a b u)
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
  · exact coefficient_164 y z w a b u
  · exact coefficient_165 y z w a b u
  · exact coefficient_166 y z w a b u
  · exact coefficient_167 y z w a b u
  · exact coefficient_168 y z w a b u
  · exact coefficient_169 y z w a b u
  · exact coefficient_170 y z w a b u
  · exact coefficient_171 y z w a b u
  · exact coefficient_172 y z w a b u
  · exact coefficient_173 y z w a b u
  · exact coefficient_174 y z w a b u
  · exact coefficient_175 y z w a b u
  · exact coefficient_176 y z w a b u
  · exact coefficient_177 y z w a b u
  · exact coefficient_178 y z w a b u
  · exact coefficient_179 y z w a b u
  · exact coefficient_180 y z w a b u
  · exact coefficient_181 y z w a b u
  · exact coefficient_182 y z w a b u
  · exact coefficient_183 y z w a b u
  · exact coefficient_184 y z w a b u
  · exact coefficient_185 y z w a b u
  · exact coefficient_186 y z w a b u
  · exact coefficient_187 y z w a b u
  · exact coefficient_188 y z w a b u
  · exact coefficient_189 y z w a b u
  · exact coefficient_190 y z w a b u
  · exact coefficient_191 y z w a b u
  · exact coefficient_192 y z w a b u
  · exact coefficient_193 y z w a b u
  · exact coefficient_194 y z w a b u
  · exact coefficient_195 y z w a b u
  · exact coefficient_196 y z w a b u
  · exact coefficient_197 y z w a b u
  · exact coefficient_198 y z w a b u
  · exact coefficient_199 y z w a b u
  · exact coefficient_200 y z w a b u
  · exact coefficient_201 y z w a b u
  · exact coefficient_202 y z w a b u
  · exact coefficient_203 y z w a b u
  · exact coefficient_204 y z w a b u
  · exact coefficient_205 y z w a b u
  · exact coefficient_206 y z w a b u
  · exact coefficient_207 y z w a b u
  · exact coefficient_208 y z w a b u
compact_certificate_declaration theorem identity (x y z w a b u : ℂ) :
    p0 x y z w a b u*p1 x y z w a b u+p2 x y z w a b u*p3 x y z w a b u=
      p4 x y z w a b u+p5 x y z w a b u*p6 x y z w a b u := by
  unfold p0 p1 p2 p3 p4 p5 p6
  exact of_zero_coefficients x _ _ _ _ _ _ _ (certificate_zero y z w a b u)
#print axioms identity

end SmallLevelTwentySixMMPPariTrace033
end
end

