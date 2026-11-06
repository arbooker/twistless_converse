module
public import SmallLevelTwentySixGridSignScalingWordBundleV4
public import SmallLevelTwentySixGridSignScalingTaylorBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid

theorem word_scale_sign (i : Fin 235) (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    gridWordSign 1 (-1) (sourceWord (gridGroupSource i))*u^(groupPowers i).1*v^(groupPowers i).2.2.1=
      gridWordSign u (-u*v) (sourceWord (gridGroupSource i)) := by
  fin_cases i
  · exact word_scale_sign_0 u v hu hv
  · exact word_scale_sign_1 u v hu hv
  · exact word_scale_sign_2 u v hu hv
  · exact word_scale_sign_3 u v hu hv
  · exact word_scale_sign_4 u v hu hv
  · exact word_scale_sign_5 u v hu hv
  · exact word_scale_sign_6 u v hu hv
  · exact word_scale_sign_7 u v hu hv
  · exact word_scale_sign_8 u v hu hv
  · exact word_scale_sign_9 u v hu hv
  · exact word_scale_sign_10 u v hu hv
  · exact word_scale_sign_11 u v hu hv
  · exact word_scale_sign_12 u v hu hv
  · exact word_scale_sign_13 u v hu hv
  · exact word_scale_sign_14 u v hu hv
  · exact word_scale_sign_15 u v hu hv
  · exact word_scale_sign_16 u v hu hv
  · exact word_scale_sign_17 u v hu hv
  · exact word_scale_sign_18 u v hu hv
  · exact word_scale_sign_19 u v hu hv
  · exact word_scale_sign_20 u v hu hv
  · exact word_scale_sign_21 u v hu hv
  · exact word_scale_sign_22 u v hu hv
  · exact word_scale_sign_23 u v hu hv
  · exact word_scale_sign_24 u v hu hv
  · exact word_scale_sign_25 u v hu hv
  · exact word_scale_sign_26 u v hu hv
  · exact word_scale_sign_27 u v hu hv
  · exact word_scale_sign_28 u v hu hv
  · exact word_scale_sign_29 u v hu hv
  · exact word_scale_sign_30 u v hu hv
  · exact word_scale_sign_31 u v hu hv
  · exact word_scale_sign_32 u v hu hv
  · exact word_scale_sign_33 u v hu hv
  · exact word_scale_sign_34 u v hu hv
  · exact word_scale_sign_35 u v hu hv
  · exact word_scale_sign_36 u v hu hv
  · exact word_scale_sign_37 u v hu hv
  · exact word_scale_sign_38 u v hu hv
  · exact word_scale_sign_39 u v hu hv
  · exact word_scale_sign_40 u v hu hv
  · exact word_scale_sign_41 u v hu hv
  · exact word_scale_sign_42 u v hu hv
  · exact word_scale_sign_43 u v hu hv
  · exact word_scale_sign_44 u v hu hv
  · exact word_scale_sign_45 u v hu hv
  · exact word_scale_sign_46 u v hu hv
  · exact word_scale_sign_47 u v hu hv
  · exact word_scale_sign_48 u v hu hv
  · exact word_scale_sign_49 u v hu hv
  · exact word_scale_sign_50 u v hu hv
  · exact word_scale_sign_51 u v hu hv
  · exact word_scale_sign_52 u v hu hv
  · exact word_scale_sign_53 u v hu hv
  · exact word_scale_sign_54 u v hu hv
  · exact word_scale_sign_55 u v hu hv
  · exact word_scale_sign_56 u v hu hv
  · exact word_scale_sign_57 u v hu hv
  · exact word_scale_sign_58 u v hu hv
  · exact word_scale_sign_59 u v hu hv
  · exact word_scale_sign_60 u v hu hv
  · exact word_scale_sign_61 u v hu hv
  · exact word_scale_sign_62 u v hu hv
  · exact word_scale_sign_63 u v hu hv
  · exact word_scale_sign_64 u v hu hv
  · exact word_scale_sign_65 u v hu hv
  · exact word_scale_sign_66 u v hu hv
  · exact word_scale_sign_67 u v hu hv
  · exact word_scale_sign_68 u v hu hv
  · exact word_scale_sign_69 u v hu hv
  · exact word_scale_sign_70 u v hu hv
  · exact word_scale_sign_71 u v hu hv
  · exact word_scale_sign_72 u v hu hv
  · exact word_scale_sign_73 u v hu hv
  · exact word_scale_sign_74 u v hu hv
  · exact word_scale_sign_75 u v hu hv
  · exact word_scale_sign_76 u v hu hv
  · exact word_scale_sign_77 u v hu hv
  · exact word_scale_sign_78 u v hu hv
  · exact word_scale_sign_79 u v hu hv
  · exact word_scale_sign_80 u v hu hv
  · exact word_scale_sign_81 u v hu hv
  · exact word_scale_sign_82 u v hu hv
  · exact word_scale_sign_83 u v hu hv
  · exact word_scale_sign_84 u v hu hv
  · exact word_scale_sign_85 u v hu hv
  · exact word_scale_sign_86 u v hu hv
  · exact word_scale_sign_87 u v hu hv
  · exact word_scale_sign_88 u v hu hv
  · exact word_scale_sign_89 u v hu hv
  · exact word_scale_sign_90 u v hu hv
  · exact word_scale_sign_91 u v hu hv
  · exact word_scale_sign_92 u v hu hv
  · exact word_scale_sign_93 u v hu hv
  · exact word_scale_sign_94 u v hu hv
  · exact word_scale_sign_95 u v hu hv
  · exact word_scale_sign_96 u v hu hv
  · exact word_scale_sign_97 u v hu hv
  · exact word_scale_sign_98 u v hu hv
  · exact word_scale_sign_99 u v hu hv
  · exact word_scale_sign_100 u v hu hv
  · exact word_scale_sign_101 u v hu hv
  · exact word_scale_sign_102 u v hu hv
  · exact word_scale_sign_103 u v hu hv
  · exact word_scale_sign_104 u v hu hv
  · exact word_scale_sign_105 u v hu hv
  · exact word_scale_sign_106 u v hu hv
  · exact word_scale_sign_107 u v hu hv
  · exact word_scale_sign_108 u v hu hv
  · exact word_scale_sign_109 u v hu hv
  · exact word_scale_sign_110 u v hu hv
  · exact word_scale_sign_111 u v hu hv
  · exact word_scale_sign_112 u v hu hv
  · exact word_scale_sign_113 u v hu hv
  · exact word_scale_sign_114 u v hu hv
  · exact word_scale_sign_115 u v hu hv
  · exact word_scale_sign_116 u v hu hv
  · exact word_scale_sign_117 u v hu hv
  · exact word_scale_sign_118 u v hu hv
  · exact word_scale_sign_119 u v hu hv
  · exact word_scale_sign_120 u v hu hv
  · exact word_scale_sign_121 u v hu hv
  · exact word_scale_sign_122 u v hu hv
  · exact word_scale_sign_123 u v hu hv
  · exact word_scale_sign_124 u v hu hv
  · exact word_scale_sign_125 u v hu hv
  · exact word_scale_sign_126 u v hu hv
  · exact word_scale_sign_127 u v hu hv
  · exact word_scale_sign_128 u v hu hv
  · exact word_scale_sign_129 u v hu hv
  · exact word_scale_sign_130 u v hu hv
  · exact word_scale_sign_131 u v hu hv
  · exact word_scale_sign_132 u v hu hv
  · exact word_scale_sign_133 u v hu hv
  · exact word_scale_sign_134 u v hu hv
  · exact word_scale_sign_135 u v hu hv
  · exact word_scale_sign_136 u v hu hv
  · exact word_scale_sign_137 u v hu hv
  · exact word_scale_sign_138 u v hu hv
  · exact word_scale_sign_139 u v hu hv
  · exact word_scale_sign_140 u v hu hv
  · exact word_scale_sign_141 u v hu hv
  · exact word_scale_sign_142 u v hu hv
  · exact word_scale_sign_143 u v hu hv
  · exact word_scale_sign_144 u v hu hv
  · exact word_scale_sign_145 u v hu hv
  · exact word_scale_sign_146 u v hu hv
  · exact word_scale_sign_147 u v hu hv
  · exact word_scale_sign_148 u v hu hv
  · exact word_scale_sign_149 u v hu hv
  · exact word_scale_sign_150 u v hu hv
  · exact word_scale_sign_151 u v hu hv
  · exact word_scale_sign_152 u v hu hv
  · exact word_scale_sign_153 u v hu hv
  · exact word_scale_sign_154 u v hu hv
  · exact word_scale_sign_155 u v hu hv
  · exact word_scale_sign_156 u v hu hv
  · exact word_scale_sign_157 u v hu hv
  · exact word_scale_sign_158 u v hu hv
  · exact word_scale_sign_159 u v hu hv
  · exact word_scale_sign_160 u v hu hv
  · exact word_scale_sign_161 u v hu hv
  · exact word_scale_sign_162 u v hu hv
  · exact word_scale_sign_163 u v hu hv
  · exact word_scale_sign_164 u v hu hv
  · exact word_scale_sign_165 u v hu hv
  · exact word_scale_sign_166 u v hu hv
  · exact word_scale_sign_167 u v hu hv
  · exact word_scale_sign_168 u v hu hv
  · exact word_scale_sign_169 u v hu hv
  · exact word_scale_sign_170 u v hu hv
  · exact word_scale_sign_171 u v hu hv
  · exact word_scale_sign_172 u v hu hv
  · exact word_scale_sign_173 u v hu hv
  · exact word_scale_sign_174 u v hu hv
  · exact word_scale_sign_175 u v hu hv
  · exact word_scale_sign_176 u v hu hv
  · exact word_scale_sign_177 u v hu hv
  · exact word_scale_sign_178 u v hu hv
  · exact word_scale_sign_179 u v hu hv
  · exact word_scale_sign_180 u v hu hv
  · exact word_scale_sign_181 u v hu hv
  · exact word_scale_sign_182 u v hu hv
  · exact word_scale_sign_183 u v hu hv
  · exact word_scale_sign_184 u v hu hv
  · exact word_scale_sign_185 u v hu hv
  · exact word_scale_sign_186 u v hu hv
  · exact word_scale_sign_187 u v hu hv
  · exact word_scale_sign_188 u v hu hv
  · exact word_scale_sign_189 u v hu hv
  · exact word_scale_sign_190 u v hu hv
  · exact word_scale_sign_191 u v hu hv
  · exact word_scale_sign_192 u v hu hv
  · exact word_scale_sign_193 u v hu hv
  · exact word_scale_sign_194 u v hu hv
  · exact word_scale_sign_195 u v hu hv
  · exact word_scale_sign_196 u v hu hv
  · exact word_scale_sign_197 u v hu hv
  · exact word_scale_sign_198 u v hu hv
  · exact word_scale_sign_199 u v hu hv
  · exact word_scale_sign_200 u v hu hv
  · exact word_scale_sign_201 u v hu hv
  · exact word_scale_sign_202 u v hu hv
  · exact word_scale_sign_203 u v hu hv
  · exact word_scale_sign_204 u v hu hv
  · exact word_scale_sign_205 u v hu hv
  · exact word_scale_sign_206 u v hu hv
  · exact word_scale_sign_207 u v hu hv
  · exact word_scale_sign_208 u v hu hv
  · exact word_scale_sign_209 u v hu hv
  · exact word_scale_sign_210 u v hu hv
  · exact word_scale_sign_211 u v hu hv
  · exact word_scale_sign_212 u v hu hv
  · exact word_scale_sign_213 u v hu hv
  · exact word_scale_sign_214 u v hu hv
  · exact word_scale_sign_215 u v hu hv
  · exact word_scale_sign_216 u v hu hv
  · exact word_scale_sign_217 u v hu hv
  · exact word_scale_sign_218 u v hu hv
  · exact word_scale_sign_219 u v hu hv
  · exact word_scale_sign_220 u v hu hv
  · exact word_scale_sign_221 u v hu hv
  · exact word_scale_sign_222 u v hu hv
  · exact word_scale_sign_223 u v hu hv
  · exact word_scale_sign_224 u v hu hv
  · exact word_scale_sign_225 u v hu hv
  · exact word_scale_sign_226 u v hu hv
  · exact word_scale_sign_227 u v hu hv
  · exact word_scale_sign_228 u v hu hv
  · exact word_scale_sign_229 u v hu hv
  · exact word_scale_sign_230 u v hu hv
  · exact word_scale_sign_231 u v hu hv
  · exact word_scale_sign_232 u v hu hv
  · exact word_scale_sign_233 u v hu hv
  · exact word_scale_sign_234 u v hu hv

theorem taylor_scale_sign (i : Fin 71) (c u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ((if 13∣gridTaylorQ i then -c else 1)*(-1))*u^(taylorPowers i).1*v^(taylorPowers i).2.2.1=
      ((if 2∣gridTaylorQ i then u else 1)*(if 13∣gridTaylorQ i then -(c*v) else 1))*(-u*v) := by
  fin_cases i
  · exact taylor_scale_sign_0 c u v hu hv
  · exact taylor_scale_sign_1 c u v hu hv
  · exact taylor_scale_sign_2 c u v hu hv
  · exact taylor_scale_sign_3 c u v hu hv
  · exact taylor_scale_sign_4 c u v hu hv
  · exact taylor_scale_sign_5 c u v hu hv
  · exact taylor_scale_sign_6 c u v hu hv
  · exact taylor_scale_sign_7 c u v hu hv
  · exact taylor_scale_sign_8 c u v hu hv
  · exact taylor_scale_sign_9 c u v hu hv
  · exact taylor_scale_sign_10 c u v hu hv
  · exact taylor_scale_sign_11 c u v hu hv
  · exact taylor_scale_sign_12 c u v hu hv
  · exact taylor_scale_sign_13 c u v hu hv
  · exact taylor_scale_sign_14 c u v hu hv
  · exact taylor_scale_sign_15 c u v hu hv
  · exact taylor_scale_sign_16 c u v hu hv
  · exact taylor_scale_sign_17 c u v hu hv
  · exact taylor_scale_sign_18 c u v hu hv
  · exact taylor_scale_sign_19 c u v hu hv
  · exact taylor_scale_sign_20 c u v hu hv
  · exact taylor_scale_sign_21 c u v hu hv
  · exact taylor_scale_sign_22 c u v hu hv
  · exact taylor_scale_sign_23 c u v hu hv
  · exact taylor_scale_sign_24 c u v hu hv
  · exact taylor_scale_sign_25 c u v hu hv
  · exact taylor_scale_sign_26 c u v hu hv
  · exact taylor_scale_sign_27 c u v hu hv
  · exact taylor_scale_sign_28 c u v hu hv
  · exact taylor_scale_sign_29 c u v hu hv
  · exact taylor_scale_sign_30 c u v hu hv
  · exact taylor_scale_sign_31 c u v hu hv
  · exact taylor_scale_sign_32 c u v hu hv
  · exact taylor_scale_sign_33 c u v hu hv
  · exact taylor_scale_sign_34 c u v hu hv
  · exact taylor_scale_sign_35 c u v hu hv
  · exact taylor_scale_sign_36 c u v hu hv
  · exact taylor_scale_sign_37 c u v hu hv
  · exact taylor_scale_sign_38 c u v hu hv
  · exact taylor_scale_sign_39 c u v hu hv
  · exact taylor_scale_sign_40 c u v hu hv
  · exact taylor_scale_sign_41 c u v hu hv
  · exact taylor_scale_sign_42 c u v hu hv
  · exact taylor_scale_sign_43 c u v hu hv
  · exact taylor_scale_sign_44 c u v hu hv
  · exact taylor_scale_sign_45 c u v hu hv
  · exact taylor_scale_sign_46 c u v hu hv
  · exact taylor_scale_sign_47 c u v hu hv
  · exact taylor_scale_sign_48 c u v hu hv
  · exact taylor_scale_sign_49 c u v hu hv
  · exact taylor_scale_sign_50 c u v hu hv
  · exact taylor_scale_sign_51 c u v hu hv
  · exact taylor_scale_sign_52 c u v hu hv
  · exact taylor_scale_sign_53 c u v hu hv
  · exact taylor_scale_sign_54 c u v hu hv
  · exact taylor_scale_sign_55 c u v hu hv
  · exact taylor_scale_sign_56 c u v hu hv
  · exact taylor_scale_sign_57 c u v hu hv
  · exact taylor_scale_sign_58 c u v hu hv
  · exact taylor_scale_sign_59 c u v hu hv
  · exact taylor_scale_sign_60 c u v hu hv
  · exact taylor_scale_sign_61 c u v hu hv
  · exact taylor_scale_sign_62 c u v hu hv
  · exact taylor_scale_sign_63 c u v hu hv
  · exact taylor_scale_sign_64 c u v hu hv
  · exact taylor_scale_sign_65 c u v hu hv
  · exact taylor_scale_sign_66 c u v hu hv
  · exact taylor_scale_sign_67 c u v hu hv
  · exact taylor_scale_sign_68 c u v hu hv
  · exact taylor_scale_sign_69 c u v hu hv
  · exact taylor_scale_sign_70 c u v hu hv

#print axioms word_scale_sign
#print axioms taylor_scale_sign

end SmallLevelTwentySixGrid
