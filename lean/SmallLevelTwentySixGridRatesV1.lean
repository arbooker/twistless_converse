module
public import SmallLevelTwentySixGridRateBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

theorem groupRate_factor (i : Fin 235) :
    gridGroupRate i=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*
      (13:ℚ)^(groupPowers i).2.2.1*(5:ℚ)^(groupPowers i).2.2.2 := by
  fin_cases i
  · exact groupRate_factor_0
  · exact groupRate_factor_1
  · exact groupRate_factor_2
  · exact groupRate_factor_3
  · exact groupRate_factor_4
  · exact groupRate_factor_5
  · exact groupRate_factor_6
  · exact groupRate_factor_7
  · exact groupRate_factor_8
  · exact groupRate_factor_9
  · exact groupRate_factor_10
  · exact groupRate_factor_11
  · exact groupRate_factor_12
  · exact groupRate_factor_13
  · exact groupRate_factor_14
  · exact groupRate_factor_15
  · exact groupRate_factor_16
  · exact groupRate_factor_17
  · exact groupRate_factor_18
  · exact groupRate_factor_19
  · exact groupRate_factor_20
  · exact groupRate_factor_21
  · exact groupRate_factor_22
  · exact groupRate_factor_23
  · exact groupRate_factor_24
  · exact groupRate_factor_25
  · exact groupRate_factor_26
  · exact groupRate_factor_27
  · exact groupRate_factor_28
  · exact groupRate_factor_29
  · exact groupRate_factor_30
  · exact groupRate_factor_31
  · exact groupRate_factor_32
  · exact groupRate_factor_33
  · exact groupRate_factor_34
  · exact groupRate_factor_35
  · exact groupRate_factor_36
  · exact groupRate_factor_37
  · exact groupRate_factor_38
  · exact groupRate_factor_39
  · exact groupRate_factor_40
  · exact groupRate_factor_41
  · exact groupRate_factor_42
  · exact groupRate_factor_43
  · exact groupRate_factor_44
  · exact groupRate_factor_45
  · exact groupRate_factor_46
  · exact groupRate_factor_47
  · exact groupRate_factor_48
  · exact groupRate_factor_49
  · exact groupRate_factor_50
  · exact groupRate_factor_51
  · exact groupRate_factor_52
  · exact groupRate_factor_53
  · exact groupRate_factor_54
  · exact groupRate_factor_55
  · exact groupRate_factor_56
  · exact groupRate_factor_57
  · exact groupRate_factor_58
  · exact groupRate_factor_59
  · exact groupRate_factor_60
  · exact groupRate_factor_61
  · exact groupRate_factor_62
  · exact groupRate_factor_63
  · exact groupRate_factor_64
  · exact groupRate_factor_65
  · exact groupRate_factor_66
  · exact groupRate_factor_67
  · exact groupRate_factor_68
  · exact groupRate_factor_69
  · exact groupRate_factor_70
  · exact groupRate_factor_71
  · exact groupRate_factor_72
  · exact groupRate_factor_73
  · exact groupRate_factor_74
  · exact groupRate_factor_75
  · exact groupRate_factor_76
  · exact groupRate_factor_77
  · exact groupRate_factor_78
  · exact groupRate_factor_79
  · exact groupRate_factor_80
  · exact groupRate_factor_81
  · exact groupRate_factor_82
  · exact groupRate_factor_83
  · exact groupRate_factor_84
  · exact groupRate_factor_85
  · exact groupRate_factor_86
  · exact groupRate_factor_87
  · exact groupRate_factor_88
  · exact groupRate_factor_89
  · exact groupRate_factor_90
  · exact groupRate_factor_91
  · exact groupRate_factor_92
  · exact groupRate_factor_93
  · exact groupRate_factor_94
  · exact groupRate_factor_95
  · exact groupRate_factor_96
  · exact groupRate_factor_97
  · exact groupRate_factor_98
  · exact groupRate_factor_99
  · exact groupRate_factor_100
  · exact groupRate_factor_101
  · exact groupRate_factor_102
  · exact groupRate_factor_103
  · exact groupRate_factor_104
  · exact groupRate_factor_105
  · exact groupRate_factor_106
  · exact groupRate_factor_107
  · exact groupRate_factor_108
  · exact groupRate_factor_109
  · exact groupRate_factor_110
  · exact groupRate_factor_111
  · exact groupRate_factor_112
  · exact groupRate_factor_113
  · exact groupRate_factor_114
  · exact groupRate_factor_115
  · exact groupRate_factor_116
  · exact groupRate_factor_117
  · exact groupRate_factor_118
  · exact groupRate_factor_119
  · exact groupRate_factor_120
  · exact groupRate_factor_121
  · exact groupRate_factor_122
  · exact groupRate_factor_123
  · exact groupRate_factor_124
  · exact groupRate_factor_125
  · exact groupRate_factor_126
  · exact groupRate_factor_127
  · exact groupRate_factor_128
  · exact groupRate_factor_129
  · exact groupRate_factor_130
  · exact groupRate_factor_131
  · exact groupRate_factor_132
  · exact groupRate_factor_133
  · exact groupRate_factor_134
  · exact groupRate_factor_135
  · exact groupRate_factor_136
  · exact groupRate_factor_137
  · exact groupRate_factor_138
  · exact groupRate_factor_139
  · exact groupRate_factor_140
  · exact groupRate_factor_141
  · exact groupRate_factor_142
  · exact groupRate_factor_143
  · exact groupRate_factor_144
  · exact groupRate_factor_145
  · exact groupRate_factor_146
  · exact groupRate_factor_147
  · exact groupRate_factor_148
  · exact groupRate_factor_149
  · exact groupRate_factor_150
  · exact groupRate_factor_151
  · exact groupRate_factor_152
  · exact groupRate_factor_153
  · exact groupRate_factor_154
  · exact groupRate_factor_155
  · exact groupRate_factor_156
  · exact groupRate_factor_157
  · exact groupRate_factor_158
  · exact groupRate_factor_159
  · exact groupRate_factor_160
  · exact groupRate_factor_161
  · exact groupRate_factor_162
  · exact groupRate_factor_163
  · exact groupRate_factor_164
  · exact groupRate_factor_165
  · exact groupRate_factor_166
  · exact groupRate_factor_167
  · exact groupRate_factor_168
  · exact groupRate_factor_169
  · exact groupRate_factor_170
  · exact groupRate_factor_171
  · exact groupRate_factor_172
  · exact groupRate_factor_173
  · exact groupRate_factor_174
  · exact groupRate_factor_175
  · exact groupRate_factor_176
  · exact groupRate_factor_177
  · exact groupRate_factor_178
  · exact groupRate_factor_179
  · exact groupRate_factor_180
  · exact groupRate_factor_181
  · exact groupRate_factor_182
  · exact groupRate_factor_183
  · exact groupRate_factor_184
  · exact groupRate_factor_185
  · exact groupRate_factor_186
  · exact groupRate_factor_187
  · exact groupRate_factor_188
  · exact groupRate_factor_189
  · exact groupRate_factor_190
  · exact groupRate_factor_191
  · exact groupRate_factor_192
  · exact groupRate_factor_193
  · exact groupRate_factor_194
  · exact groupRate_factor_195
  · exact groupRate_factor_196
  · exact groupRate_factor_197
  · exact groupRate_factor_198
  · exact groupRate_factor_199
  · exact groupRate_factor_200
  · exact groupRate_factor_201
  · exact groupRate_factor_202
  · exact groupRate_factor_203
  · exact groupRate_factor_204
  · exact groupRate_factor_205
  · exact groupRate_factor_206
  · exact groupRate_factor_207
  · exact groupRate_factor_208
  · exact groupRate_factor_209
  · exact groupRate_factor_210
  · exact groupRate_factor_211
  · exact groupRate_factor_212
  · exact groupRate_factor_213
  · exact groupRate_factor_214
  · exact groupRate_factor_215
  · exact groupRate_factor_216
  · exact groupRate_factor_217
  · exact groupRate_factor_218
  · exact groupRate_factor_219
  · exact groupRate_factor_220
  · exact groupRate_factor_221
  · exact groupRate_factor_222
  · exact groupRate_factor_223
  · exact groupRate_factor_224
  · exact groupRate_factor_225
  · exact groupRate_factor_226
  · exact groupRate_factor_227
  · exact groupRate_factor_228
  · exact groupRate_factor_229
  · exact groupRate_factor_230
  · exact groupRate_factor_231
  · exact groupRate_factor_232
  · exact groupRate_factor_233
  · exact groupRate_factor_234

theorem taylorRate_factor (i : Fin 71) :
    taylorRate i=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*
      (13:ℚ)^(taylorPowers i).2.2.1*(5:ℚ)^(taylorPowers i).2.2.2 := by
  fin_cases i <;> norm_num [taylorRate,gridTaylorL,gridTaylorQ,gridTaylorT,gridTaylorSpecs,taylorPowers]

theorem groupRate_complex (i : Fin 235) (h : ℂ) :
    (gridGroupRate i:ℂ)^h=monomial (groupPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((13:ℂ)^h) ((5:ℂ)^h) :=
  rational_power 2 3 13 5 (by decide) (by decide) (by decide) (by decide) _ _ (groupRate_factor i) h

theorem taylorRate_complex (i : Fin 71) (h : ℂ) :
    (taylorRate i:ℂ)^h=monomial (taylorPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((13:ℂ)^h) ((5:ℂ)^h) :=
  rational_power 2 3 13 5 (by decide) (by decide) (by decide) (by decide) _ _ (taylorRate_factor i) h

theorem matrixScalar_leading (m : ℕ) (f : ℕ→ℂ) (η s : ℂ) (i : Fin 235) :
    gridMatrixScalar m f η i 0 s=
      gridWordSign (-badParameter f 2) η (sourceWord (gridGroupSource i))*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s) := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one,root_two]
  rw [groupRate_complex]
  rfl

theorem taylorScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 71) :
    gridTaylorCoefficient m f ε i 0 s=
      (FinitenessNormalizedTwistProduct.root 26 f (gridTaylorQ i))*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s) := by
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  have hb : (((gridTaylorL i:ℝ)*((gridTaylorT i:ℝ)/780)^2:ℝ):ℂ)=(taylorRate i:ℂ) := by
    simp [taylorRate]
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Ring.choose_zero_right,mul_one,hm]
  rw [hb,taylorRate_complex]
  unfold phase parameter
  ring

#print axioms groupRate_complex
#print axioms taylorRate_complex
#print axioms matrixScalar_leading
#print axioms taylorScalar_leading
end SmallLevelTwentySixGrid
