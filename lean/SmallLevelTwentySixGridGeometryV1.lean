module
public import SmallLevelTwentySixGridGeometryBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Matrix SmallLevelAdditive

theorem gridGroup_geometry (i : Fin 235) : GridGroupGeometry i := by
  fin_cases i
  · exact gridGroup_geometry_0
  · exact gridGroup_geometry_1
  · exact gridGroup_geometry_2
  · exact gridGroup_geometry_3
  · exact gridGroup_geometry_4
  · exact gridGroup_geometry_5
  · exact gridGroup_geometry_6
  · exact gridGroup_geometry_7
  · exact gridGroup_geometry_8
  · exact gridGroup_geometry_9
  · exact gridGroup_geometry_10
  · exact gridGroup_geometry_11
  · exact gridGroup_geometry_12
  · exact gridGroup_geometry_13
  · exact gridGroup_geometry_14
  · exact gridGroup_geometry_15
  · exact gridGroup_geometry_16
  · exact gridGroup_geometry_17
  · exact gridGroup_geometry_18
  · exact gridGroup_geometry_19
  · exact gridGroup_geometry_20
  · exact gridGroup_geometry_21
  · exact gridGroup_geometry_22
  · exact gridGroup_geometry_23
  · exact gridGroup_geometry_24
  · exact gridGroup_geometry_25
  · exact gridGroup_geometry_26
  · exact gridGroup_geometry_27
  · exact gridGroup_geometry_28
  · exact gridGroup_geometry_29
  · exact gridGroup_geometry_30
  · exact gridGroup_geometry_31
  · exact gridGroup_geometry_32
  · exact gridGroup_geometry_33
  · exact gridGroup_geometry_34
  · exact gridGroup_geometry_35
  · exact gridGroup_geometry_36
  · exact gridGroup_geometry_37
  · exact gridGroup_geometry_38
  · exact gridGroup_geometry_39
  · exact gridGroup_geometry_40
  · exact gridGroup_geometry_41
  · exact gridGroup_geometry_42
  · exact gridGroup_geometry_43
  · exact gridGroup_geometry_44
  · exact gridGroup_geometry_45
  · exact gridGroup_geometry_46
  · exact gridGroup_geometry_47
  · exact gridGroup_geometry_48
  · exact gridGroup_geometry_49
  · exact gridGroup_geometry_50
  · exact gridGroup_geometry_51
  · exact gridGroup_geometry_52
  · exact gridGroup_geometry_53
  · exact gridGroup_geometry_54
  · exact gridGroup_geometry_55
  · exact gridGroup_geometry_56
  · exact gridGroup_geometry_57
  · exact gridGroup_geometry_58
  · exact gridGroup_geometry_59
  · exact gridGroup_geometry_60
  · exact gridGroup_geometry_61
  · exact gridGroup_geometry_62
  · exact gridGroup_geometry_63
  · exact gridGroup_geometry_64
  · exact gridGroup_geometry_65
  · exact gridGroup_geometry_66
  · exact gridGroup_geometry_67
  · exact gridGroup_geometry_68
  · exact gridGroup_geometry_69
  · exact gridGroup_geometry_70
  · exact gridGroup_geometry_71
  · exact gridGroup_geometry_72
  · exact gridGroup_geometry_73
  · exact gridGroup_geometry_74
  · exact gridGroup_geometry_75
  · exact gridGroup_geometry_76
  · exact gridGroup_geometry_77
  · exact gridGroup_geometry_78
  · exact gridGroup_geometry_79
  · exact gridGroup_geometry_80
  · exact gridGroup_geometry_81
  · exact gridGroup_geometry_82
  · exact gridGroup_geometry_83
  · exact gridGroup_geometry_84
  · exact gridGroup_geometry_85
  · exact gridGroup_geometry_86
  · exact gridGroup_geometry_87
  · exact gridGroup_geometry_88
  · exact gridGroup_geometry_89
  · exact gridGroup_geometry_90
  · exact gridGroup_geometry_91
  · exact gridGroup_geometry_92
  · exact gridGroup_geometry_93
  · exact gridGroup_geometry_94
  · exact gridGroup_geometry_95
  · exact gridGroup_geometry_96
  · exact gridGroup_geometry_97
  · exact gridGroup_geometry_98
  · exact gridGroup_geometry_99
  · exact gridGroup_geometry_100
  · exact gridGroup_geometry_101
  · exact gridGroup_geometry_102
  · exact gridGroup_geometry_103
  · exact gridGroup_geometry_104
  · exact gridGroup_geometry_105
  · exact gridGroup_geometry_106
  · exact gridGroup_geometry_107
  · exact gridGroup_geometry_108
  · exact gridGroup_geometry_109
  · exact gridGroup_geometry_110
  · exact gridGroup_geometry_111
  · exact gridGroup_geometry_112
  · exact gridGroup_geometry_113
  · exact gridGroup_geometry_114
  · exact gridGroup_geometry_115
  · exact gridGroup_geometry_116
  · exact gridGroup_geometry_117
  · exact gridGroup_geometry_118
  · exact gridGroup_geometry_119
  · exact gridGroup_geometry_120
  · exact gridGroup_geometry_121
  · exact gridGroup_geometry_122
  · exact gridGroup_geometry_123
  · exact gridGroup_geometry_124
  · exact gridGroup_geometry_125
  · exact gridGroup_geometry_126
  · exact gridGroup_geometry_127
  · exact gridGroup_geometry_128
  · exact gridGroup_geometry_129
  · exact gridGroup_geometry_130
  · exact gridGroup_geometry_131
  · exact gridGroup_geometry_132
  · exact gridGroup_geometry_133
  · exact gridGroup_geometry_134
  · exact gridGroup_geometry_135
  · exact gridGroup_geometry_136
  · exact gridGroup_geometry_137
  · exact gridGroup_geometry_138
  · exact gridGroup_geometry_139
  · exact gridGroup_geometry_140
  · exact gridGroup_geometry_141
  · exact gridGroup_geometry_142
  · exact gridGroup_geometry_143
  · exact gridGroup_geometry_144
  · exact gridGroup_geometry_145
  · exact gridGroup_geometry_146
  · exact gridGroup_geometry_147
  · exact gridGroup_geometry_148
  · exact gridGroup_geometry_149
  · exact gridGroup_geometry_150
  · exact gridGroup_geometry_151
  · exact gridGroup_geometry_152
  · exact gridGroup_geometry_153
  · exact gridGroup_geometry_154
  · exact gridGroup_geometry_155
  · exact gridGroup_geometry_156
  · exact gridGroup_geometry_157
  · exact gridGroup_geometry_158
  · exact gridGroup_geometry_159
  · exact gridGroup_geometry_160
  · exact gridGroup_geometry_161
  · exact gridGroup_geometry_162
  · exact gridGroup_geometry_163
  · exact gridGroup_geometry_164
  · exact gridGroup_geometry_165
  · exact gridGroup_geometry_166
  · exact gridGroup_geometry_167
  · exact gridGroup_geometry_168
  · exact gridGroup_geometry_169
  · exact gridGroup_geometry_170
  · exact gridGroup_geometry_171
  · exact gridGroup_geometry_172
  · exact gridGroup_geometry_173
  · exact gridGroup_geometry_174
  · exact gridGroup_geometry_175
  · exact gridGroup_geometry_176
  · exact gridGroup_geometry_177
  · exact gridGroup_geometry_178
  · exact gridGroup_geometry_179
  · exact gridGroup_geometry_180
  · exact gridGroup_geometry_181
  · exact gridGroup_geometry_182
  · exact gridGroup_geometry_183
  · exact gridGroup_geometry_184
  · exact gridGroup_geometry_185
  · exact gridGroup_geometry_186
  · exact gridGroup_geometry_187
  · exact gridGroup_geometry_188
  · exact gridGroup_geometry_189
  · exact gridGroup_geometry_190
  · exact gridGroup_geometry_191
  · exact gridGroup_geometry_192
  · exact gridGroup_geometry_193
  · exact gridGroup_geometry_194
  · exact gridGroup_geometry_195
  · exact gridGroup_geometry_196
  · exact gridGroup_geometry_197
  · exact gridGroup_geometry_198
  · exact gridGroup_geometry_199
  · exact gridGroup_geometry_200
  · exact gridGroup_geometry_201
  · exact gridGroup_geometry_202
  · exact gridGroup_geometry_203
  · exact gridGroup_geometry_204
  · exact gridGroup_geometry_205
  · exact gridGroup_geometry_206
  · exact gridGroup_geometry_207
  · exact gridGroup_geometry_208
  · exact gridGroup_geometry_209
  · exact gridGroup_geometry_210
  · exact gridGroup_geometry_211
  · exact gridGroup_geometry_212
  · exact gridGroup_geometry_213
  · exact gridGroup_geometry_214
  · exact gridGroup_geometry_215
  · exact gridGroup_geometry_216
  · exact gridGroup_geometry_217
  · exact gridGroup_geometry_218
  · exact gridGroup_geometry_219
  · exact gridGroup_geometry_220
  · exact gridGroup_geometry_221
  · exact gridGroup_geometry_222
  · exact gridGroup_geometry_223
  · exact gridGroup_geometry_224
  · exact gridGroup_geometry_225
  · exact gridGroup_geometry_226
  · exact gridGroup_geometry_227
  · exact gridGroup_geometry_228
  · exact gridGroup_geometry_229
  · exact gridGroup_geometry_230
  · exact gridGroup_geometry_231
  · exact gridGroup_geometry_232
  · exact gridGroup_geometry_233
  · exact gridGroup_geometry_234

theorem gridGroup_target_mod (i : Fin 235) :
    gridGroupPartner i%780=((gridGroupTarget i:ℕ):ℤ) := by
  fin_cases i <;> decide

theorem gridGroup_rate_pos (i : Fin 235) : 0<gridGroupRate i := by
  have hn : (sourceRaw (gridGroupSource i) 1 0:ℝ)*(((gridGroupIndex i:ℕ):ℝ)/780)+
      (sourceRaw (gridGroupSource i) 1 1:ℝ)≠0 := by
    simpa only [mul_div_assoc] using (gridGroup_geometry i).1
  have hp : 0<sourceRate (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780) :=
    div_pos (sq_pos_of_ne_zero hn) (by exact_mod_cast source_det_pos (gridGroupSource i))
  rw [(gridGroup_geometry i).2.2.1] at hp
  exact_mod_cast hp

theorem gridGroup_partner_transform (k : ℕ) (f : ℕ→ℂ) (i : Fin 235) (s : ℂ) :
    original k f (sourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/780)) s=
      grid k f 780 ((gridGroupTarget i:ℕ):ℤ) s := by
  rw [(gridGroup_geometry i).2.1]
  change grid k f 780 (gridGroupPartner i) s=_
  rw [← grid_mod k f (by decide : 0<780)]
  norm_num only [Nat.cast_ofNat]
  rw [gridGroup_target_mod]

#print axioms gridGroup_geometry
#print axioms gridGroup_partner_transform

end SmallLevelTwentySixGrid
