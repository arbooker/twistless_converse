module
public import SmallLevelTwentyTwoThirdJetTriangularIndexBundleSeriesV4
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoThirdJetTriangular
open SmallLevelTwentyTwoThirdJet

theorem kernel1 (w : Fin 264→ℂ) (hw : ∀ i, rows1 w i=0) : w=0 := by
  have z251 : w 251=0 := by
    have h:=pivot1_263 w hw
    linear_combination h
  have z245 : w 245=0 := by
    have h:=pivot1_262 w hw
    linear_combination h
  have z239 : w 239=0 := by
    have h:=pivot1_261 w hw
    linear_combination h
  have z248 : w 248=0 := by
    have h:=pivot1_260 w hw
    linear_combination h
  have z212 : w 212=0 := by
    have h:=pivot1_259 w hw
    linear_combination h
  have z238 : w 238=0 := by
    have h:=pivot1_258 w hw
    linear_combination h
  have z223 : w 223=0 := by
    have h:=pivot1_257 w hw
    linear_combination h
  have z247 : w 247=0 := by
    have h:=pivot1_256 w hw
    linear_combination h
  have z217 : w 217=0 := by
    have h:=pivot1_255 w hw
    linear_combination h
  have z250 : w 250=0 := by
    have h:=pivot1_254 w hw
    linear_combination h
  have z211 : w 211=0 := by
    have h:=pivot1_253 w hw
    linear_combination h
  have z224 : w 224=0 := by
    have h:=pivot1_252 w hw
    linear_combination h
  have z241 : w 241=0 := by
    have h:=pivot1_251 w hw
    linear_combination h
  have z221 : w 221=0 := by
    have h:=pivot1_250 w hw
    linear_combination h
  have z246 : w 246=0 := by
    have h:=pivot1_249 w hw
    linear_combination h
  have z219 : w 219=0 := by
    have h:=pivot1_248 w hw
    linear_combination h - ((-1309)/48)*z246
  have z254 : w 254=0 := by
    have h:=pivot1_247 w hw
    linear_combination h - ((-1377)/16)*z246
  have z252 : w 252=0 := by
    have h:=pivot1_246 w hw
    linear_combination h - (351/16)*z246
  have z208 : w 208=0 := by
    have h:=pivot1_245 w hw
    linear_combination h - (1377/16)*z246
  have z218 : w 218=0 := by
    have h:=pivot1_244 w hw
    linear_combination h - (239/3)*z246
  have z244 : w 244=0 := by
    have h:=pivot1_243 w hw
    linear_combination h - ((-239)/3)*z246
  have z242 : w 242=0 := by
    have h:=pivot1_242 w hw
    linear_combination h - (108/121)*z246
  have z243 : w 243=0 := by
    have h:=pivot1_241 w hw
    linear_combination h - (1)*z219
  have z203 : w 203=0 := by
    have h:=pivot1_240 w hw
    linear_combination h - ((-324))*z246
  have z229 : w 229=0 := by
    have h:=pivot1_239 w hw
    linear_combination h - ((-324))*z252
  have z227 : w 227=0 := by
    have h:=pivot1_238 w hw
    linear_combination h - (484)*z242
  have z226 : w 226=0 := by
    have h:=pivot1_237 w hw
    linear_combination h - (81/4)*z246
  have z176 : w 176=0 := by
    have h:=pivot1_236 w hw
    linear_combination h
  have z222 : w 222=0 := by
    have h:=pivot1_235 w hw
    linear_combination h - ((-682)/81)*z176 - (121/81)*z242
  have z206 : w 206=0 := by
    have h:=pivot1_234 w hw
    linear_combination h - ((-81)/4)*z219 - (715/6)*z176
  have z205 : w 205=0 := by
    have h:=pivot1_233 w hw
    linear_combination h - ((-13904)/3)*z176 - (324)*z252
  have z257 : w 257=0 := by
    have h:=pivot1_232 w hw
    linear_combination h - ((-324))*z252 - ((-3806)/3)*z176
  have z256 : w 256=0 := by
    have h:=pivot1_231 w hw
    linear_combination h - ((-81)/4)*z243 - (715/6)*z176
  have z240 : w 240=0 := by
    have h:=pivot1_230 w hw
    linear_combination h - ((-682)/81)*z176 - ((-121)/81)*z242
  have z210 : w 210=0 := by
    have h:=pivot1_229 w hw
    linear_combination h - (1)*z252 - ((-187)/18)*z176
  have z236 : w 236=0 := by
    have h:=pivot1_228 w hw
    linear_combination h - (220)*z176 - ((-81)/4)*z246
  have z235 : w 235=0 := by
    have h:=pivot1_227 w hw
    linear_combination h - ((-324))*z240 - ((-1034))*z176
  have z225 : w 225=0 := by
    have h:=pivot1_226 w hw
    linear_combination h - (374/9)*z176 - ((-4))*z210
  have z259 : w 259=0 := by
    have h:=pivot1_225 w hw
    linear_combination h - ((-2376))*z176 - (324)*z246
  have z233 : w 233=0 := by
    have h:=pivot1_224 w hw
    linear_combination h - (3410/3)*z176 - ((-324))*z210
  have z260 : w 260=0 := by
    have h:=pivot1_223 w hw
    linear_combination h - ((-81))*z210 - (1672/3)*z176
  have z202 : w 202=0 := by
    have h:=pivot1_222 w hw
    linear_combination h - ((-81))*z252 - (1672/3)*z176
  have z255 : w 255=0 := by
    have h:=pivot1_221 w hw
    linear_combination h - ((-484)/81)*z242 - (1430/81)*z176
  have z216 : w 216=0 := by
    have h:=pivot1_220 w hw
    linear_combination h - ((-374)/81)*z176 - (1)*z246
  have z253 : w 253=0 := by
    have h:=pivot1_219 w hw
    linear_combination h - ((-324)/121)*z246 - (68/11)*z176
  have z207 : w 207=0 := by
    have h:=pivot1_218 w hw
    linear_combination h - (484/81)*z242 - (1430/81)*z176
  have z185 : w 185=0 := by
    have h:=pivot1_217 w hw
    linear_combination h - (1)*z176
  have z179 : w 179=0 := by
    have h:=pivot1_216 w hw
    linear_combination h - (2/3)*z176
  have z173 : w 173=0 := by
    have h:=pivot1_215 w hw
    linear_combination h - ((-1))*z176
  have z182 : w 182=0 := by
    have h:=pivot1_214 w hw
    linear_combination h - (2/3)*z176
  have z146 : w 146=0 := by
    have h:=pivot1_213 w hw
    linear_combination h - (28/3)*z176
  have z172 : w 172=0 := by
    have h:=pivot1_212 w hw
    linear_combination h - (2)*z176
  have z157 : w 157=0 := by
    have h:=pivot1_211 w hw
    linear_combination h - (1)*z176
  have z181 : w 181=0 := by
    have h:=pivot1_210 w hw
    linear_combination h - (2/3)*z176
  have z151 : w 151=0 := by
    have h:=pivot1_209 w hw
    linear_combination h - ((-2)/3)*z176
  have z184 : w 184=0 := by
    have h:=pivot1_208 w hw
    linear_combination h - ((-28)/3)*z176
  have z145 : w 145=0 := by
    have h:=pivot1_207 w hw
    linear_combination h - ((-1))*z176
  have z158 : w 158=0 := by
    have h:=pivot1_206 w hw
    linear_combination h - ((-2))*z176
  have z175 : w 175=0 := by
    have h:=pivot1_205 w hw
    linear_combination h - (20)*z176
  have z155 : w 155=0 := by
    have h:=pivot1_204 w hw
    linear_combination h - ((-20))*z176
  have z57 : w 57=0 := by
    have h:=pivot1_203 w hw
    linear_combination h - (1/242)*z176
  have z177 : w 177=0 := by
    have h:=pivot1_202 w hw
    linear_combination h - ((-48521)/36)*z57 - ((-473)/72)*z176
  have z188 : w 188=0 := by
    have h:=pivot1_201 w hw
    linear_combination h - (55/8)*z176 - ((-3025)/4)*z57
  have z144 : w 144=0 := by
    have h:=pivot1_200 w hw
    linear_combination h - (4961/4)*z57 - (33/8)*z176
  have z142 : w 142=0 := by
    have h:=pivot1_199 w hw
    linear_combination h - (3025/4)*z57 - ((-55)/8)*z176
  have z152 : w 152=0 := by
    have h:=pivot1_198 w hw
    linear_combination h - (1573/9)*z57 - ((-77)/18)*z176
  have z178 : w 178=0 := by
    have h:=pivot1_197 w hw
    linear_combination h - ((-1573)/9)*z57 - (77/18)*z176
  have z180 : w 180=0 := by
    have h:=pivot1_196 w hw
    linear_combination h - (11/18)*z176 - ((-121)/9)*z57
  have z137 : w 137=0 := by
    have h:=pivot1_195 w hw
    linear_combination h - ((-18))*z180 - ((-726))*z57
  have z163 : w 163=0 := by
    have h:=pivot1_194 w hw
    linear_combination h - (968/3)*z57 - (18)*z144
  have z161 : w 161=0 := by
    have h:=pivot1_193 w hw
    linear_combination h - (2178)*z57 - (22)*z176
  have z160 : w 160=0 := by
    have h:=pivot1_192 w hw
    linear_combination h - (484)*z57 - (9/2)*z180
  have z140 : w 140=0 := by
    have h:=pivot1_191 w hw
    linear_combination h - (1573/3)*z57 - (9/2)*z177
  have z139 : w 139=0 := by
    have h:=pivot1_190 w hw
    linear_combination h - ((-18))*z144 - (1936/3)*z57
  have z191 : w 191=0 := by
    have h:=pivot1_189 w hw
    linear_combination h - ((-1936)/3)*z57 - (18)*z144
  have z190 : w 190=0 := by
    have h:=pivot1_188 w hw
    linear_combination h - ((-9)/2)*z177 - ((-1573)/3)*z57
  have z174 : w 174=0 := by
    have h:=pivot1_187 w hw
    linear_combination h - ((-484)/9)*z57 - ((-11)/9)*z176
  have z170 : w 170=0 := by
    have h:=pivot1_186 w hw
    linear_combination h - ((-484))*z57 - ((-9)/2)*z180
  have z169 : w 169=0 := by
    have h:=pivot1_185 w hw
    linear_combination h - ((-18))*z174 - ((-1210))*z57
  have z193 : w 193=0 := by
    have h:=pivot1_184 w hw
    linear_combination h - (726)*z57 - (18)*z180
  have z153 : w 153=0 := by
    have h:=pivot1_183 w hw
    linear_combination h - (1)*z177
  have z159 : w 159=0 := by
    have h:=pivot1_182 w hw
    linear_combination h - ((-2))*z144
  have z194 : w 194=0 := by
    have h:=pivot1_181 w hw
    linear_combination h - ((-9))*z144 - ((-484)/3)*z57
  have z136 : w 136=0 := by
    have h:=pivot1_180 w hw
    linear_combination h - (484/3)*z57 - (9)*z144
  have z189 : w 189=0 := by
    have h:=pivot1_179 w hw
    linear_combination h - ((-242)/9)*z57 - ((-22)/9)*z176
  have z156 : w 156=0 := by
    have h:=pivot1_178 w hw
    linear_combination h - (1)*z174
  have z183 : w 183=0 := by
    have h:=pivot1_177 w hw
    linear_combination h - ((-1))*z180
  have z187 : w 187=0 := by
    have h:=pivot1_176 w hw
    linear_combination h - ((-18)/11)*z180 - (22)*z57
  have z141 : w 141=0 := by
    have h:=pivot1_175 w hw
    linear_combination h - (22/9)*z176 - (242/9)*z57
  have z186 : w 186=0 := by
    have h:=pivot1_174 w hw
    linear_combination h - (1)*z144
  have z167 : w 167=0 := by
    have h:=pivot1_173 w hw
    linear_combination h - ((-2))*z194
  have z119 : w 119=0 := by
    have h:=pivot1_172 w hw
    linear_combination h - (44/3)*z57
  have z113 : w 113=0 := by
    have h:=pivot1_171 w hw
    linear_combination h - (110/9)*z57
  have z107 : w 107=0 := by
    have h:=pivot1_170 w hw
    linear_combination h - ((-22))*z57
  have z116 : w 116=0 := by
    have h:=pivot1_169 w hw
    linear_combination h - ((-22)/9)*z57
  have z80 : w 80=0 := by
    have h:=pivot1_168 w hw
    linear_combination h - (88/9)*z57
  have z106 : w 106=0 := by
    have h:=pivot1_167 w hw
    linear_combination h - ((-22))*z57
  have z91 : w 91=0 := by
    have h:=pivot1_166 w hw
    linear_combination h - ((-22))*z57
  have z115 : w 115=0 := by
    have h:=pivot1_165 w hw
    linear_combination h - (22/9)*z57
  have z85 : w 85=0 := by
    have h:=pivot1_164 w hw
    linear_combination h - (110/9)*z57
  have z118 : w 118=0 := by
    have h:=pivot1_163 w hw
    linear_combination h - (88/9)*z57
  have z79 : w 79=0 := by
    have h:=pivot1_162 w hw
    linear_combination h - (44/3)*z57
  have z92 : w 92=0 := by
    have h:=pivot1_161 w hw
    linear_combination h - ((-22))*z57
  have z109 : w 109=0 := by
    have h:=pivot1_160 w hw
    linear_combination h - ((-44)/3)*z57
  have z89 : w 89=0 := by
    have h:=pivot1_159 w hw
    linear_combination h - ((-44)/3)*z57
  have z110 : w 110=0 := by
    have h:=pivot1_158 w hw
    linear_combination h
  have z87 : w 87=0 := by
    have h:=pivot1_157 w hw
    linear_combination h - (22/3)*z57 - (2)*z110
  have z120 : w 120=0 := by
    have h:=pivot1_156 w hw
    linear_combination h - (22/3)*z57 - ((-1))*z110
  have z111 : w 111=0 := by
    have h:=pivot1_155 w hw
    linear_combination h - (1)*z87 - (44/3)*z57
  have z86 : w 86=0 := by
    have h:=pivot1_154 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z112 : w 112=0 := by
    have h:=pivot1_153 w hw
    linear_combination h - (22/3)*z57 - ((-1))*z110
  have z97 : w 97=0 := by
    have h:=pivot1_152 w hw
    linear_combination h - ((-1))*z120 - ((-44)/9)*z57
  have z95 : w 95=0 := by
    have h:=pivot1_151 w hw
    linear_combination h - ((-22))*z57 - (1)*z110
  have z90 : w 90=0 := by
    have h:=pivot1_150 w hw
    linear_combination h - ((-44)/3)*z57 - (1)*z110
  have z74 : w 74=0 := by
    have h:=pivot1_149 w hw
    linear_combination h - ((-1))*z87 - (154/9)*z57
  have z73 : w 73=0 := by
    have h:=pivot1_148 w hw
    linear_combination h - (176/9)*z57 - (1)*z120
  have z125 : w 125=0 := by
    have h:=pivot1_147 w hw
    linear_combination h - ((-1))*z120 - (44/9)*z57
  have z124 : w 124=0 := by
    have h:=pivot1_146 w hw
    linear_combination h - ((-1))*z111 - (154/9)*z57
  have z122 : w 122=0 := by
    have h:=pivot1_145 w hw
    linear_combination h - (22/3)*z57
  have z76 : w 76=0 := by
    have h:=pivot1_144 w hw
    linear_combination h - (22/3)*z57
  have z71 : w 71=0 := by
    have h:=pivot1_143 w hw
    linear_combination h - (44/3)*z57
  have z94 : w 94=0 := by
    have h:=pivot1_142 w hw
    linear_combination h - ((-22))*z57
  have z114 : w 114=0 := by
    have h:=pivot1_141 w hw
    linear_combination h - (22/3)*z57
  have z108 : w 108=0 := by
    have h:=pivot1_140 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z110
  have z78 : w 78=0 := by
    have h:=pivot1_139 w hw
    linear_combination h - (1)*z120 - (44/3)*z57
  have z104 : w 104=0 := by
    have h:=pivot1_138 w hw
    linear_combination h - ((-88)/3)*z57 - ((-1))*z114
  have z103 : w 103=0 := by
    have h:=pivot1_137 w hw
    linear_combination h - ((-1))*z108 - ((-22)/3)*z57
  have z93 : w 93=0 := by
    have h:=pivot1_136 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z78
  have z127 : w 127=0 := by
    have h:=pivot1_135 w hw
    linear_combination h - (22)*z57 - (1)*z114
  have z101 : w 101=0 := by
    have h:=pivot1_134 w hw
    linear_combination h - ((-44)/9)*z57 - ((-1))*z78
  have z128 : w 128=0 := by
    have h:=pivot1_133 w hw
    linear_combination h - ((-1))*z78 - ((-88)/9)*z57
  have z70 : w 70=0 := by
    have h:=pivot1_132 w hw
    linear_combination h - ((-1))*z120 - ((-88)/9)*z57
  have z123 : w 123=0 := by
    have h:=pivot1_131 w hw
    linear_combination h - (22/3)*z57 - ((-1))*z110
  have z117 : w 117=0 := by
    have h:=pivot1_130 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z114
  have z121 : w 121=0 := by
    have h:=pivot1_129 w hw
    linear_combination h - ((-1))*z114 - ((-22)/3)*z57
  have z75 : w 75=0 := by
    have h:=pivot1_128 w hw
    linear_combination h - (1)*z110 - (22/3)*z57
  have z237 : w 237=0 := by
    have h:=pivot1_127 w hw
    linear_combination h - (4)*z210
  have z249 : w 249=0 := by
    have h:=pivot1_126 w hw
    linear_combination h - (1)*z216
  have z215 : w 215=0 := by
    have h:=pivot1_125 w hw
    linear_combination h - (1)*z248
  have z214 : w 214=0 := by
    have h:=pivot1_124 w hw
    linear_combination h - (1)*z247
  have z213 : w 213=0 := by
    have h:=pivot1_123 w hw
    linear_combination h - (1)*z246
  have z209 : w 209=0 := by
    have h:=pivot1_122 w hw
    linear_combination h - (1)*z253
  have z220 : w 220=0 := by
    have h:=pivot1_121 w hw
    linear_combination h - (1)*z242
  have z171 : w 171=0 := by
    have h:=pivot1_120 w hw
    linear_combination h - (2)*z144
  have z150 : w 150=0 := by
    have h:=pivot1_119 w hw
    linear_combination h - (1)*z183
  have z149 : w 149=0 := by
    have h:=pivot1_118 w hw
    linear_combination h - (1)*z182
  have z148 : w 148=0 := by
    have h:=pivot1_117 w hw
    linear_combination h - (1)*z181
  have z147 : w 147=0 := by
    have h:=pivot1_116 w hw
    linear_combination h - (1)*z180
  have z143 : w 143=0 := by
    have h:=pivot1_115 w hw
    linear_combination h - (1)*z187
  have z154 : w 154=0 := by
    have h:=pivot1_114 w hw
    linear_combination h - (1)*z176
  have z105 : w 105=0 := by
    have h:=pivot1_113 w hw
    linear_combination h - (1)*z78
  have z84 : w 84=0 := by
    have h:=pivot1_112 w hw
    linear_combination h - (1)*z117
  have z83 : w 83=0 := by
    have h:=pivot1_111 w hw
    linear_combination h - (1)*z116
  have z82 : w 82=0 := by
    have h:=pivot1_110 w hw
    linear_combination h - (1)*z115
  have z81 : w 81=0 := by
    have h:=pivot1_109 w hw
    linear_combination h - (1)*z114
  have z77 : w 77=0 := by
    have h:=pivot1_108 w hw
    linear_combination h - (1)*z121
  have z88 : w 88=0 := by
    have h:=pivot1_107 w hw
    linear_combination h - (1)*z110
  have z53 : w 53=0 := by
    have h:=pivot1_106 w hw
    linear_combination h - ((-5)/3)*z57
  have z47 : w 47=0 := by
    have h:=pivot1_105 w hw
    linear_combination h - ((-62)/27)*z57
  have z41 : w 41=0 := by
    have h:=pivot1_104 w hw
    linear_combination h - ((-13)/9)*z57
  have z50 : w 50=0 := by
    have h:=pivot1_103 w hw
    linear_combination h - ((-50)/27)*z57
  have z14 : w 14=0 := by
    have h:=pivot1_102 w hw
    linear_combination h - (56/27)*z57
  have z40 : w 40=0 := by
    have h:=pivot1_101 w hw
    linear_combination h - ((-10)/9)*z57
  have z25 : w 25=0 := by
    have h:=pivot1_100 w hw
    linear_combination h - (13/9)*z57
  have z49 : w 49=0 := by
    have h:=pivot1_99 w hw
    linear_combination h - ((-50)/27)*z57
  have z19 : w 19=0 := by
    have h:=pivot1_98 w hw
    linear_combination h - (62/27)*z57
  have z52 : w 52=0 := by
    have h:=pivot1_97 w hw
    linear_combination h - ((-56)/27)*z57
  have z13 : w 13=0 := by
    have h:=pivot1_96 w hw
    linear_combination h - (5/3)*z57
  have z26 : w 26=0 := by
    have h:=pivot1_95 w hw
    linear_combination h - (10/9)*z57
  have z43 : w 43=0 := by
    have h:=pivot1_94 w hw
    linear_combination h - ((-20)/9)*z57
  have z23 : w 23=0 := by
    have h:=pivot1_93 w hw
    linear_combination h - (20/9)*z57
  have z21 : w 21=0 := by
    have h:=pivot1_92 w hw
    linear_combination h - (7/3)*z57
  have z56 : w 56=0 := by
    have h:=pivot1_91 w hw
    linear_combination h - ((-10)/9)*z57
  have z12 : w 12=0 := by
    have h:=pivot1_90 w hw
    linear_combination h - (4/3)*z57
  have z10 : w 10=0 := by
    have h:=pivot1_89 w hw
    linear_combination h - (10/9)*z57
  have z45 : w 45=0 := by
    have h:=pivot1_88 w hw
    linear_combination h - (1)*z21
  have z51 : w 51=0 := by
    have h:=pivot1_87 w hw
    linear_combination h - ((-2))*z57
  have z17 : w 17=0 := by
    have h:=pivot1_86 w hw
    linear_combination h - (1)*z50
  have z16 : w 16=0 := by
    have h:=pivot1_85 w hw
    linear_combination h - (1)*z49
  have z15 : w 15=0 := by
    have h:=pivot1_84 w hw
    linear_combination h - (2)*z57
  have z20 : w 20=0 := by
    have h:=pivot1_83 w hw
    linear_combination h - (20/9)*z57
  have z46 : w 46=0 := by
    have h:=pivot1_82 w hw
    linear_combination h - ((-20)/9)*z57
  have z48 : w 48=0 := by
    have h:=pivot1_81 w hw
    linear_combination h - ((-2))*z57
  have z54 : w 54=0 := by
    have h:=pivot1_80 w hw
    linear_combination h - (1)*z12
  have z18 : w 18=0 := by
    have h:=pivot1_79 w hw
    linear_combination h - (1)*z48
  have z44 : w 44=0 := by
    have h:=pivot1_78 w hw
    linear_combination h - ((-22)/9)*z57
  have z5 : w 5=0 := by
    have h:=pivot1_77 w hw
    linear_combination h - ((-1)/18)*z48
  have z31 : w 31=0 := by
    have h:=pivot1_76 w hw
    linear_combination h - ((-1)/18)*z54
  have z29 : w 29=0 := by
    have h:=pivot1_75 w hw
    linear_combination h - (1/22)*z44
  have z28 : w 28=0 := by
    have h:=pivot1_74 w hw
    linear_combination h - ((-2)/9)*z15
  have z24 : w 24=0 := by
    have h:=pivot1_73 w hw
    linear_combination h - (9/11)*z44
  have z8 : w 8=0 := by
    have h:=pivot1_72 w hw
    linear_combination h - ((-2)/9)*z21
  have z7 : w 7=0 := by
    have h:=pivot1_71 w hw
    linear_combination h - ((-1)/18)*z12
  have z59 : w 59=0 := by
    have h:=pivot1_70 w hw
    linear_combination h - ((-1)/18)*z54
  have z58 : w 58=0 := by
    have h:=pivot1_69 w hw
    linear_combination h - ((-2)/9)*z45
  have z42 : w 42=0 := by
    have h:=pivot1_68 w hw
    linear_combination h - ((-2))*z57
  have z39 : w 39=0 := by
    have h:=pivot1_67 w hw
    linear_combination h - ((-1)/2)*z54
  have z38 : w 38=0 := by
    have h:=pivot1_66 w hw
    linear_combination h - ((-2)/9)*z51
  have z37 : w 37=0 := by
    have h:=pivot1_65 w hw
    linear_combination h - ((-1)/18)*z42
  have z27 : w 27=0 := by
    have h:=pivot1_64 w hw
    linear_combination h - ((-1)/2)*z12
  have z61 : w 61=0 := by
    have h:=pivot1_63 w hw
    linear_combination h - ((-1)/18)*z18
  have z35 : w 35=0 := by
    have h:=pivot1_62 w hw
    linear_combination h - ((-1)/18)*z12
  have z62 : w 62=0 := by
    have h:=pivot1_61 w hw
    linear_combination h - ((-1)/9)*z12
  have z4 : w 4=0 := by
    have h:=pivot1_60 w hw
    linear_combination h - ((-1)/9)*z54
  have z22 : w 22=0 := by
    have h:=pivot1_59 w hw
    linear_combination h - (22/9)*z57
  have z55 : w 55=0 := by
    have h:=pivot1_58 w hw
    linear_combination h - (11/18)*z18
  have z11 : w 11=0 := by
    have h:=pivot1_57 w hw
    linear_combination h - (11/18)*z48
  have z9 : w 9=0 := by
    have h:=pivot1_56 w hw
    linear_combination h - (9/22)*z44
  have z234 : w 234=0 := by
    have h:=pivot1_55 w hw
    linear_combination h
  have z230 : w 230=0 := by
    have h:=pivot1_54 w hw
    linear_combination h
  have z232 : w 232=0 := by
    have h:=pivot1_53 w hw
    linear_combination h
  have z258 : w 258=0 := by
    have h:=pivot1_52 w hw
    linear_combination h
  have z204 : w 204=0 := by
    have h:=pivot1_51 w hw
    linear_combination h
  have z200 : w 200=0 := by
    have h:=pivot1_50 w hw
    linear_combination h
  have z262 : w 262=0 := by
    have h:=pivot1_49 w hw
    linear_combination h
  have z231 : w 231=0 := by
    have h:=pivot1_48 w hw
    linear_combination h
  have z228 : w 228=0 := by
    have h:=pivot1_47 w hw
    linear_combination h
  have z263 : w 263=0 := by
    have h:=pivot1_46 w hw
    linear_combination h
  have z201 : w 201=0 := by
    have h:=pivot1_45 w hw
    linear_combination h
  have z199 : w 199=0 := by
    have h:=pivot1_44 w hw
    linear_combination h
  have z261 : w 261=0 := by
    have h:=pivot1_43 w hw
    linear_combination h
  have z198 : w 198=0 := by
    have h:=pivot1_42 w hw
    linear_combination h
  have z168 : w 168=0 := by
    have h:=pivot1_41 w hw
    linear_combination h
  have z164 : w 164=0 := by
    have h:=pivot1_40 w hw
    linear_combination h
  have z166 : w 166=0 := by
    have h:=pivot1_39 w hw
    linear_combination h
  have z192 : w 192=0 := by
    have h:=pivot1_38 w hw
    linear_combination h
  have z138 : w 138=0 := by
    have h:=pivot1_37 w hw
    linear_combination h
  have z134 : w 134=0 := by
    have h:=pivot1_36 w hw
    linear_combination h
  have z196 : w 196=0 := by
    have h:=pivot1_35 w hw
    linear_combination h
  have z165 : w 165=0 := by
    have h:=pivot1_34 w hw
    linear_combination h
  have z162 : w 162=0 := by
    have h:=pivot1_33 w hw
    linear_combination h
  have z197 : w 197=0 := by
    have h:=pivot1_32 w hw
    linear_combination h
  have z135 : w 135=0 := by
    have h:=pivot1_31 w hw
    linear_combination h
  have z133 : w 133=0 := by
    have h:=pivot1_30 w hw
    linear_combination h
  have z195 : w 195=0 := by
    have h:=pivot1_29 w hw
    linear_combination h
  have z132 : w 132=0 := by
    have h:=pivot1_28 w hw
    linear_combination h
  have z102 : w 102=0 := by
    have h:=pivot1_27 w hw
    linear_combination h
  have z98 : w 98=0 := by
    have h:=pivot1_26 w hw
    linear_combination h
  have z100 : w 100=0 := by
    have h:=pivot1_25 w hw
    linear_combination h
  have z126 : w 126=0 := by
    have h:=pivot1_24 w hw
    linear_combination h
  have z72 : w 72=0 := by
    have h:=pivot1_23 w hw
    linear_combination h
  have z68 : w 68=0 := by
    have h:=pivot1_22 w hw
    linear_combination h
  have z130 : w 130=0 := by
    have h:=pivot1_21 w hw
    linear_combination h
  have z99 : w 99=0 := by
    have h:=pivot1_20 w hw
    linear_combination h
  have z96 : w 96=0 := by
    have h:=pivot1_19 w hw
    linear_combination h
  have z131 : w 131=0 := by
    have h:=pivot1_18 w hw
    linear_combination h
  have z69 : w 69=0 := by
    have h:=pivot1_17 w hw
    linear_combination h
  have z67 : w 67=0 := by
    have h:=pivot1_16 w hw
    linear_combination h
  have z129 : w 129=0 := by
    have h:=pivot1_15 w hw
    linear_combination h
  have z66 : w 66=0 := by
    have h:=pivot1_14 w hw
    linear_combination h
  have z36 : w 36=0 := by
    have h:=pivot1_13 w hw
    linear_combination h
  have z32 : w 32=0 := by
    have h:=pivot1_12 w hw
    linear_combination h
  have z34 : w 34=0 := by
    have h:=pivot1_11 w hw
    linear_combination h
  have z60 : w 60=0 := by
    have h:=pivot1_10 w hw
    linear_combination h
  have z6 : w 6=0 := by
    have h:=pivot1_9 w hw
    linear_combination h
  have z2 : w 2=0 := by
    have h:=pivot1_8 w hw
    linear_combination h
  have z64 : w 64=0 := by
    have h:=pivot1_7 w hw
    linear_combination h
  have z33 : w 33=0 := by
    have h:=pivot1_6 w hw
    linear_combination h
  have z30 : w 30=0 := by
    have h:=pivot1_5 w hw
    linear_combination h
  have z65 : w 65=0 := by
    have h:=pivot1_4 w hw
    linear_combination h
  have z3 : w 3=0 := by
    have h:=pivot1_3 w hw
    linear_combination h
  have z1 : w 1=0 := by
    have h:=pivot1_2 w hw
    linear_combination h
  have z63 : w 63=0 := by
    have h:=pivot1_1 w hw
    linear_combination h
  have z0 : w 0=0 := by
    have h:=pivot1_0 w hw
    linear_combination h
  funext j
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4
  · exact z5
  · exact z6
  · exact z7
  · exact z8
  · exact z9
  · exact z10
  · exact z11
  · exact z12
  · exact z13
  · exact z14
  · exact z15
  · exact z16
  · exact z17
  · exact z18
  · exact z19
  · exact z20
  · exact z21
  · exact z22
  · exact z23
  · exact z24
  · exact z25
  · exact z26
  · exact z27
  · exact z28
  · exact z29
  · exact z30
  · exact z31
  · exact z32
  · exact z33
  · exact z34
  · exact z35
  · exact z36
  · exact z37
  · exact z38
  · exact z39
  · exact z40
  · exact z41
  · exact z42
  · exact z43
  · exact z44
  · exact z45
  · exact z46
  · exact z47
  · exact z48
  · exact z49
  · exact z50
  · exact z51
  · exact z52
  · exact z53
  · exact z54
  · exact z55
  · exact z56
  · exact z57
  · exact z58
  · exact z59
  · exact z60
  · exact z61
  · exact z62
  · exact z63
  · exact z64
  · exact z65
  · exact z66
  · exact z67
  · exact z68
  · exact z69
  · exact z70
  · exact z71
  · exact z72
  · exact z73
  · exact z74
  · exact z75
  · exact z76
  · exact z77
  · exact z78
  · exact z79
  · exact z80
  · exact z81
  · exact z82
  · exact z83
  · exact z84
  · exact z85
  · exact z86
  · exact z87
  · exact z88
  · exact z89
  · exact z90
  · exact z91
  · exact z92
  · exact z93
  · exact z94
  · exact z95
  · exact z96
  · exact z97
  · exact z98
  · exact z99
  · exact z100
  · exact z101
  · exact z102
  · exact z103
  · exact z104
  · exact z105
  · exact z106
  · exact z107
  · exact z108
  · exact z109
  · exact z110
  · exact z111
  · exact z112
  · exact z113
  · exact z114
  · exact z115
  · exact z116
  · exact z117
  · exact z118
  · exact z119
  · exact z120
  · exact z121
  · exact z122
  · exact z123
  · exact z124
  · exact z125
  · exact z126
  · exact z127
  · exact z128
  · exact z129
  · exact z130
  · exact z131
  · exact z132
  · exact z133
  · exact z134
  · exact z135
  · exact z136
  · exact z137
  · exact z138
  · exact z139
  · exact z140
  · exact z141
  · exact z142
  · exact z143
  · exact z144
  · exact z145
  · exact z146
  · exact z147
  · exact z148
  · exact z149
  · exact z150
  · exact z151
  · exact z152
  · exact z153
  · exact z154
  · exact z155
  · exact z156
  · exact z157
  · exact z158
  · exact z159
  · exact z160
  · exact z161
  · exact z162
  · exact z163
  · exact z164
  · exact z165
  · exact z166
  · exact z167
  · exact z168
  · exact z169
  · exact z170
  · exact z171
  · exact z172
  · exact z173
  · exact z174
  · exact z175
  · exact z176
  · exact z177
  · exact z178
  · exact z179
  · exact z180
  · exact z181
  · exact z182
  · exact z183
  · exact z184
  · exact z185
  · exact z186
  · exact z187
  · exact z188
  · exact z189
  · exact z190
  · exact z191
  · exact z192
  · exact z193
  · exact z194
  · exact z195
  · exact z196
  · exact z197
  · exact z198
  · exact z199
  · exact z200
  · exact z201
  · exact z202
  · exact z203
  · exact z204
  · exact z205
  · exact z206
  · exact z207
  · exact z208
  · exact z209
  · exact z210
  · exact z211
  · exact z212
  · exact z213
  · exact z214
  · exact z215
  · exact z216
  · exact z217
  · exact z218
  · exact z219
  · exact z220
  · exact z221
  · exact z222
  · exact z223
  · exact z224
  · exact z225
  · exact z226
  · exact z227
  · exact z228
  · exact z229
  · exact z230
  · exact z231
  · exact z232
  · exact z233
  · exact z234
  · exact z235
  · exact z236
  · exact z237
  · exact z238
  · exact z239
  · exact z240
  · exact z241
  · exact z242
  · exact z243
  · exact z244
  · exact z245
  · exact z246
  · exact z247
  · exact z248
  · exact z249
  · exact z250
  · exact z251
  · exact z252
  · exact z253
  · exact z254
  · exact z255
  · exact z256
  · exact z257
  · exact z258
  · exact z259
  · exact z260
  · exact z261
  · exact z262
  · exact z263

#print axioms kernel1

theorem kernel2 (w : Fin 264→ℂ) (hw : ∀ i, rows2 w i=0) : w=0 := by
  have z251 : w 251=0 := by
    have h:=pivot2_263 w hw
    linear_combination h
  have z245 : w 245=0 := by
    have h:=pivot2_262 w hw
    linear_combination h
  have z239 : w 239=0 := by
    have h:=pivot2_261 w hw
    linear_combination h
  have z248 : w 248=0 := by
    have h:=pivot2_260 w hw
    linear_combination h
  have z212 : w 212=0 := by
    have h:=pivot2_259 w hw
    linear_combination h
  have z238 : w 238=0 := by
    have h:=pivot2_258 w hw
    linear_combination h
  have z223 : w 223=0 := by
    have h:=pivot2_257 w hw
    linear_combination h
  have z247 : w 247=0 := by
    have h:=pivot2_256 w hw
    linear_combination h
  have z217 : w 217=0 := by
    have h:=pivot2_255 w hw
    linear_combination h
  have z250 : w 250=0 := by
    have h:=pivot2_254 w hw
    linear_combination h
  have z211 : w 211=0 := by
    have h:=pivot2_253 w hw
    linear_combination h
  have z224 : w 224=0 := by
    have h:=pivot2_252 w hw
    linear_combination h
  have z241 : w 241=0 := by
    have h:=pivot2_251 w hw
    linear_combination h
  have z221 : w 221=0 := by
    have h:=pivot2_250 w hw
    linear_combination h
  have z246 : w 246=0 := by
    have h:=pivot2_249 w hw
    linear_combination h
  have z219 : w 219=0 := by
    have h:=pivot2_248 w hw
    linear_combination h - ((-1309)/48)*z246
  have z254 : w 254=0 := by
    have h:=pivot2_247 w hw
    linear_combination h - ((-1377)/16)*z246
  have z252 : w 252=0 := by
    have h:=pivot2_246 w hw
    linear_combination h - (351/16)*z246
  have z208 : w 208=0 := by
    have h:=pivot2_245 w hw
    linear_combination h - (1377/16)*z246
  have z218 : w 218=0 := by
    have h:=pivot2_244 w hw
    linear_combination h - (239/3)*z246
  have z244 : w 244=0 := by
    have h:=pivot2_243 w hw
    linear_combination h - ((-239)/3)*z246
  have z242 : w 242=0 := by
    have h:=pivot2_242 w hw
    linear_combination h - ((-108)/121)*z246
  have z243 : w 243=0 := by
    have h:=pivot2_241 w hw
    linear_combination h - (1)*z219
  have z203 : w 203=0 := by
    have h:=pivot2_240 w hw
    linear_combination h - ((-324))*z246
  have z229 : w 229=0 := by
    have h:=pivot2_239 w hw
    linear_combination h - ((-324))*z252
  have z227 : w 227=0 := by
    have h:=pivot2_238 w hw
    linear_combination h - ((-484))*z242
  have z226 : w 226=0 := by
    have h:=pivot2_237 w hw
    linear_combination h - (81/4)*z246
  have z176 : w 176=0 := by
    have h:=pivot2_236 w hw
    linear_combination h
  have z222 : w 222=0 := by
    have h:=pivot2_235 w hw
    linear_combination h - (682/81)*z176 - ((-121)/81)*z242
  have z206 : w 206=0 := by
    have h:=pivot2_234 w hw
    linear_combination h - ((-81)/4)*z219 - ((-715)/6)*z176
  have z205 : w 205=0 := by
    have h:=pivot2_233 w hw
    linear_combination h - (13904/3)*z176 - (324)*z252
  have z257 : w 257=0 := by
    have h:=pivot2_232 w hw
    linear_combination h - ((-324))*z252 - (3806/3)*z176
  have z256 : w 256=0 := by
    have h:=pivot2_231 w hw
    linear_combination h - ((-81)/4)*z243 - ((-715)/6)*z176
  have z240 : w 240=0 := by
    have h:=pivot2_230 w hw
    linear_combination h - (682/81)*z176 - (121/81)*z242
  have z210 : w 210=0 := by
    have h:=pivot2_229 w hw
    linear_combination h - (1)*z252 - (187/18)*z176
  have z236 : w 236=0 := by
    have h:=pivot2_228 w hw
    linear_combination h - ((-220))*z176 - ((-81)/4)*z246
  have z235 : w 235=0 := by
    have h:=pivot2_227 w hw
    linear_combination h - ((-324))*z240 - (1034)*z176
  have z225 : w 225=0 := by
    have h:=pivot2_226 w hw
    linear_combination h - ((-374)/9)*z176 - ((-4))*z210
  have z259 : w 259=0 := by
    have h:=pivot2_225 w hw
    linear_combination h - (2376)*z176 - (324)*z246
  have z233 : w 233=0 := by
    have h:=pivot2_224 w hw
    linear_combination h - ((-3410)/3)*z176 - ((-324))*z210
  have z260 : w 260=0 := by
    have h:=pivot2_223 w hw
    linear_combination h - ((-81))*z210 - ((-1672)/3)*z176
  have z202 : w 202=0 := by
    have h:=pivot2_222 w hw
    linear_combination h - ((-81))*z252 - ((-1672)/3)*z176
  have z255 : w 255=0 := by
    have h:=pivot2_221 w hw
    linear_combination h - (484/81)*z242 - ((-1430)/81)*z176
  have z216 : w 216=0 := by
    have h:=pivot2_220 w hw
    linear_combination h - (374/81)*z176 - (1)*z246
  have z253 : w 253=0 := by
    have h:=pivot2_219 w hw
    linear_combination h - (324/121)*z246 - (68/11)*z176
  have z207 : w 207=0 := by
    have h:=pivot2_218 w hw
    linear_combination h - ((-484)/81)*z242 - ((-1430)/81)*z176
  have z185 : w 185=0 := by
    have h:=pivot2_217 w hw
    linear_combination h - (3)*z176
  have z179 : w 179=0 := by
    have h:=pivot2_216 w hw
    linear_combination h - ((-5)/3)*z176
  have z173 : w 173=0 := by
    have h:=pivot2_215 w hw
    linear_combination h - (1)*z176
  have z182 : w 182=0 := by
    have h:=pivot2_214 w hw
    linear_combination h - (1/3)*z176
  have z146 : w 146=0 := by
    have h:=pivot2_213 w hw
    linear_combination h - ((-25)/3)*z176
  have z172 : w 172=0 := by
    have h:=pivot2_212 w hw
    linear_combination h - ((-4))*z176
  have z157 : w 157=0 := by
    have h:=pivot2_211 w hw
    linear_combination h - ((-3))*z176
  have z181 : w 181=0 := by
    have h:=pivot2_210 w hw
    linear_combination h - ((-2)/3)*z176
  have z151 : w 151=0 := by
    have h:=pivot2_209 w hw
    linear_combination h - (2/3)*z176
  have z184 : w 184=0 := by
    have h:=pivot2_208 w hw
    linear_combination h - (28/3)*z176
  have z145 : w 145=0 := by
    have h:=pivot2_207 w hw
    linear_combination h - (1)*z176
  have z158 : w 158=0 := by
    have h:=pivot2_206 w hw
    linear_combination h - (2)*z176
  have z175 : w 175=0 := by
    have h:=pivot2_205 w hw
    linear_combination h - ((-20))*z176
  have z155 : w 155=0 := by
    have h:=pivot2_204 w hw
    linear_combination h - (20)*z176
  have z57 : w 57=0 := by
    have h:=pivot2_203 w hw
    linear_combination h - ((-1)/242)*z176
  have z177 : w 177=0 := by
    have h:=pivot2_202 w hw
    linear_combination h - ((-48521)/36)*z57 - (473/72)*z176
  have z188 : w 188=0 := by
    have h:=pivot2_201 w hw
    linear_combination h - ((-55)/8)*z176 - ((-3025)/4)*z57
  have z144 : w 144=0 := by
    have h:=pivot2_200 w hw
    linear_combination h - (4961/4)*z57 - ((-33)/8)*z176
  have z142 : w 142=0 := by
    have h:=pivot2_199 w hw
    linear_combination h - (3025/4)*z57 - (55/8)*z176
  have z152 : w 152=0 := by
    have h:=pivot2_198 w hw
    linear_combination h - (1573/9)*z57 - (77/18)*z176
  have z178 : w 178=0 := by
    have h:=pivot2_197 w hw
    linear_combination h - ((-1573)/9)*z57 - ((-77)/18)*z176
  have z180 : w 180=0 := by
    have h:=pivot2_196 w hw
    linear_combination h - ((-11)/18)*z176 - ((-121)/9)*z57
  have z137 : w 137=0 := by
    have h:=pivot2_195 w hw
    linear_combination h - ((-18))*z180 - ((-726))*z57
  have z163 : w 163=0 := by
    have h:=pivot2_194 w hw
    linear_combination h - (968/3)*z57 - (18)*z144
  have z161 : w 161=0 := by
    have h:=pivot2_193 w hw
    linear_combination h - (2178)*z57 - ((-22))*z176
  have z160 : w 160=0 := by
    have h:=pivot2_192 w hw
    linear_combination h - (484)*z57 - (9/2)*z180
  have z140 : w 140=0 := by
    have h:=pivot2_191 w hw
    linear_combination h - (1573/3)*z57 - (9/2)*z177
  have z139 : w 139=0 := by
    have h:=pivot2_190 w hw
    linear_combination h - ((-18))*z144 - (1936/3)*z57
  have z191 : w 191=0 := by
    have h:=pivot2_189 w hw
    linear_combination h - ((-1936)/3)*z57 - (18)*z144
  have z190 : w 190=0 := by
    have h:=pivot2_188 w hw
    linear_combination h - ((-9)/2)*z177 - ((-1573)/3)*z57
  have z174 : w 174=0 := by
    have h:=pivot2_187 w hw
    linear_combination h - ((-484)/9)*z57 - (11/9)*z176
  have z170 : w 170=0 := by
    have h:=pivot2_186 w hw
    linear_combination h - ((-484))*z57 - ((-9)/2)*z180
  have z169 : w 169=0 := by
    have h:=pivot2_185 w hw
    linear_combination h - ((-18))*z174 - ((-1210))*z57
  have z193 : w 193=0 := by
    have h:=pivot2_184 w hw
    linear_combination h - (726)*z57 - (18)*z180
  have z153 : w 153=0 := by
    have h:=pivot2_183 w hw
    linear_combination h - (1)*z177
  have z159 : w 159=0 := by
    have h:=pivot2_182 w hw
    linear_combination h - ((-2))*z144
  have z194 : w 194=0 := by
    have h:=pivot2_181 w hw
    linear_combination h - ((-9))*z144 - ((-484)/3)*z57
  have z136 : w 136=0 := by
    have h:=pivot2_180 w hw
    linear_combination h - (484/3)*z57 - (9)*z144
  have z189 : w 189=0 := by
    have h:=pivot2_179 w hw
    linear_combination h - ((-242)/9)*z57 - (22/9)*z176
  have z156 : w 156=0 := by
    have h:=pivot2_178 w hw
    linear_combination h - (1)*z174
  have z183 : w 183=0 := by
    have h:=pivot2_177 w hw
    linear_combination h - ((-1))*z180
  have z187 : w 187=0 := by
    have h:=pivot2_176 w hw
    linear_combination h - (18/11)*z180 - ((-22))*z57
  have z141 : w 141=0 := by
    have h:=pivot2_175 w hw
    linear_combination h - ((-22)/9)*z176 - (242/9)*z57
  have z186 : w 186=0 := by
    have h:=pivot2_174 w hw
    linear_combination h - (1)*z144
  have z167 : w 167=0 := by
    have h:=pivot2_173 w hw
    linear_combination h - ((-2))*z194
  have z119 : w 119=0 := by
    have h:=pivot2_172 w hw
    linear_combination h - (44/3)*z57
  have z113 : w 113=0 := by
    have h:=pivot2_171 w hw
    linear_combination h - (110/9)*z57
  have z107 : w 107=0 := by
    have h:=pivot2_170 w hw
    linear_combination h - ((-22))*z57
  have z116 : w 116=0 := by
    have h:=pivot2_169 w hw
    linear_combination h - ((-22)/9)*z57
  have z80 : w 80=0 := by
    have h:=pivot2_168 w hw
    linear_combination h - (88/9)*z57
  have z106 : w 106=0 := by
    have h:=pivot2_167 w hw
    linear_combination h - ((-22))*z57
  have z91 : w 91=0 := by
    have h:=pivot2_166 w hw
    linear_combination h - ((-22))*z57
  have z115 : w 115=0 := by
    have h:=pivot2_165 w hw
    linear_combination h - (22/9)*z57
  have z85 : w 85=0 := by
    have h:=pivot2_164 w hw
    linear_combination h - (110/9)*z57
  have z118 : w 118=0 := by
    have h:=pivot2_163 w hw
    linear_combination h - (88/9)*z57
  have z79 : w 79=0 := by
    have h:=pivot2_162 w hw
    linear_combination h - (44/3)*z57
  have z92 : w 92=0 := by
    have h:=pivot2_161 w hw
    linear_combination h - ((-22))*z57
  have z109 : w 109=0 := by
    have h:=pivot2_160 w hw
    linear_combination h - ((-44)/3)*z57
  have z89 : w 89=0 := by
    have h:=pivot2_159 w hw
    linear_combination h - ((-44)/3)*z57
  have z110 : w 110=0 := by
    have h:=pivot2_158 w hw
    linear_combination h
  have z87 : w 87=0 := by
    have h:=pivot2_157 w hw
    linear_combination h - (22/3)*z57 - ((-2))*z110
  have z120 : w 120=0 := by
    have h:=pivot2_156 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z111 : w 111=0 := by
    have h:=pivot2_155 w hw
    linear_combination h - (1)*z87 - (44/3)*z57
  have z86 : w 86=0 := by
    have h:=pivot2_154 w hw
    linear_combination h - (22/3)*z57 - ((-1))*z110
  have z112 : w 112=0 := by
    have h:=pivot2_153 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z97 : w 97=0 := by
    have h:=pivot2_152 w hw
    linear_combination h - ((-1))*z120 - ((-44)/9)*z57
  have z95 : w 95=0 := by
    have h:=pivot2_151 w hw
    linear_combination h - ((-22))*z57 - ((-1))*z110
  have z90 : w 90=0 := by
    have h:=pivot2_150 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z110
  have z74 : w 74=0 := by
    have h:=pivot2_149 w hw
    linear_combination h - ((-1))*z87 - (154/9)*z57
  have z73 : w 73=0 := by
    have h:=pivot2_148 w hw
    linear_combination h - (176/9)*z57 - (1)*z120
  have z125 : w 125=0 := by
    have h:=pivot2_147 w hw
    linear_combination h - ((-1))*z120 - (44/9)*z57
  have z124 : w 124=0 := by
    have h:=pivot2_146 w hw
    linear_combination h - ((-1))*z111 - (154/9)*z57
  have z122 : w 122=0 := by
    have h:=pivot2_145 w hw
    linear_combination h - (22/3)*z57
  have z76 : w 76=0 := by
    have h:=pivot2_144 w hw
    linear_combination h - (22/3)*z57
  have z71 : w 71=0 := by
    have h:=pivot2_143 w hw
    linear_combination h - (44/3)*z57
  have z94 : w 94=0 := by
    have h:=pivot2_142 w hw
    linear_combination h - ((-22))*z57
  have z114 : w 114=0 := by
    have h:=pivot2_141 w hw
    linear_combination h - (22/3)*z57
  have z108 : w 108=0 := by
    have h:=pivot2_140 w hw
    linear_combination h - ((-44)/3)*z57 - (1)*z110
  have z78 : w 78=0 := by
    have h:=pivot2_139 w hw
    linear_combination h - (1)*z120 - (44/3)*z57
  have z104 : w 104=0 := by
    have h:=pivot2_138 w hw
    linear_combination h - ((-88)/3)*z57 - ((-1))*z114
  have z103 : w 103=0 := by
    have h:=pivot2_137 w hw
    linear_combination h - ((-1))*z108 - ((-22)/3)*z57
  have z93 : w 93=0 := by
    have h:=pivot2_136 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z78
  have z127 : w 127=0 := by
    have h:=pivot2_135 w hw
    linear_combination h - (22)*z57 - (1)*z114
  have z101 : w 101=0 := by
    have h:=pivot2_134 w hw
    linear_combination h - ((-44)/9)*z57 - ((-1))*z78
  have z128 : w 128=0 := by
    have h:=pivot2_133 w hw
    linear_combination h - ((-1))*z78 - ((-88)/9)*z57
  have z70 : w 70=0 := by
    have h:=pivot2_132 w hw
    linear_combination h - ((-1))*z120 - ((-88)/9)*z57
  have z123 : w 123=0 := by
    have h:=pivot2_131 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z117 : w 117=0 := by
    have h:=pivot2_130 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z114
  have z121 : w 121=0 := by
    have h:=pivot2_129 w hw
    linear_combination h - (1)*z114 - (22/3)*z57
  have z75 : w 75=0 := by
    have h:=pivot2_128 w hw
    linear_combination h - ((-1))*z110 - (22/3)*z57
  have z237 : w 237=0 := by
    have h:=pivot2_127 w hw
    linear_combination h - (4)*z210
  have z249 : w 249=0 := by
    have h:=pivot2_126 w hw
    linear_combination h - (1)*z216
  have z215 : w 215=0 := by
    have h:=pivot2_125 w hw
    linear_combination h - (1)*z248
  have z214 : w 214=0 := by
    have h:=pivot2_124 w hw
    linear_combination h - (1)*z247
  have z213 : w 213=0 := by
    have h:=pivot2_123 w hw
    linear_combination h - (1)*z246
  have z209 : w 209=0 := by
    have h:=pivot2_122 w hw
    linear_combination h - (1)*z253
  have z220 : w 220=0 := by
    have h:=pivot2_121 w hw
    linear_combination h - (1)*z242
  have z171 : w 171=0 := by
    have h:=pivot2_120 w hw
    linear_combination h - (2)*z144
  have z150 : w 150=0 := by
    have h:=pivot2_119 w hw
    linear_combination h - (1)*z183
  have z149 : w 149=0 := by
    have h:=pivot2_118 w hw
    linear_combination h - (1)*z182
  have z148 : w 148=0 := by
    have h:=pivot2_117 w hw
    linear_combination h - (1)*z181
  have z147 : w 147=0 := by
    have h:=pivot2_116 w hw
    linear_combination h - (1)*z180
  have z143 : w 143=0 := by
    have h:=pivot2_115 w hw
    linear_combination h - (1)*z187
  have z154 : w 154=0 := by
    have h:=pivot2_114 w hw
    linear_combination h - (1)*z176
  have z105 : w 105=0 := by
    have h:=pivot2_113 w hw
    linear_combination h - (1)*z78
  have z84 : w 84=0 := by
    have h:=pivot2_112 w hw
    linear_combination h - (1)*z117
  have z83 : w 83=0 := by
    have h:=pivot2_111 w hw
    linear_combination h - (1)*z116
  have z82 : w 82=0 := by
    have h:=pivot2_110 w hw
    linear_combination h - (1)*z115
  have z81 : w 81=0 := by
    have h:=pivot2_109 w hw
    linear_combination h - (1)*z114
  have z77 : w 77=0 := by
    have h:=pivot2_108 w hw
    linear_combination h - (1)*z121
  have z88 : w 88=0 := by
    have h:=pivot2_107 w hw
    linear_combination h - (1)*z110
  have z53 : w 53=0 := by
    have h:=pivot2_106 w hw
    linear_combination h - ((-37)/9)*z57
  have z47 : w 47=0 := by
    have h:=pivot2_105 w hw
    linear_combination h - (202/27)*z57
  have z41 : w 41=0 := by
    have h:=pivot2_104 w hw
    linear_combination h - ((-13)/9)*z57
  have z50 : w 50=0 := by
    have h:=pivot2_103 w hw
    linear_combination h - (82/27)*z57
  have z14 : w 14=0 := by
    have h:=pivot2_102 w hw
    linear_combination h - ((-208)/27)*z57
  have z40 : w 40=0 := by
    have h:=pivot2_101 w hw
    linear_combination h - (34/9)*z57
  have z25 : w 25=0 := by
    have h:=pivot2_100 w hw
    linear_combination h - ((-1))*z57
  have z49 : w 49=0 := by
    have h:=pivot2_99 w hw
    linear_combination h - ((-50)/27)*z57
  have z19 : w 19=0 := by
    have h:=pivot2_98 w hw
    linear_combination h - (62/27)*z57
  have z52 : w 52=0 := by
    have h:=pivot2_97 w hw
    linear_combination h - ((-56)/27)*z57
  have z13 : w 13=0 := by
    have h:=pivot2_96 w hw
    linear_combination h - (5/3)*z57
  have z26 : w 26=0 := by
    have h:=pivot2_95 w hw
    linear_combination h - (10/9)*z57
  have z43 : w 43=0 := by
    have h:=pivot2_94 w hw
    linear_combination h - ((-20)/9)*z57
  have z23 : w 23=0 := by
    have h:=pivot2_93 w hw
    linear_combination h - (20/9)*z57
  have z21 : w 21=0 := by
    have h:=pivot2_92 w hw
    linear_combination h - (7/3)*z57
  have z56 : w 56=0 := by
    have h:=pivot2_91 w hw
    linear_combination h - ((-10)/9)*z57
  have z12 : w 12=0 := by
    have h:=pivot2_90 w hw
    linear_combination h - (4/3)*z57
  have z10 : w 10=0 := by
    have h:=pivot2_89 w hw
    linear_combination h - (10/9)*z57
  have z45 : w 45=0 := by
    have h:=pivot2_88 w hw
    linear_combination h - (1)*z21
  have z51 : w 51=0 := by
    have h:=pivot2_87 w hw
    linear_combination h - ((-2))*z57
  have z17 : w 17=0 := by
    have h:=pivot2_86 w hw
    linear_combination h - (1)*z50
  have z16 : w 16=0 := by
    have h:=pivot2_85 w hw
    linear_combination h - (1)*z49
  have z15 : w 15=0 := by
    have h:=pivot2_84 w hw
    linear_combination h - (2)*z57
  have z20 : w 20=0 := by
    have h:=pivot2_83 w hw
    linear_combination h - (20/9)*z57
  have z46 : w 46=0 := by
    have h:=pivot2_82 w hw
    linear_combination h - ((-20)/9)*z57
  have z48 : w 48=0 := by
    have h:=pivot2_81 w hw
    linear_combination h - ((-2))*z57
  have z54 : w 54=0 := by
    have h:=pivot2_80 w hw
    linear_combination h - (1)*z12
  have z18 : w 18=0 := by
    have h:=pivot2_79 w hw
    linear_combination h - (1)*z48
  have z44 : w 44=0 := by
    have h:=pivot2_78 w hw
    linear_combination h - (22/9)*z57
  have z5 : w 5=0 := by
    have h:=pivot2_77 w hw
    linear_combination h - ((-1)/18)*z48
  have z31 : w 31=0 := by
    have h:=pivot2_76 w hw
    linear_combination h - ((-1)/18)*z54
  have z29 : w 29=0 := by
    have h:=pivot2_75 w hw
    linear_combination h - ((-1)/22)*z44
  have z28 : w 28=0 := by
    have h:=pivot2_74 w hw
    linear_combination h - ((-2)/9)*z15
  have z24 : w 24=0 := by
    have h:=pivot2_73 w hw
    linear_combination h - ((-9)/11)*z44
  have z8 : w 8=0 := by
    have h:=pivot2_72 w hw
    linear_combination h - ((-2)/9)*z21
  have z7 : w 7=0 := by
    have h:=pivot2_71 w hw
    linear_combination h - ((-1)/18)*z12
  have z59 : w 59=0 := by
    have h:=pivot2_70 w hw
    linear_combination h - ((-1)/18)*z54
  have z58 : w 58=0 := by
    have h:=pivot2_69 w hw
    linear_combination h - ((-2)/9)*z45
  have z42 : w 42=0 := by
    have h:=pivot2_68 w hw
    linear_combination h - ((-2))*z57
  have z39 : w 39=0 := by
    have h:=pivot2_67 w hw
    linear_combination h - ((-1)/2)*z54
  have z38 : w 38=0 := by
    have h:=pivot2_66 w hw
    linear_combination h - ((-2)/9)*z51
  have z37 : w 37=0 := by
    have h:=pivot2_65 w hw
    linear_combination h - ((-1)/18)*z42
  have z27 : w 27=0 := by
    have h:=pivot2_64 w hw
    linear_combination h - ((-1)/2)*z12
  have z61 : w 61=0 := by
    have h:=pivot2_63 w hw
    linear_combination h - ((-1)/18)*z18
  have z35 : w 35=0 := by
    have h:=pivot2_62 w hw
    linear_combination h - ((-1)/18)*z12
  have z62 : w 62=0 := by
    have h:=pivot2_61 w hw
    linear_combination h - ((-1)/9)*z12
  have z4 : w 4=0 := by
    have h:=pivot2_60 w hw
    linear_combination h - ((-1)/9)*z54
  have z22 : w 22=0 := by
    have h:=pivot2_59 w hw
    linear_combination h - ((-22)/9)*z57
  have z55 : w 55=0 := by
    have h:=pivot2_58 w hw
    linear_combination h - ((-11)/18)*z18
  have z11 : w 11=0 := by
    have h:=pivot2_57 w hw
    linear_combination h - ((-11)/18)*z48
  have z9 : w 9=0 := by
    have h:=pivot2_56 w hw
    linear_combination h - ((-9)/22)*z44
  have z234 : w 234=0 := by
    have h:=pivot2_55 w hw
    linear_combination h
  have z230 : w 230=0 := by
    have h:=pivot2_54 w hw
    linear_combination h
  have z232 : w 232=0 := by
    have h:=pivot2_53 w hw
    linear_combination h
  have z258 : w 258=0 := by
    have h:=pivot2_52 w hw
    linear_combination h
  have z204 : w 204=0 := by
    have h:=pivot2_51 w hw
    linear_combination h
  have z200 : w 200=0 := by
    have h:=pivot2_50 w hw
    linear_combination h
  have z262 : w 262=0 := by
    have h:=pivot2_49 w hw
    linear_combination h
  have z231 : w 231=0 := by
    have h:=pivot2_48 w hw
    linear_combination h
  have z228 : w 228=0 := by
    have h:=pivot2_47 w hw
    linear_combination h
  have z263 : w 263=0 := by
    have h:=pivot2_46 w hw
    linear_combination h
  have z201 : w 201=0 := by
    have h:=pivot2_45 w hw
    linear_combination h
  have z199 : w 199=0 := by
    have h:=pivot2_44 w hw
    linear_combination h
  have z261 : w 261=0 := by
    have h:=pivot2_43 w hw
    linear_combination h
  have z198 : w 198=0 := by
    have h:=pivot2_42 w hw
    linear_combination h
  have z168 : w 168=0 := by
    have h:=pivot2_41 w hw
    linear_combination h
  have z164 : w 164=0 := by
    have h:=pivot2_40 w hw
    linear_combination h
  have z166 : w 166=0 := by
    have h:=pivot2_39 w hw
    linear_combination h
  have z192 : w 192=0 := by
    have h:=pivot2_38 w hw
    linear_combination h
  have z138 : w 138=0 := by
    have h:=pivot2_37 w hw
    linear_combination h
  have z134 : w 134=0 := by
    have h:=pivot2_36 w hw
    linear_combination h
  have z196 : w 196=0 := by
    have h:=pivot2_35 w hw
    linear_combination h
  have z165 : w 165=0 := by
    have h:=pivot2_34 w hw
    linear_combination h
  have z162 : w 162=0 := by
    have h:=pivot2_33 w hw
    linear_combination h
  have z197 : w 197=0 := by
    have h:=pivot2_32 w hw
    linear_combination h
  have z135 : w 135=0 := by
    have h:=pivot2_31 w hw
    linear_combination h
  have z133 : w 133=0 := by
    have h:=pivot2_30 w hw
    linear_combination h
  have z195 : w 195=0 := by
    have h:=pivot2_29 w hw
    linear_combination h
  have z132 : w 132=0 := by
    have h:=pivot2_28 w hw
    linear_combination h
  have z102 : w 102=0 := by
    have h:=pivot2_27 w hw
    linear_combination h
  have z98 : w 98=0 := by
    have h:=pivot2_26 w hw
    linear_combination h
  have z100 : w 100=0 := by
    have h:=pivot2_25 w hw
    linear_combination h
  have z126 : w 126=0 := by
    have h:=pivot2_24 w hw
    linear_combination h
  have z72 : w 72=0 := by
    have h:=pivot2_23 w hw
    linear_combination h
  have z68 : w 68=0 := by
    have h:=pivot2_22 w hw
    linear_combination h
  have z130 : w 130=0 := by
    have h:=pivot2_21 w hw
    linear_combination h
  have z99 : w 99=0 := by
    have h:=pivot2_20 w hw
    linear_combination h
  have z96 : w 96=0 := by
    have h:=pivot2_19 w hw
    linear_combination h
  have z131 : w 131=0 := by
    have h:=pivot2_18 w hw
    linear_combination h
  have z69 : w 69=0 := by
    have h:=pivot2_17 w hw
    linear_combination h
  have z67 : w 67=0 := by
    have h:=pivot2_16 w hw
    linear_combination h
  have z129 : w 129=0 := by
    have h:=pivot2_15 w hw
    linear_combination h
  have z66 : w 66=0 := by
    have h:=pivot2_14 w hw
    linear_combination h
  have z36 : w 36=0 := by
    have h:=pivot2_13 w hw
    linear_combination h
  have z32 : w 32=0 := by
    have h:=pivot2_12 w hw
    linear_combination h
  have z34 : w 34=0 := by
    have h:=pivot2_11 w hw
    linear_combination h
  have z60 : w 60=0 := by
    have h:=pivot2_10 w hw
    linear_combination h
  have z6 : w 6=0 := by
    have h:=pivot2_9 w hw
    linear_combination h
  have z2 : w 2=0 := by
    have h:=pivot2_8 w hw
    linear_combination h
  have z64 : w 64=0 := by
    have h:=pivot2_7 w hw
    linear_combination h
  have z33 : w 33=0 := by
    have h:=pivot2_6 w hw
    linear_combination h
  have z30 : w 30=0 := by
    have h:=pivot2_5 w hw
    linear_combination h
  have z65 : w 65=0 := by
    have h:=pivot2_4 w hw
    linear_combination h
  have z3 : w 3=0 := by
    have h:=pivot2_3 w hw
    linear_combination h
  have z1 : w 1=0 := by
    have h:=pivot2_2 w hw
    linear_combination h
  have z63 : w 63=0 := by
    have h:=pivot2_1 w hw
    linear_combination h
  have z0 : w 0=0 := by
    have h:=pivot2_0 w hw
    linear_combination h
  funext j
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4
  · exact z5
  · exact z6
  · exact z7
  · exact z8
  · exact z9
  · exact z10
  · exact z11
  · exact z12
  · exact z13
  · exact z14
  · exact z15
  · exact z16
  · exact z17
  · exact z18
  · exact z19
  · exact z20
  · exact z21
  · exact z22
  · exact z23
  · exact z24
  · exact z25
  · exact z26
  · exact z27
  · exact z28
  · exact z29
  · exact z30
  · exact z31
  · exact z32
  · exact z33
  · exact z34
  · exact z35
  · exact z36
  · exact z37
  · exact z38
  · exact z39
  · exact z40
  · exact z41
  · exact z42
  · exact z43
  · exact z44
  · exact z45
  · exact z46
  · exact z47
  · exact z48
  · exact z49
  · exact z50
  · exact z51
  · exact z52
  · exact z53
  · exact z54
  · exact z55
  · exact z56
  · exact z57
  · exact z58
  · exact z59
  · exact z60
  · exact z61
  · exact z62
  · exact z63
  · exact z64
  · exact z65
  · exact z66
  · exact z67
  · exact z68
  · exact z69
  · exact z70
  · exact z71
  · exact z72
  · exact z73
  · exact z74
  · exact z75
  · exact z76
  · exact z77
  · exact z78
  · exact z79
  · exact z80
  · exact z81
  · exact z82
  · exact z83
  · exact z84
  · exact z85
  · exact z86
  · exact z87
  · exact z88
  · exact z89
  · exact z90
  · exact z91
  · exact z92
  · exact z93
  · exact z94
  · exact z95
  · exact z96
  · exact z97
  · exact z98
  · exact z99
  · exact z100
  · exact z101
  · exact z102
  · exact z103
  · exact z104
  · exact z105
  · exact z106
  · exact z107
  · exact z108
  · exact z109
  · exact z110
  · exact z111
  · exact z112
  · exact z113
  · exact z114
  · exact z115
  · exact z116
  · exact z117
  · exact z118
  · exact z119
  · exact z120
  · exact z121
  · exact z122
  · exact z123
  · exact z124
  · exact z125
  · exact z126
  · exact z127
  · exact z128
  · exact z129
  · exact z130
  · exact z131
  · exact z132
  · exact z133
  · exact z134
  · exact z135
  · exact z136
  · exact z137
  · exact z138
  · exact z139
  · exact z140
  · exact z141
  · exact z142
  · exact z143
  · exact z144
  · exact z145
  · exact z146
  · exact z147
  · exact z148
  · exact z149
  · exact z150
  · exact z151
  · exact z152
  · exact z153
  · exact z154
  · exact z155
  · exact z156
  · exact z157
  · exact z158
  · exact z159
  · exact z160
  · exact z161
  · exact z162
  · exact z163
  · exact z164
  · exact z165
  · exact z166
  · exact z167
  · exact z168
  · exact z169
  · exact z170
  · exact z171
  · exact z172
  · exact z173
  · exact z174
  · exact z175
  · exact z176
  · exact z177
  · exact z178
  · exact z179
  · exact z180
  · exact z181
  · exact z182
  · exact z183
  · exact z184
  · exact z185
  · exact z186
  · exact z187
  · exact z188
  · exact z189
  · exact z190
  · exact z191
  · exact z192
  · exact z193
  · exact z194
  · exact z195
  · exact z196
  · exact z197
  · exact z198
  · exact z199
  · exact z200
  · exact z201
  · exact z202
  · exact z203
  · exact z204
  · exact z205
  · exact z206
  · exact z207
  · exact z208
  · exact z209
  · exact z210
  · exact z211
  · exact z212
  · exact z213
  · exact z214
  · exact z215
  · exact z216
  · exact z217
  · exact z218
  · exact z219
  · exact z220
  · exact z221
  · exact z222
  · exact z223
  · exact z224
  · exact z225
  · exact z226
  · exact z227
  · exact z228
  · exact z229
  · exact z230
  · exact z231
  · exact z232
  · exact z233
  · exact z234
  · exact z235
  · exact z236
  · exact z237
  · exact z238
  · exact z239
  · exact z240
  · exact z241
  · exact z242
  · exact z243
  · exact z244
  · exact z245
  · exact z246
  · exact z247
  · exact z248
  · exact z249
  · exact z250
  · exact z251
  · exact z252
  · exact z253
  · exact z254
  · exact z255
  · exact z256
  · exact z257
  · exact z258
  · exact z259
  · exact z260
  · exact z261
  · exact z262
  · exact z263

#print axioms kernel2

theorem kernel3 (w : Fin 264→ℂ) (hw : ∀ i, rows3 w i=0) : w=0 := by
  have z251 : w 251=0 := by
    have h:=pivot3_263 w hw
    linear_combination h
  have z245 : w 245=0 := by
    have h:=pivot3_262 w hw
    linear_combination h
  have z239 : w 239=0 := by
    have h:=pivot3_261 w hw
    linear_combination h
  have z248 : w 248=0 := by
    have h:=pivot3_260 w hw
    linear_combination h
  have z212 : w 212=0 := by
    have h:=pivot3_259 w hw
    linear_combination h
  have z238 : w 238=0 := by
    have h:=pivot3_258 w hw
    linear_combination h
  have z223 : w 223=0 := by
    have h:=pivot3_257 w hw
    linear_combination h
  have z247 : w 247=0 := by
    have h:=pivot3_256 w hw
    linear_combination h
  have z217 : w 217=0 := by
    have h:=pivot3_255 w hw
    linear_combination h
  have z250 : w 250=0 := by
    have h:=pivot3_254 w hw
    linear_combination h
  have z211 : w 211=0 := by
    have h:=pivot3_253 w hw
    linear_combination h
  have z224 : w 224=0 := by
    have h:=pivot3_252 w hw
    linear_combination h
  have z241 : w 241=0 := by
    have h:=pivot3_251 w hw
    linear_combination h
  have z221 : w 221=0 := by
    have h:=pivot3_250 w hw
    linear_combination h
  have z246 : w 246=0 := by
    have h:=pivot3_249 w hw
    linear_combination h
  have z219 : w 219=0 := by
    have h:=pivot3_248 w hw
    linear_combination h - ((-1309)/48)*z246
  have z254 : w 254=0 := by
    have h:=pivot3_247 w hw
    linear_combination h - ((-1377)/16)*z246
  have z252 : w 252=0 := by
    have h:=pivot3_246 w hw
    linear_combination h - (351/16)*z246
  have z208 : w 208=0 := by
    have h:=pivot3_245 w hw
    linear_combination h - (1377/16)*z246
  have z218 : w 218=0 := by
    have h:=pivot3_244 w hw
    linear_combination h - (239/3)*z246
  have z244 : w 244=0 := by
    have h:=pivot3_243 w hw
    linear_combination h - ((-239)/3)*z246
  have z242 : w 242=0 := by
    have h:=pivot3_242 w hw
    linear_combination h - ((-108)/121)*z246
  have z243 : w 243=0 := by
    have h:=pivot3_241 w hw
    linear_combination h - (1)*z219
  have z203 : w 203=0 := by
    have h:=pivot3_240 w hw
    linear_combination h - ((-324))*z246
  have z229 : w 229=0 := by
    have h:=pivot3_239 w hw
    linear_combination h - ((-324))*z252
  have z227 : w 227=0 := by
    have h:=pivot3_238 w hw
    linear_combination h - ((-484))*z242
  have z226 : w 226=0 := by
    have h:=pivot3_237 w hw
    linear_combination h - (81/4)*z246
  have z176 : w 176=0 := by
    have h:=pivot3_236 w hw
    linear_combination h
  have z222 : w 222=0 := by
    have h:=pivot3_235 w hw
    linear_combination h - (682/81)*z176 - ((-121)/81)*z242
  have z206 : w 206=0 := by
    have h:=pivot3_234 w hw
    linear_combination h - ((-81)/4)*z219 - ((-715)/6)*z176
  have z205 : w 205=0 := by
    have h:=pivot3_233 w hw
    linear_combination h - (13904/3)*z176 - (324)*z252
  have z257 : w 257=0 := by
    have h:=pivot3_232 w hw
    linear_combination h - ((-324))*z252 - (3806/3)*z176
  have z256 : w 256=0 := by
    have h:=pivot3_231 w hw
    linear_combination h - ((-81)/4)*z243 - ((-715)/6)*z176
  have z240 : w 240=0 := by
    have h:=pivot3_230 w hw
    linear_combination h - (682/81)*z176 - (121/81)*z242
  have z210 : w 210=0 := by
    have h:=pivot3_229 w hw
    linear_combination h - (1)*z252 - (187/18)*z176
  have z236 : w 236=0 := by
    have h:=pivot3_228 w hw
    linear_combination h - ((-220))*z176 - ((-81)/4)*z246
  have z235 : w 235=0 := by
    have h:=pivot3_227 w hw
    linear_combination h - ((-324))*z240 - (1034)*z176
  have z225 : w 225=0 := by
    have h:=pivot3_226 w hw
    linear_combination h - ((-374)/9)*z176 - ((-4))*z210
  have z259 : w 259=0 := by
    have h:=pivot3_225 w hw
    linear_combination h - (2376)*z176 - (324)*z246
  have z233 : w 233=0 := by
    have h:=pivot3_224 w hw
    linear_combination h - ((-3410)/3)*z176 - ((-324))*z210
  have z260 : w 260=0 := by
    have h:=pivot3_223 w hw
    linear_combination h - ((-81))*z210 - ((-1672)/3)*z176
  have z202 : w 202=0 := by
    have h:=pivot3_222 w hw
    linear_combination h - ((-81))*z252 - ((-1672)/3)*z176
  have z255 : w 255=0 := by
    have h:=pivot3_221 w hw
    linear_combination h - (484/81)*z242 - ((-1430)/81)*z176
  have z216 : w 216=0 := by
    have h:=pivot3_220 w hw
    linear_combination h - (374/81)*z176 - (1)*z246
  have z253 : w 253=0 := by
    have h:=pivot3_219 w hw
    linear_combination h - (324/121)*z246 - (68/11)*z176
  have z207 : w 207=0 := by
    have h:=pivot3_218 w hw
    linear_combination h - ((-484)/81)*z242 - ((-1430)/81)*z176
  have z185 : w 185=0 := by
    have h:=pivot3_217 w hw
    linear_combination h - (47)*z176
  have z179 : w 179=0 := by
    have h:=pivot3_216 w hw
    linear_combination h - ((-38)/3)*z176
  have z173 : w 173=0 := by
    have h:=pivot3_215 w hw
    linear_combination h - (1)*z176
  have z182 : w 182=0 := by
    have h:=pivot3_214 w hw
    linear_combination h - (34/3)*z176
  have z146 : w 146=0 := by
    have h:=pivot3_213 w hw
    linear_combination h - (8/3)*z176
  have z172 : w 172=0 := by
    have h:=pivot3_212 w hw
    linear_combination h - ((-26))*z176
  have z157 : w 157=0 := by
    have h:=pivot3_211 w hw
    linear_combination h - ((-25))*z176
  have z181 : w 181=0 := by
    have h:=pivot3_210 w hw
    linear_combination h - ((-2)/3)*z176
  have z151 : w 151=0 := by
    have h:=pivot3_209 w hw
    linear_combination h - (2/3)*z176
  have z184 : w 184=0 := by
    have h:=pivot3_208 w hw
    linear_combination h - (28/3)*z176
  have z145 : w 145=0 := by
    have h:=pivot3_207 w hw
    linear_combination h - (1)*z176
  have z158 : w 158=0 := by
    have h:=pivot3_206 w hw
    linear_combination h - (2)*z176
  have z175 : w 175=0 := by
    have h:=pivot3_205 w hw
    linear_combination h - ((-20))*z176
  have z155 : w 155=0 := by
    have h:=pivot3_204 w hw
    linear_combination h - (20)*z176
  have z57 : w 57=0 := by
    have h:=pivot3_203 w hw
    linear_combination h - ((-1)/242)*z176
  have z177 : w 177=0 := by
    have h:=pivot3_202 w hw
    linear_combination h - ((-48521)/36)*z57 - (473/72)*z176
  have z188 : w 188=0 := by
    have h:=pivot3_201 w hw
    linear_combination h - ((-55)/8)*z176 - ((-3025)/4)*z57
  have z144 : w 144=0 := by
    have h:=pivot3_200 w hw
    linear_combination h - (4961/4)*z57 - ((-33)/8)*z176
  have z142 : w 142=0 := by
    have h:=pivot3_199 w hw
    linear_combination h - (3025/4)*z57 - (55/8)*z176
  have z152 : w 152=0 := by
    have h:=pivot3_198 w hw
    linear_combination h - (1573/9)*z57 - (77/18)*z176
  have z178 : w 178=0 := by
    have h:=pivot3_197 w hw
    linear_combination h - ((-1573)/9)*z57 - ((-77)/18)*z176
  have z180 : w 180=0 := by
    have h:=pivot3_196 w hw
    linear_combination h - ((-11)/18)*z176 - ((-121)/9)*z57
  have z137 : w 137=0 := by
    have h:=pivot3_195 w hw
    linear_combination h - ((-18))*z180 - ((-726))*z57
  have z163 : w 163=0 := by
    have h:=pivot3_194 w hw
    linear_combination h - (968/3)*z57 - (18)*z144
  have z161 : w 161=0 := by
    have h:=pivot3_193 w hw
    linear_combination h - (2178)*z57 - ((-22))*z176
  have z160 : w 160=0 := by
    have h:=pivot3_192 w hw
    linear_combination h - (484)*z57 - (9/2)*z180
  have z140 : w 140=0 := by
    have h:=pivot3_191 w hw
    linear_combination h - (1573/3)*z57 - (9/2)*z177
  have z139 : w 139=0 := by
    have h:=pivot3_190 w hw
    linear_combination h - ((-18))*z144 - (1936/3)*z57
  have z191 : w 191=0 := by
    have h:=pivot3_189 w hw
    linear_combination h - ((-1936)/3)*z57 - (18)*z144
  have z190 : w 190=0 := by
    have h:=pivot3_188 w hw
    linear_combination h - ((-9)/2)*z177 - ((-1573)/3)*z57
  have z174 : w 174=0 := by
    have h:=pivot3_187 w hw
    linear_combination h - ((-484)/9)*z57 - (11/9)*z176
  have z170 : w 170=0 := by
    have h:=pivot3_186 w hw
    linear_combination h - ((-484))*z57 - ((-9)/2)*z180
  have z169 : w 169=0 := by
    have h:=pivot3_185 w hw
    linear_combination h - ((-18))*z174 - ((-1210))*z57
  have z193 : w 193=0 := by
    have h:=pivot3_184 w hw
    linear_combination h - (726)*z57 - (18)*z180
  have z153 : w 153=0 := by
    have h:=pivot3_183 w hw
    linear_combination h - (1)*z177
  have z159 : w 159=0 := by
    have h:=pivot3_182 w hw
    linear_combination h - ((-2))*z144
  have z194 : w 194=0 := by
    have h:=pivot3_181 w hw
    linear_combination h - ((-9))*z144 - ((-484)/3)*z57
  have z136 : w 136=0 := by
    have h:=pivot3_180 w hw
    linear_combination h - (484/3)*z57 - (9)*z144
  have z189 : w 189=0 := by
    have h:=pivot3_179 w hw
    linear_combination h - ((-242)/9)*z57 - (22/9)*z176
  have z156 : w 156=0 := by
    have h:=pivot3_178 w hw
    linear_combination h - (1)*z174
  have z183 : w 183=0 := by
    have h:=pivot3_177 w hw
    linear_combination h - ((-1))*z180
  have z187 : w 187=0 := by
    have h:=pivot3_176 w hw
    linear_combination h - (18/11)*z180 - ((-22))*z57
  have z141 : w 141=0 := by
    have h:=pivot3_175 w hw
    linear_combination h - ((-22)/9)*z176 - (242/9)*z57
  have z186 : w 186=0 := by
    have h:=pivot3_174 w hw
    linear_combination h - (1)*z144
  have z167 : w 167=0 := by
    have h:=pivot3_173 w hw
    linear_combination h - ((-2))*z194
  have z119 : w 119=0 := by
    have h:=pivot3_172 w hw
    linear_combination h - (44/3)*z57
  have z113 : w 113=0 := by
    have h:=pivot3_171 w hw
    linear_combination h - (110/9)*z57
  have z107 : w 107=0 := by
    have h:=pivot3_170 w hw
    linear_combination h - ((-22))*z57
  have z116 : w 116=0 := by
    have h:=pivot3_169 w hw
    linear_combination h - ((-22)/9)*z57
  have z80 : w 80=0 := by
    have h:=pivot3_168 w hw
    linear_combination h - (88/9)*z57
  have z106 : w 106=0 := by
    have h:=pivot3_167 w hw
    linear_combination h - ((-22))*z57
  have z91 : w 91=0 := by
    have h:=pivot3_166 w hw
    linear_combination h - ((-22))*z57
  have z115 : w 115=0 := by
    have h:=pivot3_165 w hw
    linear_combination h - (22/9)*z57
  have z85 : w 85=0 := by
    have h:=pivot3_164 w hw
    linear_combination h - (110/9)*z57
  have z118 : w 118=0 := by
    have h:=pivot3_163 w hw
    linear_combination h - (88/9)*z57
  have z79 : w 79=0 := by
    have h:=pivot3_162 w hw
    linear_combination h - (44/3)*z57
  have z92 : w 92=0 := by
    have h:=pivot3_161 w hw
    linear_combination h - ((-22))*z57
  have z109 : w 109=0 := by
    have h:=pivot3_160 w hw
    linear_combination h - ((-44)/3)*z57
  have z89 : w 89=0 := by
    have h:=pivot3_159 w hw
    linear_combination h - ((-44)/3)*z57
  have z110 : w 110=0 := by
    have h:=pivot3_158 w hw
    linear_combination h
  have z87 : w 87=0 := by
    have h:=pivot3_157 w hw
    linear_combination h - (22/3)*z57 - ((-2))*z110
  have z120 : w 120=0 := by
    have h:=pivot3_156 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z111 : w 111=0 := by
    have h:=pivot3_155 w hw
    linear_combination h - (1)*z87 - (44/3)*z57
  have z86 : w 86=0 := by
    have h:=pivot3_154 w hw
    linear_combination h - (22/3)*z57 - ((-1))*z110
  have z112 : w 112=0 := by
    have h:=pivot3_153 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z97 : w 97=0 := by
    have h:=pivot3_152 w hw
    linear_combination h - ((-1))*z120 - ((-44)/9)*z57
  have z95 : w 95=0 := by
    have h:=pivot3_151 w hw
    linear_combination h - ((-22))*z57 - ((-1))*z110
  have z90 : w 90=0 := by
    have h:=pivot3_150 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z110
  have z74 : w 74=0 := by
    have h:=pivot3_149 w hw
    linear_combination h - ((-1))*z87 - (154/9)*z57
  have z73 : w 73=0 := by
    have h:=pivot3_148 w hw
    linear_combination h - (176/9)*z57 - (1)*z120
  have z125 : w 125=0 := by
    have h:=pivot3_147 w hw
    linear_combination h - ((-1))*z120 - (44/9)*z57
  have z124 : w 124=0 := by
    have h:=pivot3_146 w hw
    linear_combination h - ((-1))*z111 - (154/9)*z57
  have z122 : w 122=0 := by
    have h:=pivot3_145 w hw
    linear_combination h - (22/3)*z57
  have z76 : w 76=0 := by
    have h:=pivot3_144 w hw
    linear_combination h - (22/3)*z57
  have z71 : w 71=0 := by
    have h:=pivot3_143 w hw
    linear_combination h - (44/3)*z57
  have z94 : w 94=0 := by
    have h:=pivot3_142 w hw
    linear_combination h - ((-22))*z57
  have z114 : w 114=0 := by
    have h:=pivot3_141 w hw
    linear_combination h - (22/3)*z57
  have z108 : w 108=0 := by
    have h:=pivot3_140 w hw
    linear_combination h - ((-44)/3)*z57 - (1)*z110
  have z78 : w 78=0 := by
    have h:=pivot3_139 w hw
    linear_combination h - (1)*z120 - (44/3)*z57
  have z104 : w 104=0 := by
    have h:=pivot3_138 w hw
    linear_combination h - ((-88)/3)*z57 - ((-1))*z114
  have z103 : w 103=0 := by
    have h:=pivot3_137 w hw
    linear_combination h - ((-1))*z108 - ((-22)/3)*z57
  have z93 : w 93=0 := by
    have h:=pivot3_136 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z78
  have z127 : w 127=0 := by
    have h:=pivot3_135 w hw
    linear_combination h - (22)*z57 - (1)*z114
  have z101 : w 101=0 := by
    have h:=pivot3_134 w hw
    linear_combination h - ((-44)/9)*z57 - ((-1))*z78
  have z128 : w 128=0 := by
    have h:=pivot3_133 w hw
    linear_combination h - ((-1))*z78 - ((-88)/9)*z57
  have z70 : w 70=0 := by
    have h:=pivot3_132 w hw
    linear_combination h - ((-1))*z120 - ((-88)/9)*z57
  have z123 : w 123=0 := by
    have h:=pivot3_131 w hw
    linear_combination h - (22/3)*z57 - (1)*z110
  have z117 : w 117=0 := by
    have h:=pivot3_130 w hw
    linear_combination h - ((-44)/3)*z57 - ((-1))*z114
  have z121 : w 121=0 := by
    have h:=pivot3_129 w hw
    linear_combination h - (1)*z114 - (22/3)*z57
  have z75 : w 75=0 := by
    have h:=pivot3_128 w hw
    linear_combination h - ((-1))*z110 - (22/3)*z57
  have z237 : w 237=0 := by
    have h:=pivot3_127 w hw
    linear_combination h - (4)*z210
  have z249 : w 249=0 := by
    have h:=pivot3_126 w hw
    linear_combination h - (1)*z216
  have z215 : w 215=0 := by
    have h:=pivot3_125 w hw
    linear_combination h - (1)*z248
  have z214 : w 214=0 := by
    have h:=pivot3_124 w hw
    linear_combination h - (1)*z247
  have z213 : w 213=0 := by
    have h:=pivot3_123 w hw
    linear_combination h - (1)*z246
  have z209 : w 209=0 := by
    have h:=pivot3_122 w hw
    linear_combination h - (1)*z253
  have z220 : w 220=0 := by
    have h:=pivot3_121 w hw
    linear_combination h - (1)*z242
  have z171 : w 171=0 := by
    have h:=pivot3_120 w hw
    linear_combination h - (2)*z144
  have z150 : w 150=0 := by
    have h:=pivot3_119 w hw
    linear_combination h - (1)*z183
  have z149 : w 149=0 := by
    have h:=pivot3_118 w hw
    linear_combination h - (1)*z182
  have z148 : w 148=0 := by
    have h:=pivot3_117 w hw
    linear_combination h - (1)*z181
  have z147 : w 147=0 := by
    have h:=pivot3_116 w hw
    linear_combination h - (1)*z180
  have z143 : w 143=0 := by
    have h:=pivot3_115 w hw
    linear_combination h - (1)*z187
  have z154 : w 154=0 := by
    have h:=pivot3_114 w hw
    linear_combination h - (1)*z176
  have z105 : w 105=0 := by
    have h:=pivot3_113 w hw
    linear_combination h - (1)*z78
  have z84 : w 84=0 := by
    have h:=pivot3_112 w hw
    linear_combination h - (1)*z117
  have z83 : w 83=0 := by
    have h:=pivot3_111 w hw
    linear_combination h - (1)*z116
  have z82 : w 82=0 := by
    have h:=pivot3_110 w hw
    linear_combination h - (1)*z115
  have z81 : w 81=0 := by
    have h:=pivot3_109 w hw
    linear_combination h - (1)*z114
  have z77 : w 77=0 := by
    have h:=pivot3_108 w hw
    linear_combination h - (1)*z121
  have z88 : w 88=0 := by
    have h:=pivot3_107 w hw
    linear_combination h - (1)*z110
  have z53 : w 53=0 := by
    have h:=pivot3_106 w hw
    linear_combination h - ((-13)/3)*z57
  have z47 : w 47=0 := by
    have h:=pivot3_105 w hw
    linear_combination h - (226/27)*z57
  have z41 : w 41=0 := by
    have h:=pivot3_104 w hw
    linear_combination h - ((-13)/9)*z57
  have z50 : w 50=0 := by
    have h:=pivot3_103 w hw
    linear_combination h - (94/27)*z57
  have z14 : w 14=0 := by
    have h:=pivot3_102 w hw
    linear_combination h - ((-232)/27)*z57
  have z40 : w 40=0 := by
    have h:=pivot3_101 w hw
    linear_combination h - (38/9)*z57
  have z25 : w 25=0 := by
    have h:=pivot3_100 w hw
    linear_combination h - ((-11)/9)*z57
  have z49 : w 49=0 := by
    have h:=pivot3_99 w hw
    linear_combination h - ((-50)/27)*z57
  have z19 : w 19=0 := by
    have h:=pivot3_98 w hw
    linear_combination h - (62/27)*z57
  have z52 : w 52=0 := by
    have h:=pivot3_97 w hw
    linear_combination h - ((-56)/27)*z57
  have z13 : w 13=0 := by
    have h:=pivot3_96 w hw
    linear_combination h - (5/3)*z57
  have z26 : w 26=0 := by
    have h:=pivot3_95 w hw
    linear_combination h - (10/9)*z57
  have z43 : w 43=0 := by
    have h:=pivot3_94 w hw
    linear_combination h - ((-20)/9)*z57
  have z23 : w 23=0 := by
    have h:=pivot3_93 w hw
    linear_combination h - (20/9)*z57
  have z21 : w 21=0 := by
    have h:=pivot3_92 w hw
    linear_combination h - (7/3)*z57
  have z56 : w 56=0 := by
    have h:=pivot3_91 w hw
    linear_combination h - ((-10)/9)*z57
  have z12 : w 12=0 := by
    have h:=pivot3_90 w hw
    linear_combination h - (4/3)*z57
  have z10 : w 10=0 := by
    have h:=pivot3_89 w hw
    linear_combination h - (10/9)*z57
  have z45 : w 45=0 := by
    have h:=pivot3_88 w hw
    linear_combination h - (1)*z21
  have z51 : w 51=0 := by
    have h:=pivot3_87 w hw
    linear_combination h - ((-2))*z57
  have z17 : w 17=0 := by
    have h:=pivot3_86 w hw
    linear_combination h - (1)*z50
  have z16 : w 16=0 := by
    have h:=pivot3_85 w hw
    linear_combination h - (1)*z49
  have z15 : w 15=0 := by
    have h:=pivot3_84 w hw
    linear_combination h - (2)*z57
  have z20 : w 20=0 := by
    have h:=pivot3_83 w hw
    linear_combination h - (20/9)*z57
  have z46 : w 46=0 := by
    have h:=pivot3_82 w hw
    linear_combination h - ((-20)/9)*z57
  have z48 : w 48=0 := by
    have h:=pivot3_81 w hw
    linear_combination h - ((-2))*z57
  have z54 : w 54=0 := by
    have h:=pivot3_80 w hw
    linear_combination h - (1)*z12
  have z18 : w 18=0 := by
    have h:=pivot3_79 w hw
    linear_combination h - (1)*z48
  have z44 : w 44=0 := by
    have h:=pivot3_78 w hw
    linear_combination h - (22/9)*z57
  have z5 : w 5=0 := by
    have h:=pivot3_77 w hw
    linear_combination h - ((-1)/18)*z48
  have z31 : w 31=0 := by
    have h:=pivot3_76 w hw
    linear_combination h - ((-1)/18)*z54
  have z29 : w 29=0 := by
    have h:=pivot3_75 w hw
    linear_combination h - ((-1)/22)*z44
  have z28 : w 28=0 := by
    have h:=pivot3_74 w hw
    linear_combination h - ((-2)/9)*z15
  have z24 : w 24=0 := by
    have h:=pivot3_73 w hw
    linear_combination h - ((-9)/11)*z44
  have z8 : w 8=0 := by
    have h:=pivot3_72 w hw
    linear_combination h - ((-2)/9)*z21
  have z7 : w 7=0 := by
    have h:=pivot3_71 w hw
    linear_combination h - ((-1)/18)*z12
  have z59 : w 59=0 := by
    have h:=pivot3_70 w hw
    linear_combination h - ((-1)/18)*z54
  have z58 : w 58=0 := by
    have h:=pivot3_69 w hw
    linear_combination h - ((-2)/9)*z45
  have z42 : w 42=0 := by
    have h:=pivot3_68 w hw
    linear_combination h - ((-2))*z57
  have z39 : w 39=0 := by
    have h:=pivot3_67 w hw
    linear_combination h - ((-1)/2)*z54
  have z38 : w 38=0 := by
    have h:=pivot3_66 w hw
    linear_combination h - ((-2)/9)*z51
  have z37 : w 37=0 := by
    have h:=pivot3_65 w hw
    linear_combination h - ((-1)/18)*z42
  have z27 : w 27=0 := by
    have h:=pivot3_64 w hw
    linear_combination h - ((-1)/2)*z12
  have z61 : w 61=0 := by
    have h:=pivot3_63 w hw
    linear_combination h - ((-1)/18)*z18
  have z35 : w 35=0 := by
    have h:=pivot3_62 w hw
    linear_combination h - ((-1)/18)*z12
  have z62 : w 62=0 := by
    have h:=pivot3_61 w hw
    linear_combination h - ((-1)/9)*z12
  have z4 : w 4=0 := by
    have h:=pivot3_60 w hw
    linear_combination h - ((-1)/9)*z54
  have z22 : w 22=0 := by
    have h:=pivot3_59 w hw
    linear_combination h - ((-22)/9)*z57
  have z55 : w 55=0 := by
    have h:=pivot3_58 w hw
    linear_combination h - ((-11)/18)*z18
  have z11 : w 11=0 := by
    have h:=pivot3_57 w hw
    linear_combination h - ((-11)/18)*z48
  have z9 : w 9=0 := by
    have h:=pivot3_56 w hw
    linear_combination h - ((-9)/22)*z44
  have z234 : w 234=0 := by
    have h:=pivot3_55 w hw
    linear_combination h
  have z230 : w 230=0 := by
    have h:=pivot3_54 w hw
    linear_combination h
  have z232 : w 232=0 := by
    have h:=pivot3_53 w hw
    linear_combination h
  have z258 : w 258=0 := by
    have h:=pivot3_52 w hw
    linear_combination h
  have z204 : w 204=0 := by
    have h:=pivot3_51 w hw
    linear_combination h
  have z200 : w 200=0 := by
    have h:=pivot3_50 w hw
    linear_combination h
  have z262 : w 262=0 := by
    have h:=pivot3_49 w hw
    linear_combination h
  have z231 : w 231=0 := by
    have h:=pivot3_48 w hw
    linear_combination h
  have z228 : w 228=0 := by
    have h:=pivot3_47 w hw
    linear_combination h
  have z263 : w 263=0 := by
    have h:=pivot3_46 w hw
    linear_combination h
  have z201 : w 201=0 := by
    have h:=pivot3_45 w hw
    linear_combination h
  have z199 : w 199=0 := by
    have h:=pivot3_44 w hw
    linear_combination h
  have z261 : w 261=0 := by
    have h:=pivot3_43 w hw
    linear_combination h
  have z198 : w 198=0 := by
    have h:=pivot3_42 w hw
    linear_combination h
  have z168 : w 168=0 := by
    have h:=pivot3_41 w hw
    linear_combination h
  have z164 : w 164=0 := by
    have h:=pivot3_40 w hw
    linear_combination h
  have z166 : w 166=0 := by
    have h:=pivot3_39 w hw
    linear_combination h
  have z192 : w 192=0 := by
    have h:=pivot3_38 w hw
    linear_combination h
  have z138 : w 138=0 := by
    have h:=pivot3_37 w hw
    linear_combination h
  have z134 : w 134=0 := by
    have h:=pivot3_36 w hw
    linear_combination h
  have z196 : w 196=0 := by
    have h:=pivot3_35 w hw
    linear_combination h
  have z165 : w 165=0 := by
    have h:=pivot3_34 w hw
    linear_combination h
  have z162 : w 162=0 := by
    have h:=pivot3_33 w hw
    linear_combination h
  have z197 : w 197=0 := by
    have h:=pivot3_32 w hw
    linear_combination h
  have z135 : w 135=0 := by
    have h:=pivot3_31 w hw
    linear_combination h
  have z133 : w 133=0 := by
    have h:=pivot3_30 w hw
    linear_combination h
  have z195 : w 195=0 := by
    have h:=pivot3_29 w hw
    linear_combination h
  have z132 : w 132=0 := by
    have h:=pivot3_28 w hw
    linear_combination h
  have z102 : w 102=0 := by
    have h:=pivot3_27 w hw
    linear_combination h
  have z98 : w 98=0 := by
    have h:=pivot3_26 w hw
    linear_combination h
  have z100 : w 100=0 := by
    have h:=pivot3_25 w hw
    linear_combination h
  have z126 : w 126=0 := by
    have h:=pivot3_24 w hw
    linear_combination h
  have z72 : w 72=0 := by
    have h:=pivot3_23 w hw
    linear_combination h
  have z68 : w 68=0 := by
    have h:=pivot3_22 w hw
    linear_combination h
  have z130 : w 130=0 := by
    have h:=pivot3_21 w hw
    linear_combination h
  have z99 : w 99=0 := by
    have h:=pivot3_20 w hw
    linear_combination h
  have z96 : w 96=0 := by
    have h:=pivot3_19 w hw
    linear_combination h
  have z131 : w 131=0 := by
    have h:=pivot3_18 w hw
    linear_combination h
  have z69 : w 69=0 := by
    have h:=pivot3_17 w hw
    linear_combination h
  have z67 : w 67=0 := by
    have h:=pivot3_16 w hw
    linear_combination h
  have z129 : w 129=0 := by
    have h:=pivot3_15 w hw
    linear_combination h
  have z66 : w 66=0 := by
    have h:=pivot3_14 w hw
    linear_combination h
  have z36 : w 36=0 := by
    have h:=pivot3_13 w hw
    linear_combination h
  have z32 : w 32=0 := by
    have h:=pivot3_12 w hw
    linear_combination h
  have z34 : w 34=0 := by
    have h:=pivot3_11 w hw
    linear_combination h
  have z60 : w 60=0 := by
    have h:=pivot3_10 w hw
    linear_combination h
  have z6 : w 6=0 := by
    have h:=pivot3_9 w hw
    linear_combination h
  have z2 : w 2=0 := by
    have h:=pivot3_8 w hw
    linear_combination h
  have z64 : w 64=0 := by
    have h:=pivot3_7 w hw
    linear_combination h
  have z33 : w 33=0 := by
    have h:=pivot3_6 w hw
    linear_combination h
  have z30 : w 30=0 := by
    have h:=pivot3_5 w hw
    linear_combination h
  have z65 : w 65=0 := by
    have h:=pivot3_4 w hw
    linear_combination h
  have z3 : w 3=0 := by
    have h:=pivot3_3 w hw
    linear_combination h
  have z1 : w 1=0 := by
    have h:=pivot3_2 w hw
    linear_combination h
  have z63 : w 63=0 := by
    have h:=pivot3_1 w hw
    linear_combination h
  have z0 : w 0=0 := by
    have h:=pivot3_0 w hw
    linear_combination h
  funext j
  fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4
  · exact z5
  · exact z6
  · exact z7
  · exact z8
  · exact z9
  · exact z10
  · exact z11
  · exact z12
  · exact z13
  · exact z14
  · exact z15
  · exact z16
  · exact z17
  · exact z18
  · exact z19
  · exact z20
  · exact z21
  · exact z22
  · exact z23
  · exact z24
  · exact z25
  · exact z26
  · exact z27
  · exact z28
  · exact z29
  · exact z30
  · exact z31
  · exact z32
  · exact z33
  · exact z34
  · exact z35
  · exact z36
  · exact z37
  · exact z38
  · exact z39
  · exact z40
  · exact z41
  · exact z42
  · exact z43
  · exact z44
  · exact z45
  · exact z46
  · exact z47
  · exact z48
  · exact z49
  · exact z50
  · exact z51
  · exact z52
  · exact z53
  · exact z54
  · exact z55
  · exact z56
  · exact z57
  · exact z58
  · exact z59
  · exact z60
  · exact z61
  · exact z62
  · exact z63
  · exact z64
  · exact z65
  · exact z66
  · exact z67
  · exact z68
  · exact z69
  · exact z70
  · exact z71
  · exact z72
  · exact z73
  · exact z74
  · exact z75
  · exact z76
  · exact z77
  · exact z78
  · exact z79
  · exact z80
  · exact z81
  · exact z82
  · exact z83
  · exact z84
  · exact z85
  · exact z86
  · exact z87
  · exact z88
  · exact z89
  · exact z90
  · exact z91
  · exact z92
  · exact z93
  · exact z94
  · exact z95
  · exact z96
  · exact z97
  · exact z98
  · exact z99
  · exact z100
  · exact z101
  · exact z102
  · exact z103
  · exact z104
  · exact z105
  · exact z106
  · exact z107
  · exact z108
  · exact z109
  · exact z110
  · exact z111
  · exact z112
  · exact z113
  · exact z114
  · exact z115
  · exact z116
  · exact z117
  · exact z118
  · exact z119
  · exact z120
  · exact z121
  · exact z122
  · exact z123
  · exact z124
  · exact z125
  · exact z126
  · exact z127
  · exact z128
  · exact z129
  · exact z130
  · exact z131
  · exact z132
  · exact z133
  · exact z134
  · exact z135
  · exact z136
  · exact z137
  · exact z138
  · exact z139
  · exact z140
  · exact z141
  · exact z142
  · exact z143
  · exact z144
  · exact z145
  · exact z146
  · exact z147
  · exact z148
  · exact z149
  · exact z150
  · exact z151
  · exact z152
  · exact z153
  · exact z154
  · exact z155
  · exact z156
  · exact z157
  · exact z158
  · exact z159
  · exact z160
  · exact z161
  · exact z162
  · exact z163
  · exact z164
  · exact z165
  · exact z166
  · exact z167
  · exact z168
  · exact z169
  · exact z170
  · exact z171
  · exact z172
  · exact z173
  · exact z174
  · exact z175
  · exact z176
  · exact z177
  · exact z178
  · exact z179
  · exact z180
  · exact z181
  · exact z182
  · exact z183
  · exact z184
  · exact z185
  · exact z186
  · exact z187
  · exact z188
  · exact z189
  · exact z190
  · exact z191
  · exact z192
  · exact z193
  · exact z194
  · exact z195
  · exact z196
  · exact z197
  · exact z198
  · exact z199
  · exact z200
  · exact z201
  · exact z202
  · exact z203
  · exact z204
  · exact z205
  · exact z206
  · exact z207
  · exact z208
  · exact z209
  · exact z210
  · exact z211
  · exact z212
  · exact z213
  · exact z214
  · exact z215
  · exact z216
  · exact z217
  · exact z218
  · exact z219
  · exact z220
  · exact z221
  · exact z222
  · exact z223
  · exact z224
  · exact z225
  · exact z226
  · exact z227
  · exact z228
  · exact z229
  · exact z230
  · exact z231
  · exact z232
  · exact z233
  · exact z234
  · exact z235
  · exact z236
  · exact z237
  · exact z238
  · exact z239
  · exact z240
  · exact z241
  · exact z242
  · exact z243
  · exact z244
  · exact z245
  · exact z246
  · exact z247
  · exact z248
  · exact z249
  · exact z250
  · exact z251
  · exact z252
  · exact z253
  · exact z254
  · exact z255
  · exact z256
  · exact z257
  · exact z258
  · exact z259
  · exact z260
  · exact z261
  · exact z262
  · exact z263

#print axioms kernel3

end SmallLevelTwentyTwoThirdJetTriangular
