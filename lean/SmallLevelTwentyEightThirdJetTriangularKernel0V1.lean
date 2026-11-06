module

public import SmallLevelTwentyEightThirdJetTriangular0BundleV4

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightThirdJetTriangular
open SmallLevelTwentyEightThirdJet

theorem kernel0 (w : Fin 336→ℂ) (hw : ∀ i, rows0 w i=0) : w=0 := by
  have z277 : w 277=0 := by
    have h:=pivot0_335 w hw
    linear_combination h
  have z325 : w 325=0 := by
    have h:=pivot0_334 w hw
    linear_combination h
  have z311 : w 311=0 := by
    have h:=pivot0_333 w hw
    linear_combination h
  have z317 : w 317=0 := by
    have h:=pivot0_332 w hw
    linear_combination h
  have z313 : w 313=0 := by
    have h:=pivot0_331 w hw
    linear_combination h
  have z280 : w 280=0 := by
    have h:=pivot0_330 w hw
    linear_combination h
  have z314 : w 314=0 := by
    have h:=pivot0_329 w hw
    linear_combination h - ((-1518485)/30699)*z280
  have z273 : w 273=0 := by
    have h:=pivot0_328 w hw
    linear_combination h - ((-12544)/30699)*z280
  have z316 : w 316=0 := by
    have h:=pivot0_327 w hw
    linear_combination h - ((-1))*z314
  have z279 : w 279=0 := by
    have h:=pivot0_326 w hw
    linear_combination h - (49/81)*z273 - ((-784)/6561)*z280
  have z326 : w 326=0 := by
    have h:=pivot0_325 w hw
    linear_combination h - ((-49)/16)*z273 - (49/81)*z280
  have z278 : w 278=0 := by
    have h:=pivot0_324 w hw
    linear_combination h - ((-49))*z280 - ((-49)/16)*z273
  have z310 : w 310=0 := by
    have h:=pivot0_323 w hw
    linear_combination h - (49)*z280 - (49/16)*z273
  have z307 : w 307=0 := by
    have h:=pivot0_322 w hw
    linear_combination h - (1)*z279 - ((-784))*z280
  have z323 : w 323=0 := by
    have h:=pivot0_321 w hw
    linear_combination h - ((-784))*z280 - ((-16)/81)*z326
  have z257 : w 257=0 := by
    have h:=pivot0_320 w hw
    linear_combination h - (3969)*z273
  have z328 : w 328=0 := by
    have h:=pivot0_319 w hw
    linear_combination h - (49)*z280
  have z267 : w 267=0 := by
    have h:=pivot0_318 w hw
    linear_combination h - (16/81)*z326
  have z304 : w 304=0 := by
    have h:=pivot0_317 w hw
    linear_combination h - (81/16)*z279
  have z260 : w 260=0 := by
    have h:=pivot0_316 w hw
    linear_combination h - ((-49))*z280
  have z289 : w 289=0 := by
    have h:=pivot0_315 w hw
    linear_combination h - (3969)*z273
  have z306 : w 306=0 := by
    have h:=pivot0_314 w hw
    linear_combination h - (49/16)*z273
  have z303 : w 303=0 := by
    have h:=pivot0_313 w hw
    linear_combination h - (784/81)*z280
  have z298 : w 298=0 := by
    have h:=pivot0_312 w hw
    linear_combination h - ((-3969)/16)*z273
  have z290 : w 290=0 := by
    have h:=pivot0_311 w hw
    linear_combination h - (3969/16)*z273
  have z285 : w 285=0 := by
    have h:=pivot0_310 w hw
    linear_combination h - ((-784)/81)*z280
  have z282 : w 282=0 := by
    have h:=pivot0_309 w hw
    linear_combination h - ((-49)/16)*z273
  have z224 : w 224=0 := by
    have h:=pivot0_308 w hw
    linear_combination h
  have z312 : w 312=0 := by
    have h:=pivot0_307 w hw
    linear_combination h - (49/81)*z280 - ((-280)/81)*z224
  have z276 : w 276=0 := by
    have h:=pivot0_306 w hw
    linear_combination h - ((-280)/81)*z224 - ((-49)/81)*z280
  have z327 : w 327=0 := by
    have h:=pivot0_305 w hw
    linear_combination h - (784/81)*z280 - (2324/81)*z224
  have z324 : w 324=0 := by
    have h:=pivot0_304 w hw
    linear_combination h - (49/16)*z273 - (70/9)*z224
  have z270 : w 270=0 := by
    have h:=pivot0_303 w hw
    linear_combination h - (1)*z312
  have z322 : w 322=0 := by
    have h:=pivot0_302 w hw
    linear_combination h - (81/49)*z270 - (40/7)*z224
  have z318 : w 318=0 := by
    have h:=pivot0_301 w hw
    linear_combination h - (280/81)*z224 - (49/81)*z280
  have z264 : w 264=0 := by
    have h:=pivot0_300 w hw
    linear_combination h - (70/9)*z224 - ((-49)/16)*z273
  have z266 : w 266=0 := by
    have h:=pivot0_299 w hw
    linear_combination h - ((-1))*z280
  have z261 : w 261=0 := by
    have h:=pivot0_298 w hw
    linear_combination h - (2324/81)*z224 - ((-784)/81)*z280
  have z256 : w 256=0 := by
    have h:=pivot0_297 w hw
    linear_combination h - (3969/16)*z273 - ((-658)/3)*z224
  have z315 : w 315=0 := by
    have h:=pivot0_296 w hw
    linear_combination h - (1)*z273
  have z332 : w 332=0 := by
    have h:=pivot0_295 w hw
    linear_combination h - ((-3969)/16)*z273 - ((-658)/3)*z224
  have z193 : w 193=0 := by
    have h:=pivot0_294 w hw
    linear_combination h - (39)*z224
  have z241 : w 241=0 := by
    have h:=pivot0_293 w hw
    linear_combination h
  have z227 : w 227=0 := by
    have h:=pivot0_292 w hw
    linear_combination h - ((-39))*z224
  have z233 : w 233=0 := by
    have h:=pivot0_291 w hw
    linear_combination h - (55/3)*z224
  have z229 : w 229=0 := by
    have h:=pivot0_290 w hw
    linear_combination h - (55/3)*z224
  have z70 : w 70=0 := by
    have h:=pivot0_289 w hw
    linear_combination h - (1/126)*z224
  have z230 : w 230=0 := by
    have h:=pivot0_288 w hw
    linear_combination h - (361/45)*z224 - (5474/5)*z70
  have z189 : w 189=0 := by
    have h:=pivot0_287 w hw
    linear_combination h - (364/5)*z70 - (56/45)*z224
  have z232 : w 232=0 := by
    have h:=pivot0_286 w hw
    linear_combination h - ((-1))*z230
  have z195 : w 195=0 := by
    have h:=pivot0_285 w hw
    linear_combination h - ((-1330)/9)*z70 - (7/9)*z189 - (28/81)*z224
  have z183 : w 183=0 := by
    have h:=pivot0_284 w hw
    linear_combination h - (7/9)*z189 - ((-1330)/9)*z70 - (28/81)*z224
  have z194 : w 194=0 := by
    have h:=pivot0_283 w hw
    linear_combination h - (147)*z70 - (7)*z224 - ((-7)/4)*z189
  have z226 : w 226=0 := by
    have h:=pivot0_282 w hw
    linear_combination h - ((-147))*z70 - ((-7))*z224 - (7/4)*z189
  have z223 : w 223=0 := by
    have h:=pivot0_281 w hw
    linear_combination h - (1)*z195 - (28)*z224 - (126)*z70
  have z239 : w 239=0 := by
    have h:=pivot0_280 w hw
    linear_combination h - (126)*z70 - (1)*z183 - (28)*z224
  have z173 : w 173=0 := by
    have h:=pivot0_279 w hw
    linear_combination h - ((-1344))*z70 - (63)*z189
  have z244 : w 244=0 := by
    have h:=pivot0_278 w hw
    linear_combination h - ((-504))*z70 - ((-7))*z224
  have z242 : w 242=0 := by
    have h:=pivot0_277 w hw
    linear_combination h - (9/4)*z183 - ((-315)/2)*z70
  have z220 : w 220=0 := by
    have h:=pivot0_276 w hw
    linear_combination h - (9/4)*z195 - ((-315)/2)*z70
  have z176 : w 176=0 := by
    have h:=pivot0_275 w hw
    linear_combination h - (504)*z70 - (7)*z224
  have z247 : w 247=0 := by
    have h:=pivot0_274 w hw
    linear_combination h - (1344)*z70 - ((-63))*z189
  have z222 : w 222=0 := by
    have h:=pivot0_273 w hw
    linear_combination h - ((-21))*z70 - (7/4)*z189
  have z219 : w 219=0 := by
    have h:=pivot0_272 w hw
    linear_combination h - ((-28)/9)*z224 - ((-14))*z70
  have z214 : w 214=0 := by
    have h:=pivot0_271 w hw
    linear_combination h - ((-63)/4)*z189 - (21)*z70
  have z206 : w 206=0 := by
    have h:=pivot0_270 w hw
    linear_combination h - ((-21))*z70 - (63/4)*z189
  have z201 : w 201=0 := by
    have h:=pivot0_269 w hw
    linear_combination h - (14)*z70 - (28/9)*z224
  have z198 : w 198=0 := by
    have h:=pivot0_268 w hw
    linear_combination h - ((-7)/4)*z189 - (21)*z70
  have z192 : w 192=0 := by
    have h:=pivot0_267 w hw
    linear_combination h - (14)*z70 - (7/9)*z224
  have z243 : w 243=0 := by
    have h:=pivot0_266 w hw
    linear_combination h - ((-14))*z70 - ((-28)/9)*z224
  have z228 : w 228=0 := by
    have h:=pivot0_265 w hw
    linear_combination h - (1)*z192
  have z240 : w 240=0 := by
    have h:=pivot0_264 w hw
    linear_combination h - (7/4)*z189 - ((-21))*z70
  have z238 : w 238=0 := by
    have h:=pivot0_263 w hw
    linear_combination h - ((-1))*z224
  have z186 : w 186=0 := by
    have h:=pivot0_262 w hw
    linear_combination h - (7/9)*z238 - (14)*z70
  have z234 : w 234=0 := by
    have h:=pivot0_261 w hw
    linear_combination h - ((-14))*z70 - ((-7)/9)*z224
  have z180 : w 180=0 := by
    have h:=pivot0_260 w hw
    linear_combination h - (21)*z70 - ((-7)/4)*z189
  have z182 : w 182=0 := by
    have h:=pivot0_259 w hw
    linear_combination h - (1)*z224
  have z177 : w 177=0 := by
    have h:=pivot0_258 w hw
    linear_combination h - (28/9)*z224 - (14)*z70
  have z172 : w 172=0 := by
    have h:=pivot0_257 w hw
    linear_combination h - (63/4)*z189 - ((-21))*z70
  have z231 : w 231=0 := by
    have h:=pivot0_256 w hw
    linear_combination h - (1)*z189
  have z248 : w 248=0 := by
    have h:=pivot0_255 w hw
    linear_combination h - ((-63)/4)*z189 - (21)*z70
  have z109 : w 109=0 := by
    have h:=pivot0_254 w hw
    linear_combination h - ((-13))*z70
  have z157 : w 157=0 := by
    have h:=pivot0_253 w hw
    linear_combination h - (10)*z70
  have z143 : w 143=0 := by
    have h:=pivot0_252 w hw
    linear_combination h - ((-3))*z70
  have z149 : w 149=0 := by
    have h:=pivot0_251 w hw
    linear_combination h - ((-5))*z70
  have z145 : w 145=0 := by
    have h:=pivot0_250 w hw
    linear_combination h - (5)*z70
  have z148 : w 148=0 := by
    have h:=pivot0_249 w hw
    linear_combination h - (2)*z70
  have z140 : w 140=0 := by
    have h:=pivot0_248 w hw
    linear_combination h
  have z105 : w 105=0 := by
    have h:=pivot0_247 w hw
    linear_combination h
  have z111 : w 111=0 := by
    have h:=pivot0_246 w hw
    linear_combination h - ((-1))*z105 - (3)*z70 - (1)*z140
  have z139 : w 139=0 := by
    have h:=pivot0_245 w hw
    linear_combination h - (1)*z111 - (1)*z140 - ((-3))*z70
  have z155 : w 155=0 := by
    have h:=pivot0_244 w hw
    linear_combination h - (3)*z70 - ((-1))*z140 - ((-1))*z111
  have z146 : w 146=0 := by
    have h:=pivot0_243 w hw
    linear_combination h - (1)*z70 - (1)*z111
  have z99 : w 99=0 := by
    have h:=pivot0_242 w hw
    linear_combination h - (1)*z111 - (2)*z140
  have z110 : w 110=0 := by
    have h:=pivot0_241 w hw
    linear_combination h - (1)*z140 - ((-1))*z105
  have z142 : w 142=0 := by
    have h:=pivot0_240 w hw
    linear_combination h - ((-1))*z140 - (1)*z105
  have z89 : w 89=0 := by
    have h:=pivot0_239 w hw
    linear_combination h - (8)*z70 - (1)*z105
  have z160 : w 160=0 := by
    have h:=pivot0_238 w hw
    linear_combination h - (12)*z70 - ((-1))*z140
  have z158 : w 158=0 := by
    have h:=pivot0_237 w hw
    linear_combination h - (1)*z99 - (9)*z70
  have z94 : w 94=0 := by
    have h:=pivot0_236 w hw
    linear_combination h - ((-1))*z111 - (9)*z70
  have z92 : w 92=0 := by
    have h:=pivot0_235 w hw
    linear_combination h - (12)*z70 - (1)*z140
  have z163 : w 163=0 := by
    have h:=pivot0_234 w hw
    linear_combination h - (8)*z70 - ((-1))*z105
  have z144 : w 144=0 := by
    have h:=pivot0_233 w hw
    linear_combination h - ((-6))*z70 - ((-1))*z140
  have z138 : w 138=0 := by
    have h:=pivot0_232 w hw
    linear_combination h - ((-6))*z70 - (1)*z105
  have z135 : w 135=0 := by
    have h:=pivot0_231 w hw
    linear_combination h - ((-1))*z140 - ((-3))*z70
  have z130 : w 130=0 := by
    have h:=pivot0_230 w hw
    linear_combination h - ((-1))*z105 - (2)*z70
  have z122 : w 122=0 := by
    have h:=pivot0_229 w hw
    linear_combination h - (2)*z70 - (1)*z105
  have z117 : w 117=0 := by
    have h:=pivot0_228 w hw
    linear_combination h - ((-3))*z70 - (1)*z140
  have z114 : w 114=0 := by
    have h:=pivot0_227 w hw
    linear_combination h - ((-1))*z105 - ((-6))*z70
  have z108 : w 108=0 := by
    have h:=pivot0_226 w hw
    linear_combination h - ((-6))*z70 - (1)*z140
  have z159 : w 159=0 := by
    have h:=pivot0_225 w hw
    linear_combination h - (3)*z70 - ((-1))*z140
  have z156 : w 156=0 := by
    have h:=pivot0_224 w hw
    linear_combination h - (1)*z105 - (6)*z70
  have z154 : w 154=0 := by
    have h:=pivot0_223 w hw
    linear_combination h - ((-1))*z140
  have z102 : w 102=0 := by
    have h:=pivot0_222 w hw
    linear_combination h - (1)*z154 - (6)*z70
  have z150 : w 150=0 := by
    have h:=pivot0_221 w hw
    linear_combination h - (6)*z70 - ((-1))*z140
  have z96 : w 96=0 := by
    have h:=pivot0_220 w hw
    linear_combination h - (6)*z70 - ((-1))*z105
  have z98 : w 98=0 := by
    have h:=pivot0_219 w hw
    linear_combination h - (1)*z140
  have z93 : w 93=0 := by
    have h:=pivot0_218 w hw
    linear_combination h - (1)*z140 - (3)*z70
  have z88 : w 88=0 := by
    have h:=pivot0_217 w hw
    linear_combination h - (1)*z105 - ((-2))*z70
  have z147 : w 147=0 := by
    have h:=pivot0_216 w hw
    linear_combination h - (1)*z105
  have z164 : w 164=0 := by
    have h:=pivot0_215 w hw
    linear_combination h - ((-1))*z105 - ((-2))*z70
  have z25 : w 25=0 := by
    have h:=pivot0_214 w hw
    linear_combination h - (13/28)*z70
  have z73 : w 73=0 := by
    have h:=pivot0_213 w hw
    linear_combination h
  have z59 : w 59=0 := by
    have h:=pivot0_212 w hw
    linear_combination h - ((-13)/28)*z70
  have z65 : w 65=0 := by
    have h:=pivot0_211 w hw
    linear_combination h - ((-115)/84)*z70
  have z61 : w 61=0 := by
    have h:=pivot0_210 w hw
    linear_combination h - ((-115)/84)*z70
  have z62 : w 62=0 := by
    have h:=pivot0_209 w hw
    linear_combination h - ((-31)/21)*z70
  have z21 : w 21=0 := by
    have h:=pivot0_208 w hw
    linear_combination h - (3/2)*z70
  have z64 : w 64=0 := by
    have h:=pivot0_207 w hw
    linear_combination h - ((-1))*z62
  have z10 : w 10=0 := by
    have h:=pivot0_206 w hw
    linear_combination h - (4/7)*z21 - (9/7)*z70
  have z15 : w 15=0 := by
    have h:=pivot0_205 w hw
    linear_combination h - (9/7)*z21 - (81/28)*z70
  have z26 : w 26=0 := by
    have h:=pivot0_204 w hw
    linear_combination h - (1/7)*z70 - ((-4)/7)*z21
  have z58 : w 58=0 := by
    have h:=pivot0_203 w hw
    linear_combination h - (4/7)*z21 - ((-1)/7)*z70
  have z55 : w 55=0 := by
    have h:=pivot0_202 w hw
    linear_combination h - (9/4)*z10 - (1/28)*z70
  have z71 : w 71=0 := by
    have h:=pivot0_201 w hw
    linear_combination h - (1/28)*z70 - (1)*z15
  have z308 : w 308=0 := by
    have h:=pivot0_200 w hw
    linear_combination h - (1)*z280
  have z331 : w 331=0 := by
    have h:=pivot0_199 w hw
    linear_combination h - (1)*z289
  have z286 : w 286=0 := by
    have h:=pivot0_198 w hw
    linear_combination h - (1)*z328
  have z284 : w 284=0 := by
    have h:=pivot0_197 w hw
    linear_combination h - (1)*z326
  have z283 : w 283=0 := by
    have h:=pivot0_196 w hw
    linear_combination h - (1)*z325
  have z281 : w 281=0 := by
    have h:=pivot0_195 w hw
    linear_combination h - (1)*z323
  have z321 : w 321=0 := by
    have h:=pivot0_194 w hw
    linear_combination h - (1)*z279
  have z320 : w 320=0 := by
    have h:=pivot0_193 w hw
    linear_combination h - (1)*z278
  have z319 : w 319=0 := by
    have h:=pivot0_192 w hw
    linear_combination h - (1)*z277
  have z275 : w 275=0 := by
    have h:=pivot0_191 w hw
    linear_combination h - (1)*z317
  have z274 : w 274=0 := by
    have h:=pivot0_190 w hw
    linear_combination h - (1)*z316
  have z272 : w 272=0 := by
    have h:=pivot0_189 w hw
    linear_combination h - (1)*z314
  have z271 : w 271=0 := by
    have h:=pivot0_188 w hw
    linear_combination h - (1)*z313
  have z269 : w 269=0 := by
    have h:=pivot0_187 w hw
    linear_combination h - (1)*z311
  have z268 : w 268=0 := by
    have h:=pivot0_186 w hw
    linear_combination h - (1)*z310
  have z309 : w 309=0 := by
    have h:=pivot0_185 w hw
    linear_combination h - (1)*z267
  have z265 : w 265=0 := by
    have h:=pivot0_184 w hw
    linear_combination h - (1)*z307
  have z262 : w 262=0 := by
    have h:=pivot0_183 w hw
    linear_combination h - (1)*z304
  have z302 : w 302=0 := by
    have h:=pivot0_182 w hw
    linear_combination h - (1)*z260
  have z299 : w 299=0 := by
    have h:=pivot0_181 w hw
    linear_combination h - (1)*z257
  have z196 : w 196=0 := by
    have h:=pivot0_180 w hw
    linear_combination h - (1)*z224
  have z205 : w 205=0 := by
    have h:=pivot0_179 w hw
    linear_combination h - (1)*z247
  have z202 : w 202=0 := by
    have h:=pivot0_178 w hw
    linear_combination h - (1)*z244
  have z200 : w 200=0 := by
    have h:=pivot0_177 w hw
    linear_combination h - (1)*z242
  have z199 : w 199=0 := by
    have h:=pivot0_176 w hw
    linear_combination h - (1)*z241
  have z197 : w 197=0 := by
    have h:=pivot0_175 w hw
    linear_combination h - (1)*z239
  have z237 : w 237=0 := by
    have h:=pivot0_174 w hw
    linear_combination h - (1)*z195
  have z236 : w 236=0 := by
    have h:=pivot0_173 w hw
    linear_combination h - (1)*z194
  have z235 : w 235=0 := by
    have h:=pivot0_172 w hw
    linear_combination h - (1)*z193
  have z191 : w 191=0 := by
    have h:=pivot0_171 w hw
    linear_combination h - (1)*z233
  have z190 : w 190=0 := by
    have h:=pivot0_170 w hw
    linear_combination h - (1)*z232
  have z188 : w 188=0 := by
    have h:=pivot0_169 w hw
    linear_combination h - (1)*z230
  have z187 : w 187=0 := by
    have h:=pivot0_168 w hw
    linear_combination h - (1)*z229
  have z185 : w 185=0 := by
    have h:=pivot0_167 w hw
    linear_combination h - (1)*z227
  have z184 : w 184=0 := by
    have h:=pivot0_166 w hw
    linear_combination h - (1)*z226
  have z225 : w 225=0 := by
    have h:=pivot0_165 w hw
    linear_combination h - (1)*z183
  have z181 : w 181=0 := by
    have h:=pivot0_164 w hw
    linear_combination h - (1)*z223
  have z178 : w 178=0 := by
    have h:=pivot0_163 w hw
    linear_combination h - (1)*z220
  have z218 : w 218=0 := by
    have h:=pivot0_162 w hw
    linear_combination h - (1)*z176
  have z215 : w 215=0 := by
    have h:=pivot0_161 w hw
    linear_combination h - (1)*z173
  have z112 : w 112=0 := by
    have h:=pivot0_160 w hw
    linear_combination h - (1)*z140
  have z121 : w 121=0 := by
    have h:=pivot0_159 w hw
    linear_combination h - (1)*z163
  have z118 : w 118=0 := by
    have h:=pivot0_158 w hw
    linear_combination h - (1)*z160
  have z116 : w 116=0 := by
    have h:=pivot0_157 w hw
    linear_combination h - (1)*z158
  have z115 : w 115=0 := by
    have h:=pivot0_156 w hw
    linear_combination h - (1)*z157
  have z113 : w 113=0 := by
    have h:=pivot0_155 w hw
    linear_combination h - (1)*z155
  have z153 : w 153=0 := by
    have h:=pivot0_154 w hw
    linear_combination h - (1)*z111
  have z152 : w 152=0 := by
    have h:=pivot0_153 w hw
    linear_combination h - (1)*z110
  have z151 : w 151=0 := by
    have h:=pivot0_152 w hw
    linear_combination h - (1)*z109
  have z107 : w 107=0 := by
    have h:=pivot0_151 w hw
    linear_combination h - (1)*z149
  have z106 : w 106=0 := by
    have h:=pivot0_150 w hw
    linear_combination h - (1)*z148
  have z104 : w 104=0 := by
    have h:=pivot0_149 w hw
    linear_combination h - (1)*z146
  have z103 : w 103=0 := by
    have h:=pivot0_148 w hw
    linear_combination h - (1)*z145
  have z101 : w 101=0 := by
    have h:=pivot0_147 w hw
    linear_combination h - (1)*z143
  have z100 : w 100=0 := by
    have h:=pivot0_146 w hw
    linear_combination h - (1)*z142
  have z141 : w 141=0 := by
    have h:=pivot0_145 w hw
    linear_combination h - (1)*z99
  have z97 : w 97=0 := by
    have h:=pivot0_144 w hw
    linear_combination h - (1)*z139
  have z136 : w 136=0 := by
    have h:=pivot0_143 w hw
    linear_combination h - (1)*z94
  have z134 : w 134=0 := by
    have h:=pivot0_142 w hw
    linear_combination h - (1)*z92
  have z131 : w 131=0 := by
    have h:=pivot0_141 w hw
    linear_combination h - (1)*z89
  have z56 : w 56=0 := by
    have h:=pivot0_140 w hw
    linear_combination h - ((-1))*z70
  have z37 : w 37=0 := by
    have h:=pivot0_139 w hw
    linear_combination h - (1/63)*z21
  have z34 : w 34=0 := by
    have h:=pivot0_138 w hw
    linear_combination h - (1/7)*z56
  have z32 : w 32=0 := by
    have h:=pivot0_137 w hw
    linear_combination h - ((-4)/9)*z15
  have z31 : w 31=0 := by
    have h:=pivot0_136 w hw
    linear_combination h - (1)*z73
  have z29 : w 29=0 := by
    have h:=pivot0_135 w hw
    linear_combination h - (1)*z71
  have z27 : w 27=0 := by
    have h:=pivot0_134 w hw
    linear_combination h - ((-9)/4)*z10
  have z68 : w 68=0 := by
    have h:=pivot0_133 w hw
    linear_combination h - (1)*z26
  have z67 : w 67=0 := by
    have h:=pivot0_132 w hw
    linear_combination h - (1)*z25
  have z23 : w 23=0 := by
    have h:=pivot0_131 w hw
    linear_combination h - (1)*z65
  have z22 : w 22=0 := by
    have h:=pivot0_130 w hw
    linear_combination h - (1)*z64
  have z20 : w 20=0 := by
    have h:=pivot0_129 w hw
    linear_combination h - (1)*z62
  have z19 : w 19=0 := by
    have h:=pivot0_128 w hw
    linear_combination h - (1)*z61
  have z17 : w 17=0 := by
    have h:=pivot0_127 w hw
    linear_combination h - (1)*z59
  have z16 : w 16=0 := by
    have h:=pivot0_126 w hw
    linear_combination h - (1)*z58
  have z57 : w 57=0 := by
    have h:=pivot0_125 w hw
    linear_combination h - (1)*z15
  have z13 : w 13=0 := by
    have h:=pivot0_124 w hw
    linear_combination h - (1)*z55
  have z52 : w 52=0 := by
    have h:=pivot0_123 w hw
    linear_combination h - (1)*z10
  have z50 : w 50=0 := by
    have h:=pivot0_122 w hw
    linear_combination h - ((-1)/7)*z70
  have z47 : w 47=0 := by
    have h:=pivot0_121 w hw
    linear_combination h - ((-1)/63)*z21
  have z5 : w 5=0 := by
    have h:=pivot0_120 w hw
    linear_combination h - (1/63)*z21
  have z76 : w 76=0 := by
    have h:=pivot0_119 w hw
    linear_combination h - ((-1)/7)*z56
  have z74 : w 74=0 := by
    have h:=pivot0_118 w hw
    linear_combination h - (4/9)*z15
  have z69 : w 69=0 := by
    have h:=pivot0_117 w hw
    linear_combination h - (9/4)*z10
  have z8 : w 8=0 := by
    have h:=pivot0_116 w hw
    linear_combination h - (1/7)*z70
  have z79 : w 79=0 := by
    have h:=pivot0_115 w hw
    linear_combination h - ((-1)/63)*z21
  have z60 : w 60=0 := by
    have h:=pivot0_114 w hw
    linear_combination h - ((-9)/7)*z70
  have z54 : w 54=0 := by
    have h:=pivot0_113 w hw
    linear_combination h - (4/7)*z21
  have z51 : w 51=0 := by
    have h:=pivot0_112 w hw
    linear_combination h - ((-9)/28)*z56
  have z46 : w 46=0 := by
    have h:=pivot0_111 w hw
    linear_combination h - ((-4)/63)*z21
  have z38 : w 38=0 := by
    have h:=pivot0_110 w hw
    linear_combination h - (4/63)*z21
  have z33 : w 33=0 := by
    have h:=pivot0_109 w hw
    linear_combination h - (9/28)*z70
  have z30 : w 30=0 := by
    have h:=pivot0_108 w hw
    linear_combination h - ((-4)/7)*z21
  have z28 : w 28=0 := by
    have h:=pivot0_107 w hw
    linear_combination h - (1)*z70
  have z24 : w 24=0 := by
    have h:=pivot0_106 w hw
    linear_combination h - (9/7)*z56
  have z14 : w 14=0 := by
    have h:=pivot0_105 w hw
    linear_combination h - (1)*z56
  have z63 : w 63=0 := by
    have h:=pivot0_104 w hw
    linear_combination h - (1)*z21
  have z75 : w 75=0 := by
    have h:=pivot0_103 w hw
    linear_combination h - (9/28)*z28
  have z72 : w 72=0 := by
    have h:=pivot0_102 w hw
    linear_combination h - (4/7)*z21
  have z18 : w 18=0 := by
    have h:=pivot0_101 w hw
    linear_combination h - (9/7)*z70
  have z66 : w 66=0 := by
    have h:=pivot0_100 w hw
    linear_combination h - (9/7)*z14
  have z12 : w 12=0 := by
    have h:=pivot0_99 w hw
    linear_combination h - (4/7)*z63
  have z9 : w 9=0 := by
    have h:=pivot0_98 w hw
    linear_combination h - (9/28)*z56
  have z4 : w 4=0 := by
    have h:=pivot0_97 w hw
    linear_combination h - (4/63)*z21
  have z80 : w 80=0 := by
    have h:=pivot0_96 w hw
    linear_combination h - ((-4)/63)*z21
  have z263 : w 263=0 := by
    have h:=pivot0_95 w hw
    linear_combination h
  have z305 : w 305=0 := by
    have h:=pivot0_94 w hw
    linear_combination h
  have z335 : w 335=0 := by
    have h:=pivot0_93 w hw
    linear_combination h
  have z301 : w 301=0 := by
    have h:=pivot0_92 w hw
    linear_combination h
  have z297 : w 297=0 := by
    have h:=pivot0_91 w hw
    linear_combination h
  have z296 : w 296=0 := by
    have h:=pivot0_90 w hw
    linear_combination h
  have z295 : w 295=0 := by
    have h:=pivot0_89 w hw
    linear_combination h
  have z293 : w 293=0 := by
    have h:=pivot0_88 w hw
    linear_combination h
  have z292 : w 292=0 := by
    have h:=pivot0_87 w hw
    linear_combination h
  have z291 : w 291=0 := by
    have h:=pivot0_86 w hw
    linear_combination h
  have z287 : w 287=0 := by
    have h:=pivot0_85 w hw
    linear_combination h
  have z329 : w 329=0 := by
    have h:=pivot0_84 w hw
    linear_combination h
  have z288 : w 288=0 := by
    have h:=pivot0_83 w hw
    linear_combination h
  have z300 : w 300=0 := by
    have h:=pivot0_82 w hw
    linear_combination h
  have z259 : w 259=0 := by
    have h:=pivot0_81 w hw
    linear_combination h
  have z258 : w 258=0 := by
    have h:=pivot0_80 w hw
    linear_combination h
  have z255 : w 255=0 := by
    have h:=pivot0_79 w hw
    linear_combination h
  have z254 : w 254=0 := by
    have h:=pivot0_78 w hw
    linear_combination h
  have z253 : w 253=0 := by
    have h:=pivot0_77 w hw
    linear_combination h
  have z330 : w 330=0 := by
    have h:=pivot0_76 w hw
    linear_combination h
  have z294 : w 294=0 := by
    have h:=pivot0_75 w hw
    linear_combination h
  have z333 : w 333=0 := by
    have h:=pivot0_74 w hw
    linear_combination h
  have z334 : w 334=0 := by
    have h:=pivot0_73 w hw
    linear_combination h
  have z252 : w 252=0 := by
    have h:=pivot0_72 w hw
    linear_combination h
  have z179 : w 179=0 := by
    have h:=pivot0_71 w hw
    linear_combination h
  have z221 : w 221=0 := by
    have h:=pivot0_70 w hw
    linear_combination h
  have z251 : w 251=0 := by
    have h:=pivot0_69 w hw
    linear_combination h
  have z217 : w 217=0 := by
    have h:=pivot0_68 w hw
    linear_combination h
  have z213 : w 213=0 := by
    have h:=pivot0_67 w hw
    linear_combination h
  have z212 : w 212=0 := by
    have h:=pivot0_66 w hw
    linear_combination h
  have z211 : w 211=0 := by
    have h:=pivot0_65 w hw
    linear_combination h
  have z209 : w 209=0 := by
    have h:=pivot0_64 w hw
    linear_combination h
  have z208 : w 208=0 := by
    have h:=pivot0_63 w hw
    linear_combination h
  have z207 : w 207=0 := by
    have h:=pivot0_62 w hw
    linear_combination h
  have z203 : w 203=0 := by
    have h:=pivot0_61 w hw
    linear_combination h
  have z245 : w 245=0 := by
    have h:=pivot0_60 w hw
    linear_combination h
  have z204 : w 204=0 := by
    have h:=pivot0_59 w hw
    linear_combination h
  have z216 : w 216=0 := by
    have h:=pivot0_58 w hw
    linear_combination h
  have z175 : w 175=0 := by
    have h:=pivot0_57 w hw
    linear_combination h
  have z174 : w 174=0 := by
    have h:=pivot0_56 w hw
    linear_combination h
  have z171 : w 171=0 := by
    have h:=pivot0_55 w hw
    linear_combination h
  have z170 : w 170=0 := by
    have h:=pivot0_54 w hw
    linear_combination h
  have z169 : w 169=0 := by
    have h:=pivot0_53 w hw
    linear_combination h
  have z246 : w 246=0 := by
    have h:=pivot0_52 w hw
    linear_combination h
  have z210 : w 210=0 := by
    have h:=pivot0_51 w hw
    linear_combination h
  have z249 : w 249=0 := by
    have h:=pivot0_50 w hw
    linear_combination h
  have z250 : w 250=0 := by
    have h:=pivot0_49 w hw
    linear_combination h
  have z168 : w 168=0 := by
    have h:=pivot0_48 w hw
    linear_combination h
  have z95 : w 95=0 := by
    have h:=pivot0_47 w hw
    linear_combination h
  have z137 : w 137=0 := by
    have h:=pivot0_46 w hw
    linear_combination h
  have z167 : w 167=0 := by
    have h:=pivot0_45 w hw
    linear_combination h
  have z133 : w 133=0 := by
    have h:=pivot0_44 w hw
    linear_combination h
  have z129 : w 129=0 := by
    have h:=pivot0_43 w hw
    linear_combination h
  have z128 : w 128=0 := by
    have h:=pivot0_42 w hw
    linear_combination h
  have z127 : w 127=0 := by
    have h:=pivot0_41 w hw
    linear_combination h
  have z125 : w 125=0 := by
    have h:=pivot0_40 w hw
    linear_combination h
  have z124 : w 124=0 := by
    have h:=pivot0_39 w hw
    linear_combination h
  have z123 : w 123=0 := by
    have h:=pivot0_38 w hw
    linear_combination h
  have z119 : w 119=0 := by
    have h:=pivot0_37 w hw
    linear_combination h
  have z161 : w 161=0 := by
    have h:=pivot0_36 w hw
    linear_combination h
  have z120 : w 120=0 := by
    have h:=pivot0_35 w hw
    linear_combination h
  have z132 : w 132=0 := by
    have h:=pivot0_34 w hw
    linear_combination h
  have z91 : w 91=0 := by
    have h:=pivot0_33 w hw
    linear_combination h
  have z90 : w 90=0 := by
    have h:=pivot0_32 w hw
    linear_combination h
  have z87 : w 87=0 := by
    have h:=pivot0_31 w hw
    linear_combination h
  have z86 : w 86=0 := by
    have h:=pivot0_30 w hw
    linear_combination h
  have z85 : w 85=0 := by
    have h:=pivot0_29 w hw
    linear_combination h
  have z162 : w 162=0 := by
    have h:=pivot0_28 w hw
    linear_combination h
  have z126 : w 126=0 := by
    have h:=pivot0_27 w hw
    linear_combination h
  have z165 : w 165=0 := by
    have h:=pivot0_26 w hw
    linear_combination h
  have z166 : w 166=0 := by
    have h:=pivot0_25 w hw
    linear_combination h
  have z84 : w 84=0 := by
    have h:=pivot0_24 w hw
    linear_combination h
  have z11 : w 11=0 := by
    have h:=pivot0_23 w hw
    linear_combination h
  have z53 : w 53=0 := by
    have h:=pivot0_22 w hw
    linear_combination h
  have z83 : w 83=0 := by
    have h:=pivot0_21 w hw
    linear_combination h
  have z49 : w 49=0 := by
    have h:=pivot0_20 w hw
    linear_combination h
  have z45 : w 45=0 := by
    have h:=pivot0_19 w hw
    linear_combination h
  have z44 : w 44=0 := by
    have h:=pivot0_18 w hw
    linear_combination h
  have z43 : w 43=0 := by
    have h:=pivot0_17 w hw
    linear_combination h
  have z41 : w 41=0 := by
    have h:=pivot0_16 w hw
    linear_combination h
  have z40 : w 40=0 := by
    have h:=pivot0_15 w hw
    linear_combination h
  have z39 : w 39=0 := by
    have h:=pivot0_14 w hw
    linear_combination h
  have z35 : w 35=0 := by
    have h:=pivot0_13 w hw
    linear_combination h
  have z77 : w 77=0 := by
    have h:=pivot0_12 w hw
    linear_combination h
  have z36 : w 36=0 := by
    have h:=pivot0_11 w hw
    linear_combination h
  have z48 : w 48=0 := by
    have h:=pivot0_10 w hw
    linear_combination h
  have z7 : w 7=0 := by
    have h:=pivot0_9 w hw
    linear_combination h
  have z6 : w 6=0 := by
    have h:=pivot0_8 w hw
    linear_combination h
  have z3 : w 3=0 := by
    have h:=pivot0_7 w hw
    linear_combination h
  have z2 : w 2=0 := by
    have h:=pivot0_6 w hw
    linear_combination h
  have z1 : w 1=0 := by
    have h:=pivot0_5 w hw
    linear_combination h
  have z78 : w 78=0 := by
    have h:=pivot0_4 w hw
    linear_combination h
  have z42 : w 42=0 := by
    have h:=pivot0_3 w hw
    linear_combination h
  have z81 : w 81=0 := by
    have h:=pivot0_2 w hw
    linear_combination h
  have z82 : w 82=0 := by
    have h:=pivot0_1 w hw
    linear_combination h
  have z0 : w 0=0 := by
    have h:=pivot0_0 w hw
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
  · exact z264
  · exact z265
  · exact z266
  · exact z267
  · exact z268
  · exact z269
  · exact z270
  · exact z271
  · exact z272
  · exact z273
  · exact z274
  · exact z275
  · exact z276
  · exact z277
  · exact z278
  · exact z279
  · exact z280
  · exact z281
  · exact z282
  · exact z283
  · exact z284
  · exact z285
  · exact z286
  · exact z287
  · exact z288
  · exact z289
  · exact z290
  · exact z291
  · exact z292
  · exact z293
  · exact z294
  · exact z295
  · exact z296
  · exact z297
  · exact z298
  · exact z299
  · exact z300
  · exact z301
  · exact z302
  · exact z303
  · exact z304
  · exact z305
  · exact z306
  · exact z307
  · exact z308
  · exact z309
  · exact z310
  · exact z311
  · exact z312
  · exact z313
  · exact z314
  · exact z315
  · exact z316
  · exact z317
  · exact z318
  · exact z319
  · exact z320
  · exact z321
  · exact z322
  · exact z323
  · exact z324
  · exact z325
  · exact z326
  · exact z327
  · exact z328
  · exact z329
  · exact z330
  · exact z331
  · exact z332
  · exact z333
  · exact z334
  · exact z335

#print axioms kernel0
end SmallLevelTwentyEightThirdJetTriangular
