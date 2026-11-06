module
public import SmallLevelThirtyFourUnitMMMTriangularBundleV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 6000
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMM
open Complex

theorem residual_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 213
  change (((1)/(Z)))*v 0 + ((1))*v 48 + (((1)/(Z)))*v 102 + ((1))*v 150 + (((1)/(Z)))*v 204 + ((1))*v 354 + (((1)/(Z)))*v 408 + ((1))*v 456=0 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Z)))*p10 - (((1)/(Z)))*p113 - (((1)/(Z)))*p120 - (((1)/(Z)))*p165 - ((((-1)*X)/(W^2)))*p194 - ((((-1))/(W^2)))*p230 - ((1))*p233 - ((1))*p262 - ((1))*p293 - ((1))*p332 - ((((-1))/(X)))*p353

theorem residual_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2*Z)/(X*W^2)) + (((-1)*Y^2*Z)/(W^2)))*v 370 + (((1*Z)/(X)) + ((2*Z)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X^2*Y^2*Z)/(W^2)))*v 390 + ((((-1)*Z)/(2*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Z)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2*Z*a^2)/(2*W^2)) + ((1*X^4*Y^3*Z*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 216
  change ((1))*v 0 + ((1*Z))*v 48 + ((1))*v 102 + ((1*Z))*v 150 + ((1))*v 204 + ((1*Z))*v 354 + ((1))*v 408 + ((1*Z))*v 456=0 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p10 - ((1))*p113 - ((1))*p120 - ((1))*p165 - ((((-1)*X*Z)/(W^2)))*p194 - ((((-1)*Z)/(W^2)))*p230 - ((1*Z))*p233 - ((1*Z))*p262 - ((1*Z))*p293 - ((1*Z))*p332 - ((((-1)*Z)/(X)))*p353

theorem residual_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 221
  change (((1)/(X*Y^2)))*v 0 + (((1)/(X*Y^2)))*v 30 + ((1))*v 35 + (((1)/(X*Y^2)))*v 60 + ((1))*v 65 + (((1)/(X*Y^2)))*v 90 + ((1))*v 95 + (((1)/(X*Y^2)))*v 120 + ((1))*v 125 + (((1)/(X*Y^2)))*v 150 + ((1))*v 155 + (((1)/(X*Y^2)))*v 180 + ((1))*v 185 + (((1)/(X*Y^2)))*v 210 + ((1))*v 215 + (((1)/(X*Y^2)))*v 240 + ((1))*v 245 + (((1)/(X*Y^2)))*v 270 + ((1))*v 275 + (((1)/(X*Y^2)))*v 300 + ((1))*v 305 + (((1)/(X*Y^2)))*v 330 + ((1))*v 335 + (((1)/(X*Y^2)))*v 360 + ((1))*v 365 + (((1)/(X*Y^2)))*v 390 + ((1))*v 395 + ((1))*v 425 + (((1)/(X*Y^2)))*v 450 + ((1))*v 455 + (((1)/(X*Y^2)))*v 480 + ((1))*v 485=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p251:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X*Y^2)))*p3 - (((1)/(X*Y^2)))*p9 - (((1)/(X*Y^2)))*p10 - ((1))*p12 - (((1)/(X*Y^2)))*p13 - (((1)/(X*Y^2)))*p15 - (((1)/(X*Y^2)))*p27 - (((1)/(X*Y^2)))*p77 - ((1))*p89 - (((1)/(X*Y^2)))*p91 - ((1))*p95 - ((1))*p100 - (((1)/(X*Y^2)))*p121 - ((1))*p138 - ((1))*p142 - ((((-1)*W^2)/(X*Y^2*Z)))*p143 - ((1))*p145 - ((1))*p147 - ((1))*p148 - (((1)/(X*Y^2)))*p150 - ((1))*p154 - (((1)/(Y^2)))*p189 - (((2)/(Y^2)))*p194 - (((2)/(X*Y^2)))*p195 - ((1))*p210 - (((1)/(X*Y^2)))*p232 - (((2)/(X*Y^2)))*p233 - (((1)/(X*Y^2)))*p235 - ((1))*p251 - ((1))*p254 - ((((-1)*Y^2)/(X)))*p256 - (((1)/(Y^2)))*p257 - (((1*W^2)/(X*Y^2)))*p262 - ((1))*p273 - (((1*W^2)/(X*Y^2)))*p302 - ((1))*p304 - ((1))*p317 - (((-1)))*p319 - (((1*W^2)/(X*Y^2)))*p322 - (((-1)))*p330 - (((1*W^2)/(X*Y^2)))*p331 - ((((-1)*W^2)/(X*Y^2)) + ((1*W^2)/(Y^2)))*p335 - (((1)/(X)) + ((-1)))*p358

theorem residual_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^2)) + ((4)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((5)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-8)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-10)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-9)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)))*v 435=0 := by
  have h:=hv 223
  change (((1*X)/(W^2)))*v 15 + ((1))*v 36 + (((1*X)/(W^2)))*v 45 + ((1))*v 66 + (((1*X)/(W^2)))*v 75 + ((1))*v 96 + (((1*X)/(W^2)))*v 105 + ((1))*v 126 + (((1*X)/(W^2)))*v 135 + ((1))*v 156 + (((1*X)/(W^2)))*v 165 + ((1))*v 186 + (((1*X)/(W^2)))*v 195 + ((1))*v 216 + (((1*X)/(W^2)))*v 225 + ((1))*v 246 + (((1*X)/(W^2)))*v 255 + ((1))*v 276 + (((1*X)/(W^2)))*v 285 + ((1))*v 306 + (((1*X)/(W^2)))*v 315 + ((1))*v 336 + (((1*X)/(W^2)))*v 345 + ((1))*v 366 + (((1*X)/(W^2)))*v 375 + ((1))*v 396 + (((1*X)/(W^2)))*v 405 + ((1))*v 426 + ((1))*v 456 + (((1*X)/(W^2)))*v 465 + ((1))*v 486 + (((1*X)/(W^2)))*v 495=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*X)/(W^2)))*p2 - (((1*X)/(W^2)))*p5 - (((1*X)/(W^2)))*p6 - ((1))*p16 - (((1*X)/(W^2)))*p83 - ((1))*p96 - (((1*X)/(W^2)))*p99 - (((1*X)/(W^2)))*p102 - ((1))*p114 - ((1))*p115 - ((1))*p127 - (((1*X)/(W^2)))*p131 - (((1*X)/(W^2)))*p137 - ((1))*p143 - ((1))*p162 - (((2*X)/(W^2)))*p189 - (((2*X)/(W^2)))*p194 - ((((-1)*Z)/(W^2)))*p195 - (((1*X)/(W^2)))*p196 - (((2*X)/(W^2)))*p198 - ((1))*p199 - (((2*X)/(W^2)))*p202 - ((1))*p204 - (((1*X)/(W^2)))*p208 - (((1*Z)/(W^2)))*p230 - (((2)/(W^2)) + (((-1)*X)/(W^2)))*p235 - (((1*X)/(W^2)))*p236 - (((1*Y^2)/(W^2)))*p256 - ((((-1)*X)/(W^2)))*p257 - ((1))*p269 - ((1))*p309 - (((-1)*X))*p310 - (((-1)*X))*p322 - ((1))*p327 - ((1))*p332 - ((1))*p341 - ((1))*p346 - (((-1)*X))*p354 - ((((-1))/(X)))*p355 - ((1))*p356 - ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p358

theorem residual_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*b)/(W)) + (2) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(W)) + (((-1)*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-7)*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-5)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-17)*X^4)/(2*W^2)) + ((3*X^4*Z)/(2*W^2)) + (((-2)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 224
  change (((1*X)/(W^2)))*v 15 + ((1))*v 24 + (((1*X)/(W^2)))*v 45 + ((1))*v 54 + ((1))*v 84 + (((1*X)/(W^2)))*v 105 + ((1))*v 114 + (((1*X)/(W^2)))*v 135 + ((1))*v 144 + (((1*X)/(W^2)))*v 165 + ((1))*v 174 + (((1*X)/(W^2)))*v 195 + ((1))*v 204 + (((1*X)/(W^2)))*v 225 + ((1))*v 234 + (((1*X)/(W^2)))*v 255 + ((1))*v 264 + (((1*X)/(W^2)))*v 285 + ((1))*v 294 + (((1*X)/(W^2)))*v 315 + ((1))*v 324 + (((1*X)/(W^2)))*v 345 + ((1))*v 354 + (((1*X)/(W^2)))*v 375 + ((1))*v 384 + (((1*X)/(W^2)))*v 405 + ((1))*v 414 + (((1*X)/(W^2)))*v 435 + ((1))*v 444 + (((1*X)/(W^2)))*v 465 + ((1))*v 474 + (((1*X)/(W^2)))*v 495=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - (((1*X)/(W^2)))*p2 - (((1*X)/(W^2)))*p5 - (((1*X)/(W^2)))*p6 - (((1*X)/(W^2)))*p83 - (((1*X)/(W^2)))*p99 - (((1*X)/(W^2)))*p102 - ((1))*p104 - ((1))*p109 - ((1))*p126 - (((1*X)/(W^2)))*p131 - (((1*X)/(W^2)))*p137 - ((1))*p152 - ((1))*p158 - ((1))*p165 - (((1*X)/(W^2)))*p189 - (((1*X)/(W^2)))*p194 - (((1*X)/(W^2)))*p196 - (((2*X)/(W^2)))*p198 - (((2*X)/(W^2)))*p202 - (((1*X)/(W^2)))*p208 - ((1))*p220 - ((1))*p224 - ((((-1)*Z)/(W^2)))*p230 - (((1)/(W^2)) + (((-1)*X)/(W^2)))*p235 - (((2*X)/(W^2)))*p236 - ((((-1)*Y^2)/(W^2)))*p256 - (((1*X)/(W^2)))*p257 - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p267 - (((-1)*X))*p274 - ((1))*p288 - ((1))*p293 - (((-1)*X))*p313 - ((1))*p339 - ((1))*p342 - ((((-1))/(X)))*p353 - ((((-1))/(X)))*p354 - (((-1)*X))*p355 - ((1))*p357 - ((((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*p358

theorem residual_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^4)) + ((4)/(X^3*W^2)) + ((2)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((4*Y^2)/(X^3*W^2)) + ((2)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-4))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-1))/(X*W^2)) + ((2*b)/(X*W)) + ((1*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + (((-1)*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-5)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-2))/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((4*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + (((-2)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-15))/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((1*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + (((-2)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-13))/(2*W^2)) + ((2*b)/(W)) + (2) + ((2*Z)/(W^2)) + ((1*Y*Z*a)/(W^2)) + (((-5)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^2*Z)/(W^2)) + (((-2)*Y^3*a)/(W^2)) + (((-3)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-5)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(2*W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-7)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((15*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 225
  change (((1*Y^2)/(X*W^2)))*v 10 + ((1))*v 39 + (((1*Y^2)/(X*W^2)))*v 40 + ((1))*v 69 + (((1*Y^2)/(X*W^2)))*v 70 + ((1))*v 99 + (((1*Y^2)/(X*W^2)))*v 100 + ((1))*v 129 + (((1*Y^2)/(X*W^2)))*v 130 + ((1))*v 159 + (((1*Y^2)/(X*W^2)))*v 160 + ((1))*v 189 + (((1*Y^2)/(X*W^2)))*v 190 + ((1))*v 219 + (((1*Y^2)/(X*W^2)))*v 220 + ((1))*v 249 + (((1*Y^2)/(X*W^2)))*v 250 + ((1))*v 279 + (((1*Y^2)/(X*W^2)))*v 280 + ((1))*v 309 + (((1*Y^2)/(X*W^2)))*v 310 + ((1))*v 339 + (((1*Y^2)/(X*W^2)))*v 340 + ((1))*v 369 + (((1*Y^2)/(X*W^2)))*v 370 + ((1))*v 399 + (((1*Y^2)/(X*W^2)))*v 400 + ((1))*v 429 + (((1*Y^2)/(X*W^2)))*v 430 + ((1))*v 459 + ((1))*v 489 + (((1*Y^2)/(X*W^2)))*v 490=0 at h
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*Y^2)/(X*W^2)))*p31 - (((1*Y^2)/(X*W^2)))*p43 - (((1*Y^2)/(X*W^2)))*p60 - (((1*Y^2)/(X*W^2)))*p62 - ((1))*p87 - (((1*Y^2)/(X*W^2)))*p88 - ((1))*p97 - (((1*Y^2)/(X*W^2)))*p98 - ((1))*p116 - (((1*Y^2)/(X*W^2)))*p118 - ((1))*p135 - (((1*Y^2)/(X*W^2)))*p144 - ((1))*p153 - ((1))*p163 - (((1*Y^2)/(X*W^2)))*p193 - ((1))*p201 - (((2*Y^2)/(X*W^2)))*p205 - (((1)/(W^2)))*p208 - ((1))*p214 - ((((-2))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)))*p230 - ((((-1)*Z)/(X*W^2)))*p233 - ((((-1))/(W^2)))*p235 - (((1*Y^2)/(X*W^2)))*p239 - (((1*Y^2)/(X*W^2)))*p246 - ((2))*p253 - (((2*Y^2)/(X*W^2)))*p256 - (((2)/(W^2)) + (((-1)*Z)/(W^2)))*p257 - ((1))*p259 - ((1))*p261 - (((1*Y^2)/(X*W^2)))*p264 - (((1*Y^2)/(X*W^2)))*p277 - ((1))*p279 - ((1))*p298 - ((1))*p306 - ((((-1))/(X)))*p310 - ((1))*p329 - ((((-1)*Y^2)/(X*W^2)))*p330 - ((((-2))/(X)))*p331 - (((2)/(X)))*p335 - ((((-1))/(X)))*p337 - (((-1)))*p339 - (((-1)))*p342 - ((1))*p350 - ((((-1))/(X^3)) + (1*X))*p355 - ((((-1)*Y^2)/(X^3*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p358 - ((((-1))/(X)))*p394 - ((1))*p395

theorem residual_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^4)) + ((1)/(X^3*W^2)) + (((-1))/(X^3)) + (((-2)*Y^2)/(X^3*W^2)) + (((-3))/(X^2*W^2)) + ((1*b)/(X^2*W)) + ((1)/(X^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((1*b)/(W)) + (1) + ((1*Z)/(W^2)) + ((2*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + (((-3)*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(2*X*W^2)) + ((1*b)/(X*W)) + (((-1))/(2*X)) + ((1*Z)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + (((-1)*Y*a)/(2*X)) + ((1*Y*Z*a)/(2*X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^2)/(2*X)) + ((1*Y^2*Z)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + (((-3)*Y^4)/(2*X*W^2)) + ((7)/(2*W^2)) + (((-3))/(2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + (((-3)*Y^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((3*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((1*Y^4*a^2)/(2*W^2)) + ((1*Y^5*a)/(2*W^2)) + ((17*X)/(2*W^2)) + ((1*X*b)/(W)) + ((-2)*X) + (((-1)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + ((-1)*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((-1)*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + ((3*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(W^2)) + ((7*X^2)/(2*W^2)) + ((-1)*X^2) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((6*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 226
  change (((1*Y^2)/(X*W^2)))*v 20 + ((1))*v 21 + ((1))*v 51 + (((1*Y^2)/(X*W^2)))*v 80 + ((1))*v 81 + (((1*Y^2)/(X*W^2)))*v 110 + ((1))*v 111 + (((1*Y^2)/(X*W^2)))*v 140 + ((1))*v 141 + (((1*Y^2)/(X*W^2)))*v 170 + ((1))*v 171 + (((1*Y^2)/(X*W^2)))*v 200 + ((1))*v 201 + (((1*Y^2)/(X*W^2)))*v 230 + ((1))*v 231 + (((1*Y^2)/(X*W^2)))*v 260 + ((1))*v 261 + (((1*Y^2)/(X*W^2)))*v 290 + ((1))*v 291 + (((1*Y^2)/(X*W^2)))*v 320 + ((1))*v 321 + (((1*Y^2)/(X*W^2)))*v 350 + ((1))*v 351 + (((1*Y^2)/(X*W^2)))*v 380 + ((1))*v 381 + (((1*Y^2)/(X*W^2)))*v 410 + ((1))*v 411 + (((1*Y^2)/(X*W^2)))*v 440 + ((1))*v 441 + (((1*Y^2)/(X*W^2)))*v 470 + ((1))*v 471 + (((1*Y^2)/(X*W^2)))*v 500=0 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*Y^2)/(X*W^2)))*p1 - (((1*Y^2)/(X*W^2)))*p21 - (((1*Y^2)/(X*W^2)))*p64 - ((1))*p65 - ((1))*p66 - (((1*Y^2)/(X*W^2)))*p78 - ((1))*p80 - (((1)/(X*W^2)))*p91 - (((1*Y^2)/(X*W^2)))*p92 - (((1*Y^2)/(X*W^2)))*p93 - ((1))*p103 - (((1*Y^2)/(X*W^2)))*p117 - (((2)/(X)))*p126 - ((1))*p130 - ((1))*p151 - (((1*Y^2)/(X*W^2)))*p156 - ((1))*p157 - (((1*Y^2)/(X*W^2)))*p164 - (((2)/(W^2)) + (((-1)*Z)/(W^2)))*p189 - (((1*Y^2)/(X*W^2)))*p192 - (((3)/(W^2)))*p194 - ((((-1)*Y^2)/(X*W^2)))*p195 - (((1)/(W^2)))*p196 - ((1))*p211 - (((2*Y^2)/(X*W^2)))*p219 - ((1))*p222 - (((1*Y^2)/(X*W^2)))*p227 - (((2)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((2*Y^2)/(W^2)))*p230 - ((((-1)*Z)/(X*W^2)))*p232 - (((2)/(W^2)))*p236 - (((1*Y^2)/(X*W^2)))*p242 - (((2)/(X)))*p252 - ((((-2)*Y^2)/(X*W^2)))*p256 - ((((-2))/(W^2)) + ((1*Z)/(W^2)))*p257 - ((1))*p258 - ((1))*p265 - ((1))*p278 - ((1))*p291 - ((((-1))/(X)))*p313 - ((1))*p318 - (((1*Y^2)/(X*W^2)))*p319 - ((1*X))*p322 - (((1*Y^2)/(X*W^2)))*p330 - ((1))*p333 - ((((-2))/(X)))*p335 - ((((-1))/(X)))*p336 - (((-1)))*p341 - ((1))*p345 - ((1))*p351 - ((((-1))/(X^3)) + (1*X))*p354 - (((2*Y^2)/(X*W^2)))*p358 - ((((-1))/(X)))*p403 - ((((-1))/(X)))*p404

theorem residual_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + ((((-1))/(X^3)) + (((-4))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(W^2)) + ((1*Z)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 390 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((10*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((11*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-3)*X^3)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)))*v 435=0 := by
  have h:=hv 229
  change (((1*X*Y^2)/(W^2)))*v 5 + (((1*X*Y^2)/(W^2)))*v 35 + ((1))*v 48 + (((1*X*Y^2)/(W^2)))*v 65 + ((1))*v 78 + (((1*X*Y^2)/(W^2)))*v 95 + ((1))*v 108 + (((1*X*Y^2)/(W^2)))*v 125 + ((1))*v 138 + (((1*X*Y^2)/(W^2)))*v 155 + ((1))*v 168 + (((1*X*Y^2)/(W^2)))*v 185 + ((1))*v 198 + (((1*X*Y^2)/(W^2)))*v 215 + ((1))*v 228 + (((1*X*Y^2)/(W^2)))*v 245 + ((1))*v 258 + (((1*X*Y^2)/(W^2)))*v 275 + ((1))*v 288 + (((1*X*Y^2)/(W^2)))*v 305 + ((1))*v 318 + (((1*X*Y^2)/(W^2)))*v 335 + ((1))*v 348 + (((1*X*Y^2)/(W^2)))*v 365 + ((1))*v 378 + (((1*X*Y^2)/(W^2)))*v 395 + ((1))*v 408 + (((1*X*Y^2)/(W^2)))*v 425 + ((1))*v 438 + (((1*X*Y^2)/(W^2)))*v 455 + ((1))*v 468 + ((1))*v 498=0 at h
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p251:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*X*Y^2)/(W^2)))*p12 - (((1*X*Y^2)/(W^2)))*p35 - ((1))*p46 - ((1))*p58 - (((1*X*Y^2)/(W^2)))*p89 - (((1*X*Y^2)/(W^2)))*p95 - (((1*X*Y^2)/(W^2)))*p100 - ((1))*p120 - (((1*X*Y^2)/(W^2)))*p142 - (((1*X*Y^2)/(W^2)))*p145 - (((1*X*Y^2)/(W^2)))*p147 - (((1*X*Y^2)/(W^2)))*p148 - (((1*X*Y^2)/(W^2)))*p154 - ((1))*p180 - (((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)))*p194 - (((1*X*Y^2)/(W^2)))*p210 - (((1)/(W^2)))*p230 - (((1)/(W^2)))*p233 - (((1*X*Y^2)/(W^2)))*p251 - ((1))*p252 - (((1*X*Y^2)/(W^2)))*p254 - ((((-1)*Y^4)/(W^2)))*p256 - (((1*X)/(W^2)))*p257 - ((2))*p262 - (((1*X*Y^2)/(W^2)))*p273 - ((2))*p302 - (((1*X*Y^2)/(W^2)))*p304 - ((1))*p310 - (((1*X*Y^2)/(W^2)))*p317 - ((((-1)*X*Y^2)/(W^2)))*p319 - ((2))*p322 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p330 - ((2))*p331 - ((1))*p333 - (((-2)) + (1*X))*p335 - ((1))*p337 - ((1))*p353 - ((1))*p354 - (((1)/(X^2)))*p355 - (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(W^2)) + (((-2)*X*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394

#print axioms residual_7

end SmallLevelThirtyFourUnitMMM
