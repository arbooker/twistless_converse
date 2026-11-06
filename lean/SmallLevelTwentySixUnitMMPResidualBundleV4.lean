module
public import SmallLevelTwentySixUnitMMPTriangularBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixUnitMMP
open Complex

theorem residual_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((1)/(Z)) + (((-1)*X)/(Z)))*v 520 + ((((-1))/(X^2*Y^2)) + (((-1))/(X^2)) + ((1*a^2)/(X^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1))/(X)))*v 540=0 := by
  have h:=hv 242
  change (((1*X)/(Z)))*v 130 + ((1))*v 280 + (((1*X)/(Z)))*v 390 + ((1))*v 540=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*X)/(Z)))*p23 - (((1*X)/(Z)))*p86 - ((((-1))/(Y^2)))*p252 - ((1))*p273 - ((((-1))/(X)))*p290 - ((((-1)*X^2)/(Y^2*Z)) + (((-1)*X^2*a)/(Y*Z)))*p295 - (((-1)))*p300

theorem residual_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + ((1*X)/(Z)))*v 520 + (((1)/(X^2*Y^2)) + ((1)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X*Y^2)) + ((1*a)/(X*Y)) + ((1)/(X)))*v 540=0 := by
  have h:=hv 243
  change ((1))*v 240 + (((1*X)/(Z)))*v 390 + ((1))*v 500 + (((1*X)/(Z)))*v 650=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*X)/(Z)))*p23 - (((1*X)/(Z)))*p89 - ((((-1))/(Y^2)))*p245 - ((1))*p247 - (((1)/(Y^2)))*p252 - ((1))*p278 - ((((-1))/(X)))*p291 - (((1*X^2)/(Y^2*Z)) + ((1*X^2*a)/(Y*Z)))*p295 - (((-1)))*p301

theorem residual_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Z)) + (((-1)*Y*a)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + (((-1)*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-1)*X)/(Z)) + ((1*X^2)/(Z)))*v 520 + (((1)/(X*Y^2)) + ((1)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((1)/(Y^2)) + ((1*a)/(Y)) + (1))*v 540=0 := by
  have h:=hv 248
  change (((1*X^3)/(Z)))*v 195 + ((1))*v 300 + (((1*X^3)/(Z)))*v 455 + ((1))*v 560=0 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p150 - (((1*X^3)/(Z)))*p193 - ((((-1)*X)/(Y^2)))*p243 - (((1*X)/(Y^2)))*p252 - ((1))*p290 - (((1*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)) + ((1*X^3)/(Z)))*p295

theorem residual_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Z)) + ((1*Y*a)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + ((1*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + ((1*Y^4)/(Z)) + ((1*X)/(Z)) + (((-1)*X^2)/(Z)))*v 520 + ((((-1))/(X*Y^2)) + (((-1))/(X)) + ((1*a^2)/(X)) + ((1*Y*a)/(X)) + (((-1))/(Y^2)) + (((-1)*a)/(Y)) + ((-1)))*v 540=0 := by
  have h:=hv 249
  change ((1))*v 220 + (((1*X^3)/(Z)))*v 325 + ((1))*v 480 + (((1*X^3)/(Z)))*v 585=0 at h
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*X^3)/(Z)))*p85 - (((1*X^3)/(Z)))*p97 - ((1))*p185 - ((((-1)*W^2)/(Y^2)))*p189 - ((((-1)*Y^2)/(Z)))*p237 - (((-1)))*p238 - ((((-1)*X)/(Y^2)))*p244 - (((1*X)/(Y^2)))*p245 - ((((-1)*X)/(Y^2)))*p252 - ((1))*p291 - ((((-1)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)) + (((-1)*X^3)/(Z)))*p295

theorem residual_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^4)) + ((1*Y*a)/(X^4)) + (((-1)*Y^3*a)/(X^4)) + (((-1)*Y^4)/(X^4)) + ((1*Y^2)/(X^3)) + ((1*Y^3*a)/(X^3)) + ((1*Y^4)/(X^3)) + ((1)/(X^2)) + (((-1))/(X)))*v 520 + ((((-1)*Z)/(X^4*Y^2)) + (((-1)*Z)/(X^4)) + ((1*Z*a^2)/(X^4)) + ((1*Y*Z*a)/(X^4)) + (((-1)*Z)/(X^3*Y^2)) + (((-1)*Z*a)/(X^3*Y)) + (((-1)*Z)/(X^3)))*v 540=0 := by
  have h:=hv 252
  change (((1*Z)/(X^3)))*v 220 + ((1))*v 325 + (((1*Z)/(X^3)))*v 480 + ((1))*v 585=0 at h
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p85 - ((1))*p97 - (((1*Z)/(X^3)))*p185 - ((((-1)*Z*W^2)/(X^3*Y^2)))*p189 - ((((-1)*Y^2)/(X^3)))*p237 - ((((-1)*Z)/(X^3)))*p238 - ((((-1)*Z)/(X^2*Y^2)))*p244 - (((1*Z)/(X^2*Y^2)))*p245 - ((((-1)*Z)/(X^2*Y^2)))*p252 - (((1*Z)/(X^3)))*p291 - ((((-1))/(Y^2)) + (((-1)*a)/(Y)) + ((-1)))*p295

theorem residual_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^4)) + (((-1)*Y*a)/(X^4)) + ((1*Y^3*a)/(X^4)) + ((1*Y^4)/(X^4)) + (((-1)*Y^2)/(X^3)) + (((-1)*Y^3*a)/(X^3)) + (((-1)*Y^4)/(X^3)) + (((-1))/(X^2)) + ((1)/(X)))*v 520 + (((1*Z)/(X^4*Y^2)) + ((1*Z)/(X^4)) + (((-1)*Z*a^2)/(X^4)) + (((-1)*Y*Z*a)/(X^4)) + ((1*Z)/(X^3*Y^2)) + ((1*Z*a)/(X^3*Y)) + ((1*Z)/(X^3)))*v 540=0 := by
  have h:=hv 253
  change ((1))*v 195 + (((1*Z)/(X^3)))*v 300 + ((1))*v 455 + (((1*Z)/(X^3)))*v 560=0 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*Z)/(X^3)))*p150 - ((1))*p193 - ((((-1)*Z)/(X^2*Y^2)))*p243 - (((1*Z)/(X^2*Y^2)))*p252 - (((1*Z)/(X^3)))*p290 - (((1)/(Y^2)) + ((1*a)/(Y)) + (1))*p295

theorem residual_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3)) + (((-1)*Y*a)/(X^3)) + ((1*Y^3*a)/(X^3)) + ((1*Y^4)/(X^3)) + (((-1)*Y^2)/(X^2)) + (((-1)*Y^3*a)/(X^2)) + (((-1)*Y^4)/(X^2)) + (((-1))/(X)) + (1))*v 520 + (((1*Z)/(X^3*Y^2)) + ((1*Z)/(X^3)) + (((-1)*Z*a^2)/(X^3)) + (((-1)*Y*Z*a)/(X^3)) + ((1*Z)/(X^2*Y^2)) + ((1*Z*a)/(X^2*Y)) + ((1*Z)/(X^2)))*v 540=0 := by
  have h:=hv 254
  change (((1*Z)/(X)))*v 240 + ((1))*v 390 + (((1*Z)/(X)))*v 500 + ((1))*v 650=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p23 - ((1))*p89 - ((((-1)*Z)/(X*Y^2)))*p245 - (((1*Z)/(X)))*p247 - (((1*Z)/(X*Y^2)))*p252 - (((1*Z)/(X)))*p278 - ((((-1)*Z)/(X^2)))*p291 - (((1*X)/(Y^2)) + ((1*X*a)/(Y)))*p295 - ((((-1)*Z)/(X)))*p301

theorem residual_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^3)) + ((1*Y*a)/(X^3)) + (((-1)*Y^3*a)/(X^3)) + (((-1)*Y^4)/(X^3)) + ((1*Y^2)/(X^2)) + ((1*Y^3*a)/(X^2)) + ((1*Y^4)/(X^2)) + ((1)/(X)) + ((-1)))*v 520 + ((((-1)*Z)/(X^3*Y^2)) + (((-1)*Z)/(X^3)) + ((1*Z*a^2)/(X^3)) + ((1*Y*Z*a)/(X^3)) + (((-1)*Z)/(X^2*Y^2)) + (((-1)*Z*a)/(X^2*Y)) + (((-1)*Z)/(X^2)))*v 540=0 := by
  have h:=hv 255
  change ((1))*v 130 + (((1*Z)/(X)))*v 280 + ((1))*v 390 + (((1*Z)/(X)))*v 540=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p23 - ((1))*p86 - ((((-1)*Z)/(X*Y^2)))*p252 - (((1*Z)/(X)))*p273 - ((((-1)*Z)/(X^2)))*p290 - ((((-1)*X)/(Y^2)) + (((-1)*X*a)/(Y)))*p295 - ((((-1)*Z)/(X)))*p300

#print axioms residual_7

theorem residual_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^3*Z)) + (((-2)*Y^4)/(X^3*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((4*Y^4)/(X^2*Z)) + ((2)/(X*Z)) + ((1)/(X)) + ((1*Y*a)/(X*Z)) + (((-2)*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + ((-1)) + (((-3)*Y*a)/(Z)) + ((2*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + ((((-2))/(X^3)) + ((2*Y*a)/(X^3)) + (((-2)*Y*a)/(X^2)) + (((-2))/(X*Y^2)) + ((1*a)/(X*Y)) + ((2)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((2)/(Y^2)) + (2) + ((2*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 289
  change ((((-1))/(X*Y^2)))*v 0 + ((((-1))/(X*Y^2)))*v 60 + ((1))*v 70 + ((((-1))/(X*Y^2)))*v 120 + ((1))*v 130 + ((((-1))/(X*Y^2)))*v 180 + ((1))*v 190 + ((((-1))/(X*Y^2)))*v 240 + ((1))*v 250 + ((((-1))/(X*Y^2)))*v 300 + ((1))*v 310 + ((((-1))/(X*Y^2)))*v 360 + ((1))*v 370 + ((((-1))/(X*Y^2)))*v 420 + ((1))*v 430 + ((((-1))/(X*Y^2)))*v 480 + ((1))*v 490 + ((((-1))/(X*Y^2)))*v 540 + ((1))*v 550 + ((1))*v 610 + ((((-1))/(X*Y^2)))*v 660 + ((1))*v 670 + ((((-1))/(X*Y^2)))*v 720 + ((1))*v 730=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1))/(X*Y^2)))*p0 - ((((-1))/(X*Y^2)))*p18 - ((((-1))/(X*Y^2)))*p29 - ((((-1))/(X*Y^2)))*p30 - ((((-1))/(X*Y^2)))*p39 - ((1))*p86 - ((((-1))/(X*Y^2)))*p90 - ((1))*p99 - ((((-1)*W^2)/(X*Y^2*Z)))*p148 - ((((-1))/(X*Y^2)))*p150 - ((1))*p165 - ((1))*p177 - ((((-1))/(X*Y^2)))*p185 - ((1))*p192 - (((1)/(X*Z)))*p237 - ((((-1))/(X*Y^2)))*p238 - ((1))*p240 - ((((-1)*Z)/(X*Y^2)))*p252 - ((1))*p254 - (((-1)))*p272 - ((1))*p276 - ((1))*p285 - ((((-1)*X^2)/(Y^2*Z)) + ((1*X^3)/(Z)))*p295 - ((1))*p298 - ((1))*p300 - ((((-1))/(X)))*p302 - ((1))*p305 - (((1)/(X)) + ((-1)))*p308 - ((1))*p312

theorem residual_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X^3*Z)) + ((2*Y^4)/(X^3*Z)) + ((2*Y^2)/(X^2*Z)) + (((-4)*Y^4)/(X^2*Z)) + (((-2))/(X*Z)) + (((-1))/(X)) + (((-1)*Y*a)/(X*Z)) + ((2*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((1)/(Z)) + (1) + ((3*Y*a)/(Z)) + (((-2)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + ((1*Y^4)/(Z)) + ((2*X)/(Z)) + (((-1)*X*Y*a)/(Z)) + ((1*X*Y^2)/(Z)))*v 520 + (((2)/(X^3)) + (((-2)*Y*a)/(X^3)) + ((2*Y*a)/(X^2)) + ((2)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-2))/(X)) + ((1*a^2)/(X)) + ((1*Y*a)/(X)) + (((-2))/(Y^2)) + ((-2)) + (((-2)*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 290
  change ((((-1))/(X*Y^2)))*v 0 + ((1))*v 50 + ((((-1))/(X*Y^2)))*v 60 + ((1))*v 110 + ((((-1))/(X*Y^2)))*v 120 + ((1))*v 170 + ((1))*v 230 + ((((-1))/(X*Y^2)))*v 240 + ((1))*v 290 + ((((-1))/(X*Y^2)))*v 300 + ((1))*v 350 + ((((-1))/(X*Y^2)))*v 360 + ((1))*v 410 + ((((-1))/(X*Y^2)))*v 420 + ((1))*v 470 + ((((-1))/(X*Y^2)))*v 480 + ((1))*v 530 + ((((-1))/(X*Y^2)))*v 540 + ((1))*v 590 + ((((-1))/(X*Y^2)))*v 600 + ((1))*v 650 + ((((-1))/(X*Y^2)))*v 660 + ((1))*v 710 + ((((-1))/(X*Y^2)))*v 720=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1))/(X*Y^2)))*p0 - ((((-1))/(X*Y^2)))*p18 - ((((-1))/(X*Y^2)))*p29 - ((((-1))/(X*Y^2)))*p30 - ((((-1))/(X*Y^2)))*p39 - ((1))*p76 - ((1))*p89 - ((((-1))/(X*Y^2)))*p90 - ((((-1))/(X*Y^2)))*p150 - ((1))*p151 - ((1))*p153 - ((1))*p157 - ((((-1))/(X*Y^2)))*p185 - ((((-1)*W^2)/(X*Y^2*Z)))*p188 - (((1)/(X*Z)))*p237 - ((1))*p239 - ((((-1)*Z)/(X*Y^2)))*p245 - (((1*Z)/(X*Y^2)))*p252 - ((1))*p253 - ((1))*p272 - ((1))*p277 - (((-1)))*p285 - (((1*X^2)/(Y^2*Z)) + (((-1)*X^3)/(Z)))*p295 - ((1))*p299 - ((1))*p301 - (((-1)))*p302 - ((1))*p306 - ((1))*p307 - ((((-1))/(X)) + (1))*p308 - (((-1)))*p312

theorem residual_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((3*Y^4)/(X^2*Z)) + (((-1))/(X*Z)) + (((-1)*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-2)*Y^4)/(X*Z)) + (((-4))/(Z)) + ((-1)) + (((-2)*Y*a)/(Z)) + ((1*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + (((1)/(X^2*Y^2)) + ((3)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-3)*Y*a)/(X^2)) + ((2)/(X*Y^2)) + ((1*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((4)/(Y^2)) + (2) + ((2*X)/(Y^2)) + ((2*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 291
  change ((((-1)*X)/(Y^2)))*v 30 + ((1))*v 80 + ((((-1)*X)/(Y^2)))*v 90 + ((1))*v 140 + ((((-1)*X)/(Y^2)))*v 150 + ((1))*v 200 + ((((-1)*X)/(Y^2)))*v 210 + ((1))*v 260 + ((((-1)*X)/(Y^2)))*v 270 + ((1))*v 320 + ((((-1)*X)/(Y^2)))*v 330 + ((1))*v 380 + ((((-1)*X)/(Y^2)))*v 390 + ((1))*v 440 + ((((-1)*X)/(Y^2)))*v 450 + ((1))*v 500 + ((((-1)*X)/(Y^2)))*v 510 + ((1))*v 560 + ((((-1)*X)/(Y^2)))*v 570 + ((1))*v 620 + ((((-1)*X)/(Y^2)))*v 630 + ((1))*v 680 + ((1))*v 740 + ((((-1)*X)/(Y^2)))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*X)/(Y^2)))*p2 - ((((-1)*X)/(Y^2)))*p10 - ((((-1)*X)/(Y^2)))*p23 - ((1))*p43 - ((((-1)*X)/(Y^2)))*p81 - ((1))*p101 - ((1))*p154 - ((((-1)*X)/(Y^2)))*p155 - ((1))*p160 - ((((-1)*X)/(Y^2)))*p162 - ((1))*p237 - ((((-1)*X)/(Y^2)))*p243 - ((((-1)*X)/(Y^2)))*p244 - (((1*X)/(Y^2)))*p245 - ((((-1)*X)/(Y^2)))*p248 - (((1*X)/(Y^2)))*p261 - ((1))*p264 - ((1))*p270 - ((((-1)*X)/(Y^2)))*p272 - ((1))*p278 - ((1))*p285 - ((1))*p290 - ((((-1))/(X)))*p291 - (((1*X^2)/(Y^2*Z)) + ((1*X^2*a)/(Y*Z)) + ((1*X^2)/(Z)) + ((2*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)) + ((1*X^3)/(Z)) + ((1*X^4)/(Y^2*Z)))*p295 - (((-1)))*p301 - ((1))*p302 - ((1))*p303 - (((-1)))*p308

theorem residual_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + ((2*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-3)*Y^4)/(X^2*Z)) + ((1)/(X*Z)) + ((1*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + ((2*Y^4)/(X*Z)) + ((4)/(Z)) + (1) + ((2*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + ((1*Y^4)/(Z)) + ((2*X)/(Z)) + (((-1)*X*Y*a)/(Z)) + ((1*X*Y^2)/(Z)))*v 520 + ((((-1))/(X^2*Y^2)) + (((-3))/(X^2)) + ((1*a^2)/(X^2)) + ((3*Y*a)/(X^2)) + (((-2))/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-4))/(X)) + ((1*a^2)/(X)) + ((1*Y*a)/(X)) + (((-4))/(Y^2)) + ((-2)) + (((-2)*X)/(Y^2)) + (((-2)*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 292
  change ((((-1)*X)/(Y^2)))*v 30 + ((1))*v 40 + ((1))*v 100 + ((((-1)*X)/(Y^2)))*v 150 + ((1))*v 160 + ((((-1)*X)/(Y^2)))*v 210 + ((1))*v 220 + ((((-1)*X)/(Y^2)))*v 270 + ((1))*v 280 + ((((-1)*X)/(Y^2)))*v 330 + ((1))*v 340 + ((((-1)*X)/(Y^2)))*v 390 + ((1))*v 400 + ((((-1)*X)/(Y^2)))*v 450 + ((1))*v 460 + ((((-1)*X)/(Y^2)))*v 510 + ((1))*v 520 + ((((-1)*X)/(Y^2)))*v 570 + ((1))*v 580 + ((((-1)*X)/(Y^2)))*v 630 + ((1))*v 640 + ((((-1)*X)/(Y^2)))*v 690 + ((1))*v 700 + ((((-1)*X)/(Y^2)))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*X)/(Y^2)))*p2 - ((((-1)*X)/(Y^2)))*p10 - ((((-1)*X)/(Y^2)))*p23 - ((1))*p37 - ((1))*p74 - ((((-1)*X)/(Y^2)))*p94 - ((((-1)*X)/(Y^2)))*p155 - ((((-1)*X)/(Y^2)))*p162 - ((1))*p187 - ((1))*p198 - (((1)/(Z)))*p237 - ((((-1))/(Y^2)))*p238 - ((((-1)*X)/(Y^2)))*p243 - ((((-1)*X)/(Y^2)))*p244 - (((1*X)/(Y^2)))*p245 - ((1))*p246 - ((((-1)*X)/(Y^2)))*p249 - ((((-1)*X)/(Y^2)))*p261 - ((1))*p265 - ((1))*p268 - (((1*X)/(Y^2)))*p272 - ((1))*p273 - (((-1)))*p285 - ((((-1))/(X)))*p290 - ((1))*p291 - ((((-1)*X^2)/(Y^2*Z)) + (((-1)*X^2*a)/(Y*Z)) + (((-1)*X^2)/(Z)) + (((-2)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)) + (((-1)*X^3)/(Z)) + (((-1)*X^4)/(Y^2*Z)))*p295 - ((1))*p297 - (((-1)))*p300 - (((-1)))*p303 - ((1))*p308

theorem residual_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*Z)) + (((-1)*Y^3*a)/(X^3*Z)) + (((-2)*Y^4)/(X^3*Z)) + ((1*Y^5*a)/(X^3*Z)) + ((3*Y^6)/(X^3*Z)) + (((-1)*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + (((-2)*Y^6)/(X^2*Z)) + (((-4)*Y^2)/(X*Z)) + (((-1)*Y^2)/(X)) + (((-2)*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + (((-1)*Y^5*a)/(X*Z)) + (((-1)*Y^6)/(X*Z)) + (((-2)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)))*v 520 + (((1)/(X^3)) + ((3*Y^2)/(X^3)) + (((-1)*Y^2*a^2)/(X^3)) + (((-3)*Y^3*a)/(X^3)) + ((2)/(X^2)) + ((1*Y*a)/(X^2)) + ((4*Y^2)/(X^2)) + (((-1)*Y^2*a^2)/(X^2)) + (((-1)*Y^3*a)/(X^2)) + ((4)/(X)) + ((2*Y^2)/(X)) + (2) + (2*X))*v 540=0 := by
  have h:=hv 294
  change ((1))*v 30 + ((((-1)*Y^2)/(X)))*v 40 + ((((-1)*Y^2)/(X)))*v 100 + ((1))*v 150 + ((((-1)*Y^2)/(X)))*v 160 + ((1))*v 210 + ((((-1)*Y^2)/(X)))*v 220 + ((1))*v 270 + ((((-1)*Y^2)/(X)))*v 280 + ((1))*v 330 + ((((-1)*Y^2)/(X)))*v 340 + ((1))*v 390 + ((((-1)*Y^2)/(X)))*v 400 + ((1))*v 450 + ((((-1)*Y^2)/(X)))*v 460 + ((1))*v 510 + ((((-1)*Y^2)/(X)))*v 520 + ((1))*v 570 + ((((-1)*Y^2)/(X)))*v 580 + ((1))*v 630 + ((((-1)*Y^2)/(X)))*v 640 + ((1))*v 690 + ((((-1)*Y^2)/(X)))*v 700 + ((1))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p2 - ((1))*p10 - ((1))*p23 - ((((-1)*Y^2)/(X)))*p37 - ((((-1)*Y^2)/(X)))*p74 - ((1))*p94 - ((1))*p155 - ((1))*p162 - ((((-1)*Y^2)/(X)))*p187 - ((((-1)*Y^2)/(X)))*p198 - ((((-1)*Y^2)/(X*Z)))*p237 - (((1)/(X)))*p238 - ((1))*p243 - ((1))*p244 - (((-1)))*p245 - ((((-1)*Y^2)/(X)))*p246 - ((1))*p249 - ((1))*p261 - ((((-1)*Y^2)/(X)))*p265 - ((((-1)*Y^2)/(X)))*p268 - (((-1)))*p272 - ((((-1)*Y^2)/(X)))*p273 - (((1*Y^2)/(X)))*p285 - (((1*Y^2)/(X^2)))*p290 - ((((-1)*Y^2)/(X)))*p291 - (((1*X)/(Z)) + ((1*X*Y*a)/(Z)) + ((1*X*Y^2)/(Z)) + ((2*X^2)/(Z)) + ((1*X^2*Y*a)/(Z)) + ((1*X^2*Y^2)/(Z)) + ((1*X^3)/(Z)))*p295 - ((((-1)*Y^2)/(X)))*p297 - (((1*Y^2)/(X)))*p300 - (((1*Y^2)/(X)))*p303 - ((((-1)*Y^2)/(X)))*p308

theorem residual_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^3*Z)) + ((1*Y^3*a)/(X^3*Z)) + ((2*Y^4)/(X^3*Z)) + (((-1)*Y^5*a)/(X^3*Z)) + (((-3)*Y^6)/(X^3*Z)) + ((1*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + ((2*Y^6)/(X^2*Z)) + ((4*Y^2)/(X*Z)) + ((1*Y^2)/(X)) + ((2*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + ((1*Y^5*a)/(X*Z)) + ((1*Y^6)/(X*Z)) + ((2*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + ((1*Y^4)/(Z)))*v 520 + ((((-1))/(X^3)) + (((-3)*Y^2)/(X^3)) + ((1*Y^2*a^2)/(X^3)) + ((3*Y^3*a)/(X^3)) + (((-2))/(X^2)) + (((-1)*Y*a)/(X^2)) + (((-4)*Y^2)/(X^2)) + ((1*Y^2*a^2)/(X^2)) + ((1*Y^3*a)/(X^2)) + (((-4))/(X)) + (((-2)*Y^2)/(X)) + ((-2)) + ((-2)*X))*v 540=0 := by
  have h:=hv 295
  change ((1))*v 30 + ((((-1)*Y^2)/(X)))*v 80 + ((1))*v 90 + ((((-1)*Y^2)/(X)))*v 140 + ((1))*v 150 + ((((-1)*Y^2)/(X)))*v 200 + ((1))*v 210 + ((((-1)*Y^2)/(X)))*v 260 + ((1))*v 270 + ((((-1)*Y^2)/(X)))*v 320 + ((1))*v 330 + ((((-1)*Y^2)/(X)))*v 380 + ((1))*v 390 + ((((-1)*Y^2)/(X)))*v 440 + ((1))*v 450 + ((((-1)*Y^2)/(X)))*v 500 + ((1))*v 510 + ((((-1)*Y^2)/(X)))*v 560 + ((1))*v 570 + ((((-1)*Y^2)/(X)))*v 620 + ((1))*v 630 + ((((-1)*Y^2)/(X)))*v 680 + ((((-1)*Y^2)/(X)))*v 740 + ((1))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p2 - ((1))*p10 - ((1))*p23 - ((((-1)*Y^2)/(X)))*p43 - ((1))*p81 - ((((-1)*Y^2)/(X)))*p101 - ((((-1)*Y^2)/(X)))*p154 - ((1))*p155 - ((((-1)*Y^2)/(X)))*p160 - ((1))*p162 - ((((-1)*Y^2)/(X)))*p237 - ((1))*p243 - ((1))*p244 - (((-1)))*p245 - ((1))*p248 - (((-1)))*p261 - ((((-1)*Y^2)/(X)))*p264 - ((((-1)*Y^2)/(X)))*p270 - ((1))*p272 - ((((-1)*Y^2)/(X)))*p278 - ((((-1)*Y^2)/(X)))*p285 - ((((-1)*Y^2)/(X)))*p290 - (((1*Y^2)/(X^2)))*p291 - ((((-1)*X)/(Z)) + (((-1)*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)) + (((-2)*X^2)/(Z)) + (((-1)*X^2*Y*a)/(Z)) + (((-1)*X^2*Y^2)/(Z)) + (((-1)*X^3)/(Z)))*p295 - (((1*Y^2)/(X)))*p301 - ((((-1)*Y^2)/(X)))*p302 - ((((-1)*Y^2)/(X)))*p303 - (((1*Y^2)/(X)))*p308

theorem residual_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^4)/(X^2*Z)) + (((-2)*Y^6)/(X^2*Z)) + (((-2)*Y^4)/(X*Z)) + ((4*Y^6)/(X*Z)) + ((2*Y^2)/(Z)) + (1*Y^2) + ((1*Y^3*a)/(Z)) + (((-2)*Y^4)/(Z)) + ((1*Y^5*a)/(Z)) + (((-1)*Y^6)/(Z)) + (((-1)*X*Y^2)/(Z)) + ((-1)*X*Y^2) + (((-3)*X*Y^3*a)/(Z)) + ((2*X*Y^4)/(Z)) + (((-1)*X*Y^5*a)/(Z)) + (((-1)*X*Y^6)/(Z)) + (((-2)*X^2*Y^2)/(Z)) + ((1*X^2*Y^3*a)/(Z)) + (((-1)*X^2*Y^4)/(Z)))*v 520 + ((((-2)*Y^2)/(X^2)) + ((2*Y^3*a)/(X^2)) + (((-2)*Y^3*a)/(X)) + ((-2)) + (1*Y*a) + (2*Y^2) + ((-1)*Y^2*a^2) + ((-1)*Y^3*a) + (2*X) + (2*X*Y^2) + (2*X^3))*v 540=0 := by
  have h:=hv 296
  change ((1))*v 0 + (((-1)*X*Y^2))*v 50 + ((1))*v 60 + (((-1)*X*Y^2))*v 110 + ((1))*v 120 + (((-1)*X*Y^2))*v 170 + (((-1)*X*Y^2))*v 230 + ((1))*v 240 + (((-1)*X*Y^2))*v 290 + ((1))*v 300 + (((-1)*X*Y^2))*v 350 + ((1))*v 360 + (((-1)*X*Y^2))*v 410 + ((1))*v 420 + (((-1)*X*Y^2))*v 470 + ((1))*v 480 + (((-1)*X*Y^2))*v 530 + ((1))*v 540 + (((-1)*X*Y^2))*v 590 + ((1))*v 600 + (((-1)*X*Y^2))*v 650 + ((1))*v 660 + (((-1)*X*Y^2))*v 710 + ((1))*v 720=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p18 - ((1))*p29 - ((1))*p30 - ((1))*p39 - (((-1)*X*Y^2))*p76 - (((-1)*X*Y^2))*p89 - ((1))*p90 - ((1))*p150 - (((-1)*X*Y^2))*p151 - (((-1)*X*Y^2))*p153 - (((-1)*X*Y^2))*p157 - ((1))*p185 - (((1*W^2)/(Z)))*p188 - ((((-1)*Y^2)/(Z)))*p237 - (((-1)*X*Y^2))*p239 - ((1*Z))*p245 - (((-1)*Z))*p252 - (((-1)*X*Y^2))*p253 - (((-1)*X*Y^2))*p272 - (((-1)*X*Y^2))*p277 - ((1*X*Y^2))*p285 - ((((-1)*X^3)/(Z)) + ((1*X^4*Y^2)/(Z)))*p295 - (((-1)*X*Y^2))*p299 - (((-1)*X*Y^2))*p301 - ((1*X*Y^2))*p302 - (((-1)*X*Y^2))*p306 - (((-1)*X*Y^2))*p307 - ((1*Y^2) + ((-1)*X*Y^2))*p308 - ((1*X*Y^2))*p312

theorem residual_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^4)/(X^2*Z)) + ((2*Y^6)/(X^2*Z)) + ((2*Y^4)/(X*Z)) + (((-4)*Y^6)/(X*Z)) + (((-2)*Y^2)/(Z)) + ((-1)*Y^2) + (((-1)*Y^3*a)/(Z)) + ((2*Y^4)/(Z)) + (((-1)*Y^5*a)/(Z)) + ((1*Y^6)/(Z)) + ((1*X*Y^2)/(Z)) + (1*X*Y^2) + ((3*X*Y^3*a)/(Z)) + (((-2)*X*Y^4)/(Z)) + ((1*X*Y^5*a)/(Z)) + ((1*X*Y^6)/(Z)) + ((2*X^2*Y^2)/(Z)) + (((-1)*X^2*Y^3*a)/(Z)) + ((1*X^2*Y^4)/(Z)))*v 520 + (((2*Y^2)/(X^2)) + (((-2)*Y^3*a)/(X^2)) + ((2*Y^3*a)/(X)) + (2) + ((-1)*Y*a) + ((-2)*Y^2) + (1*Y^2*a^2) + (1*Y^3*a) + ((-2)*X) + ((-2)*X*Y^2) + ((-2)*X^3))*v 540=0 := by
  have h:=hv 297
  change ((1))*v 0 + ((1))*v 60 + (((-1)*X*Y^2))*v 70 + ((1))*v 120 + (((-1)*X*Y^2))*v 130 + ((1))*v 180 + (((-1)*X*Y^2))*v 190 + ((1))*v 240 + (((-1)*X*Y^2))*v 250 + ((1))*v 300 + (((-1)*X*Y^2))*v 310 + ((1))*v 360 + (((-1)*X*Y^2))*v 370 + ((1))*v 420 + (((-1)*X*Y^2))*v 430 + ((1))*v 480 + (((-1)*X*Y^2))*v 490 + ((1))*v 540 + (((-1)*X*Y^2))*v 550 + (((-1)*X*Y^2))*v 610 + ((1))*v 660 + (((-1)*X*Y^2))*v 670 + ((1))*v 720 + (((-1)*X*Y^2))*v 730=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p18 - ((1))*p29 - ((1))*p30 - ((1))*p39 - (((-1)*X*Y^2))*p86 - ((1))*p90 - (((-1)*X*Y^2))*p99 - (((1*W^2)/(Z)))*p148 - ((1))*p150 - (((-1)*X*Y^2))*p165 - (((-1)*X*Y^2))*p177 - ((1))*p185 - (((-1)*X*Y^2))*p192 - ((((-1)*Y^2)/(Z)))*p237 - ((1))*p238 - (((-1)*X*Y^2))*p240 - ((1*Z))*p252 - (((-1)*X*Y^2))*p254 - ((1*X*Y^2))*p272 - (((-1)*X*Y^2))*p276 - (((-1)*X*Y^2))*p285 - (((1*X^3)/(Z)) + (((-1)*X^4*Y^2)/(Z)))*p295 - (((-1)*X*Y^2))*p298 - (((-1)*X*Y^2))*p300 - ((1*Y^2))*p302 - (((-1)*X*Y^2))*p305 - (((-1)*Y^2) + (1*X*Y^2))*p308 - (((-1)*X*Y^2))*p312

#print axioms residual_15

theorem residual_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X^3*Z)) + ((2*Y^4)/(X^3*Z)) + (((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + (((-3))/(X*Z)) + (((-1))/(X)) + (((-2)*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + (((-3))/(Z)) + ((1*Y*a)/(Z)) + (((-1)*Y^2)/(Z)))*v 520 + (((2)/(X^3)) + (((-2)*Y*a)/(X^3)) + ((1)/(X^2*Y^2)) + ((3)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((4)/(X*Y^2)) + ((2)/(X)) + ((2)/(Y^2)) + ((2*X)/(Y^2)))*v 540=0 := by
  have h:=hv 310
  change ((((-1))/(Y^2)))*v 0 + ((1))*v 20 + ((((-1))/(Y^2)))*v 30 + ((1))*v 50 + ((((-1))/(Y^2)))*v 60 + ((1))*v 80 + ((((-1))/(Y^2)))*v 90 + ((1))*v 110 + ((((-1))/(Y^2)))*v 120 + ((1))*v 140 + ((1))*v 170 + ((((-1))/(Y^2)))*v 180 + ((((-1))/(Y^2)))*v 210 + ((1))*v 230 + ((((-1))/(Y^2)))*v 240 + ((1))*v 260 + ((((-1))/(Y^2)))*v 270 + ((1))*v 290 + ((((-1))/(Y^2)))*v 300 + ((1))*v 320 + ((((-1))/(Y^2)))*v 330 + ((1))*v 350 + ((((-1))/(Y^2)))*v 360 + ((1))*v 380 + ((((-1))/(Y^2)))*v 390 + ((1))*v 410 + ((((-1))/(Y^2)))*v 420 + ((1))*v 440 + ((((-1))/(Y^2)))*v 450 + ((1))*v 470 + ((((-1))/(Y^2)))*v 480 + ((1))*v 500 + ((((-1))/(Y^2)))*v 510 + ((1))*v 530 + ((1))*v 560 + ((((-1))/(Y^2)))*v 570 + ((((-1))/(Y^2)))*v 600 + ((1))*v 620 + ((((-1))/(Y^2)))*v 630 + ((1))*v 650 + ((((-1))/(Y^2)))*v 660 + ((1))*v 680 + ((((-1))/(Y^2)))*v 690 + ((1))*v 710 + ((((-1))/(Y^2)))*v 720 + ((1))*v 740 + ((((-1))/(Y^2)))*v 750 + ((1))*v 770=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1))/(Y^2)))*p0 - ((((-1))/(Y^2)))*p2 - ((((-1))/(Y^2)))*p10 - ((1))*p11 - ((((-1))/(Y^2)))*p18 - ((((-1))/(Y^2)))*p23 - ((1))*p28 - ((((-1))/(Y^2)))*p29 - ((((-1))/(Y^2)))*p30 - ((((-1))/(Y^2)))*p39 - ((1))*p43 - ((1))*p76 - ((((-1))/(Y^2)))*p81 - ((1))*p89 - ((((-1))/(Y^2)))*p90 - ((((-1))/(Y^2)))*p94 - ((1))*p101 - ((((-1))/(Y^2)))*p150 - ((1))*p151 - ((1))*p153 - ((1))*p154 - ((((-1))/(Y^2)))*p155 - ((1))*p157 - ((1))*p160 - ((((-1))/(Y^2)))*p162 - ((((-1))/(Y^2)))*p185 - ((((-1)*W^2)/(X*Y^2*Z)))*p188 - (((1)/(X*Z)) + ((1)/(Z)) + (1))*p237 - ((((-1))/(Y^2)))*p243 - ((((-1))/(Y^2)))*p244 - ((((-1)*Z)/(X*Y^2)))*p245 - (((1)/(X*Y^2)) + (((-1))/(Y^2)))*p247 - ((((-1))/(Y^2)) + ((1*X)/(Y^2)))*p249 - (((1)/(X*Y^2)) + ((1*Z)/(X*Y^2)))*p252 - ((1))*p253 - ((((-1))/(Y^2)) + ((1*X)/(Y^2)))*p261 - ((1))*p264 - ((1))*p270 - ((1) + (((-1)*X)/(Y^2)))*p272 - ((1))*p277 - ((1))*p278 - ((1))*p290 - ((((-1))/(X)))*p291 - (((2*X^2)/(Y^2*Z)) + ((1*X^2*a)/(Y*Z)) + ((1*X^2)/(Z)) + ((2*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)) + ((1*X^4)/(Y^2*Z)))*p295 - ((1))*p299 - ((1))*p303 - ((1))*p306 - ((1))*p307 - ((((-1))/(X)))*p308 - (((-1)))*p312

theorem residual_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^3*Z)) + (((-2)*Y^4)/(X^3*Z)) + ((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + ((3)/(X*Z)) + ((1)/(X)) + ((2*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((3)/(Z)) + (((-1)*Y*a)/(Z)) + ((1*Y^2)/(Z)))*v 520 + ((((-2))/(X^3)) + ((2*Y*a)/(X^3)) + (((-1))/(X^2*Y^2)) + (((-3))/(X^2)) + ((1*a^2)/(X^2)) + ((1*Y*a)/(X^2)) + (((-4))/(X*Y^2)) + (((-2))/(X)) + (((-2))/(Y^2)) + (((-2)*X)/(Y^2)))*v 540=0 := by
  have h:=hv 311
  change ((((-1))/(Y^2)))*v 0 + ((1))*v 10 + ((((-1))/(Y^2)))*v 30 + ((1))*v 40 + ((((-1))/(Y^2)))*v 60 + ((1))*v 70 + ((((-1))/(Y^2)))*v 90 + ((1))*v 100 + ((((-1))/(Y^2)))*v 120 + ((1))*v 130 + ((((-1))/(Y^2)))*v 150 + ((1))*v 160 + ((((-1))/(Y^2)))*v 180 + ((((-1))/(Y^2)))*v 210 + ((1))*v 220 + ((1))*v 250 + ((((-1))/(Y^2)))*v 270 + ((1))*v 280 + ((((-1))/(Y^2)))*v 300 + ((1))*v 310 + ((((-1))/(Y^2)))*v 330 + ((1))*v 340 + ((((-1))/(Y^2)))*v 360 + ((1))*v 370 + ((((-1))/(Y^2)))*v 390 + ((1))*v 400 + ((((-1))/(Y^2)))*v 420 + ((1))*v 430 + ((((-1))/(Y^2)))*v 450 + ((1))*v 460 + ((((-1))/(Y^2)))*v 480 + ((1))*v 490 + ((((-1))/(Y^2)))*v 510 + ((1))*v 520 + ((((-1))/(Y^2)))*v 540 + ((1))*v 550 + ((((-1))/(Y^2)))*v 570 + ((((-1))/(Y^2)))*v 600 + ((1))*v 610 + ((1))*v 640 + ((((-1))/(Y^2)))*v 660 + ((1))*v 670 + ((((-1))/(Y^2)))*v 690 + ((1))*v 700 + ((((-1))/(Y^2)))*v 720 + ((1))*v 730 + ((((-1))/(Y^2)))*v 750 + ((1))*v 760=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1))/(Y^2)))*p0 - ((((-1))/(Y^2)))*p2 - ((1))*p8 - ((((-1))/(Y^2)))*p10 - ((((-1))/(Y^2)))*p18 - ((((-1))/(Y^2)))*p23 - ((1))*p25 - ((((-1))/(Y^2)))*p29 - ((((-1))/(Y^2)))*p30 - ((1))*p37 - ((((-1))/(Y^2)))*p39 - ((1))*p74 - ((((-1))/(Y^2)))*p81 - ((1))*p86 - ((((-1))/(Y^2)))*p90 - ((((-1))/(Y^2)))*p94 - ((1))*p99 - ((((-1)*W^2)/(X*Y^2*Z)))*p148 - ((((-1))/(Y^2)))*p150 - ((((-1))/(Y^2)))*p155 - ((((-1))/(Y^2)))*p162 - ((1))*p165 - ((1))*p177 - ((((-1))/(Y^2)))*p185 - ((1))*p187 - ((1))*p192 - ((1))*p198 - (((1)/(X*Z)) + ((1)/(Z)))*p237 - ((((-1))/(X*Y^2)) + (((-1))/(Y^2)))*p238 - ((((-1))/(Y^2)))*p243 - ((((-1))/(Y^2)))*p244 - (((1)/(X*Y^2)))*p245 - ((1))*p246 - (((1)/(X*Y^2)))*p247 - ((((-1))/(Y^2)) + ((1*X)/(Y^2)))*p248 - ((((-1))/(Y^2)))*p249 - ((((-1))/(X*Y^2)) + (((-1)*Z)/(X*Y^2)))*p252 - ((1))*p254 - (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*p261 - ((1))*p265 - ((1))*p268 - (((-1)) + ((1*X)/(Y^2)))*p272 - ((1))*p273 - ((1))*p276 - ((((-1))/(X)))*p290 - ((1))*p291 - ((((-2)*X^2)/(Y^2*Z)) + (((-1)*X^2*a)/(Y*Z)) + (((-1)*X^2)/(Z)) + (((-2)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)) + (((-1)*X^4)/(Y^2*Z)))*p295 - ((1))*p297 - ((1))*p298 - ((((-1))/(X)))*p302 - (((-1)))*p303 - ((1))*p305 - (((1)/(X)))*p308 - ((1))*p312

theorem residual_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^4)/(X^3*Z)) + ((2*Y^6)/(X^3*Z)) + (((-1)*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + ((1*Y^5*a)/(X^2*Z)) + (((-1)*Y^6)/(X^2*Z)) + (((-3)*Y^2)/(X*Z)) + (((-1)*Y^2)/(X)) + (((-2)*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + (((-1)*Y^5*a)/(X*Z)) + (((-1)*Y^6)/(X*Z)) + (((-3)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)))*v 520 + (((2*Y^2)/(X^3)) + (((-2)*Y^3*a)/(X^3)) + ((1)/(X^2)) + ((3*Y^2)/(X^2)) + (((-1)*Y^2*a^2)/(X^2)) + (((-1)*Y^3*a)/(X^2)) + ((4)/(X)) + ((2*Y^2)/(X)) + (2) + (2*X))*v 540=0 := by
  have h:=hv 312
  change ((1))*v 0 + (((-1)*Y^2))*v 10 + ((1))*v 30 + (((-1)*Y^2))*v 40 + ((1))*v 60 + (((-1)*Y^2))*v 70 + ((1))*v 90 + (((-1)*Y^2))*v 100 + ((1))*v 120 + (((-1)*Y^2))*v 130 + ((1))*v 150 + (((-1)*Y^2))*v 160 + ((1))*v 180 + ((1))*v 210 + (((-1)*Y^2))*v 220 + (((-1)*Y^2))*v 250 + ((1))*v 270 + (((-1)*Y^2))*v 280 + ((1))*v 300 + (((-1)*Y^2))*v 310 + ((1))*v 330 + (((-1)*Y^2))*v 340 + ((1))*v 360 + (((-1)*Y^2))*v 370 + ((1))*v 390 + (((-1)*Y^2))*v 400 + ((1))*v 420 + (((-1)*Y^2))*v 430 + ((1))*v 450 + (((-1)*Y^2))*v 460 + ((1))*v 480 + (((-1)*Y^2))*v 490 + ((1))*v 510 + (((-1)*Y^2))*v 520 + ((1))*v 540 + (((-1)*Y^2))*v 550 + ((1))*v 570 + ((1))*v 600 + (((-1)*Y^2))*v 610 + (((-1)*Y^2))*v 640 + ((1))*v 660 + (((-1)*Y^2))*v 670 + ((1))*v 690 + (((-1)*Y^2))*v 700 + ((1))*v 720 + (((-1)*Y^2))*v 730 + ((1))*v 750 + (((-1)*Y^2))*v 760=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p2 - (((-1)*Y^2))*p8 - ((1))*p10 - ((1))*p18 - ((1))*p23 - (((-1)*Y^2))*p25 - ((1))*p29 - ((1))*p30 - (((-1)*Y^2))*p37 - ((1))*p39 - (((-1)*Y^2))*p74 - ((1))*p81 - (((-1)*Y^2))*p86 - ((1))*p90 - ((1))*p94 - (((-1)*Y^2))*p99 - (((1*W^2)/(X*Z)))*p148 - ((1))*p150 - ((1))*p155 - ((1))*p162 - (((-1)*Y^2))*p165 - (((-1)*Y^2))*p177 - ((1))*p185 - (((-1)*Y^2))*p187 - (((-1)*Y^2))*p192 - (((-1)*Y^2))*p198 - ((((-1)*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)))*p237 - (((1)/(X)) + (1))*p238 - ((1))*p243 - ((1))*p244 - ((((-1))/(X)))*p245 - (((-1)*Y^2))*p246 - ((((-1))/(X)))*p247 - ((1) + ((-1)*X))*p248 - ((1))*p249 - (((1)/(X)) + ((1*Z)/(X)))*p252 - (((-1)*Y^2))*p254 - (((-1)) + (1*X))*p261 - (((-1)*Y^2))*p265 - (((-1)*Y^2))*p268 - ((1*Y^2) + ((-1)*X))*p272 - (((-1)*Y^2))*p273 - (((-1)*Y^2))*p276 - (((1*Y^2)/(X)))*p290 - (((-1)*Y^2))*p291 - (((2*X^2)/(Z)) + ((1*X^2*Y*a)/(Z)) + ((1*X^2*Y^2)/(Z)) + ((2*X^3)/(Z)) + ((1*X^3*Y*a)/(Z)) + ((1*X^4)/(Z)))*p295 - (((-1)*Y^2))*p297 - (((-1)*Y^2))*p298 - (((1*Y^2)/(X)))*p302 - ((1*Y^2))*p303 - (((-1)*Y^2))*p305 - ((((-1)*Y^2)/(X)))*p308 - (((-1)*Y^2))*p312

theorem residual_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^4)/(X^3*Z)) + (((-2)*Y^6)/(X^3*Z)) + ((1*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + (((-1)*Y^5*a)/(X^2*Z)) + ((1*Y^6)/(X^2*Z)) + ((3*Y^2)/(X*Z)) + ((1*Y^2)/(X)) + ((2*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + ((1*Y^5*a)/(X*Z)) + ((1*Y^6)/(X*Z)) + ((3*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + ((1*Y^4)/(Z)))*v 520 + ((((-2)*Y^2)/(X^3)) + ((2*Y^3*a)/(X^3)) + (((-1))/(X^2)) + (((-3)*Y^2)/(X^2)) + ((1*Y^2*a^2)/(X^2)) + ((1*Y^3*a)/(X^2)) + (((-4))/(X)) + (((-2)*Y^2)/(X)) + ((-2)) + ((-2)*X))*v 540=0 := by
  have h:=hv 313
  change ((1))*v 0 + (((-1)*Y^2))*v 20 + ((1))*v 30 + (((-1)*Y^2))*v 50 + ((1))*v 60 + (((-1)*Y^2))*v 80 + ((1))*v 90 + (((-1)*Y^2))*v 110 + ((1))*v 120 + (((-1)*Y^2))*v 140 + (((-1)*Y^2))*v 170 + ((1))*v 180 + ((1))*v 210 + (((-1)*Y^2))*v 230 + ((1))*v 240 + (((-1)*Y^2))*v 260 + ((1))*v 270 + (((-1)*Y^2))*v 290 + ((1))*v 300 + (((-1)*Y^2))*v 320 + ((1))*v 330 + (((-1)*Y^2))*v 350 + ((1))*v 360 + (((-1)*Y^2))*v 380 + ((1))*v 390 + (((-1)*Y^2))*v 410 + ((1))*v 420 + (((-1)*Y^2))*v 440 + ((1))*v 450 + (((-1)*Y^2))*v 470 + ((1))*v 480 + (((-1)*Y^2))*v 500 + ((1))*v 510 + (((-1)*Y^2))*v 530 + (((-1)*Y^2))*v 560 + ((1))*v 570 + ((1))*v 600 + (((-1)*Y^2))*v 620 + ((1))*v 630 + (((-1)*Y^2))*v 650 + ((1))*v 660 + (((-1)*Y^2))*v 680 + ((1))*v 690 + (((-1)*Y^2))*v 710 + ((1))*v 720 + (((-1)*Y^2))*v 740 + ((1))*v 750 + (((-1)*Y^2))*v 770=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p2 - ((1))*p10 - (((-1)*Y^2))*p11 - ((1))*p18 - ((1))*p23 - (((-1)*Y^2))*p28 - ((1))*p29 - ((1))*p30 - ((1))*p39 - (((-1)*Y^2))*p43 - (((-1)*Y^2))*p76 - ((1))*p81 - (((-1)*Y^2))*p89 - ((1))*p90 - ((1))*p94 - (((-1)*Y^2))*p101 - ((1))*p150 - (((-1)*Y^2))*p151 - (((-1)*Y^2))*p153 - (((-1)*Y^2))*p154 - ((1))*p155 - (((-1)*Y^2))*p157 - (((-1)*Y^2))*p160 - ((1))*p162 - ((1))*p185 - (((1*W^2)/(X*Z)))*p188 - ((((-1)*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)) + ((-1)*Y^2))*p237 - ((1))*p243 - ((1))*p244 - (((1*Z)/(X)))*p245 - ((((-1))/(X)) + (1))*p247 - ((1) + ((-1)*X))*p249 - ((((-1))/(X)) + (((-1)*Z)/(X)))*p252 - (((-1)*Y^2))*p253 - ((1) + ((-1)*X))*p261 - (((-1)*Y^2))*p264 - (((-1)*Y^2))*p270 - (((-1)*Y^2) + (1*X))*p272 - (((-1)*Y^2))*p277 - (((-1)*Y^2))*p278 - (((-1)*Y^2))*p290 - (((1*Y^2)/(X)))*p291 - ((((-2)*X^2)/(Z)) + (((-1)*X^2*Y*a)/(Z)) + (((-1)*X^2*Y^2)/(Z)) + (((-2)*X^3)/(Z)) + (((-1)*X^3*Y*a)/(Z)) + (((-1)*X^4)/(Z)))*p295 - (((-1)*Y^2))*p299 - (((-1)*Y^2))*p303 - (((-1)*Y^2))*p306 - (((-1)*Y^2))*p307 - (((1*Y^2)/(X)))*p308 - ((1*Y^2))*p312

theorem residual_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X^2*Z)) + (((-2)*Y*a)/(X^2*Z)) + (((-4)*Y^2)/(X^2*Z)) + ((2*Y^3*a)/(X^2*Z)) + ((6*Y^4)/(X^2*Z)) + (((-2))/(X*Z)) + (((-2)*Y*a)/(X*Z)) + (((-2)*Y^2)/(X*Z)) + (((-4)*Y^4)/(X*Z)) + (((-8))/(Z)) + ((-2)) + (((-4)*Y*a)/(Z)) + ((2*Y^2)/(Z)) + (((-2)*Y^3*a)/(Z)) + (((-2)*Y^4)/(Z)) + (((-4)*X)/(Z)) + ((2*X*Y*a)/(Z)) + (((-2)*X*Y^2)/(Z)))*v 520 + (((2)/(X^2*Y^2)) + ((6)/(X^2)) + (((-2)*a^2)/(X^2)) + (((-6)*Y*a)/(X^2)) + ((4)/(X*Y^2)) + ((2*a)/(X*Y)) + ((8)/(X)) + (((-2)*a^2)/(X)) + (((-2)*Y*a)/(X)) + ((8)/(Y^2)) + (4) + ((4*X)/(Y^2)) + ((4*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 315
  change ((1))*v 20 + (((-1)))*v 40 + ((1))*v 80 + (((-1)))*v 100 + ((1))*v 120 + (((-1)))*v 160 + ((1))*v 200 + (((-1)))*v 220 + ((1))*v 260 + (((-1)))*v 280 + ((1))*v 320 + (((-1)))*v 340 + ((1))*v 380 + (((-1)))*v 400 + ((1))*v 440 + (((-1)))*v 460 + ((1))*v 500 + (((-1)))*v 520 + ((1))*v 560 + (((-1)))*v 580 + ((1))*v 620 + (((-1)))*v 660 + ((1))*v 680 + (((-1)))*v 700 + ((1))*v 740 + (((-1)))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((-1)))*p25 - ((1))*p28 - (((-1)))*p37 - ((1))*p43 - (((-1)))*p74 - (((-1)))*p90 - ((1))*p101 - ((1))*p154 - ((1))*p160 - (((-1)))*p187 - (((-1)))*p198 - ((1))*p237 - (((1)/(Y^2)) + (1))*p238 - (((-1)))*p246 - ((((-1)*X)/(Y^2)))*p248 - (((1*X)/(Y^2)))*p249 - (((2*X)/(Y^2)))*p261 - (((-1)))*p268 - ((1))*p270 - ((((-2)*X)/(Y^2)))*p272 - (((-1)))*p273 - ((1))*p278 - ((2))*p285 - (((1)/(X)) + (1))*p290 - ((((-1))/(X)) + ((-1)))*p291 - (((2*X^2)/(Y^2*Z)) + ((2*X^2*a)/(Y*Z)) + ((2*X^2)/(Z)) + ((4*X^3)/(Y^2*Z)) + ((2*X^3*a)/(Y*Z)) + ((2*X^3)/(Z)) + ((2*X^4)/(Y^2*Z)))*p295 - (((-1)))*p297 - ((1))*p300 - (((-1)))*p301 - ((1))*p302 - ((2))*p303 - (((-2)))*p308

theorem residual_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2)/(X^2*Z)) + ((2*Y*a)/(X^2*Z)) + ((4*Y^2)/(X^2*Z)) + (((-2)*Y^3*a)/(X^2*Z)) + (((-6)*Y^4)/(X^2*Z)) + ((2)/(X*Z)) + ((2*Y*a)/(X*Z)) + ((2*Y^2)/(X*Z)) + ((4*Y^4)/(X*Z)) + ((8)/(Z)) + (2) + ((4*Y*a)/(Z)) + (((-2)*Y^2)/(Z)) + ((2*Y^3*a)/(Z)) + ((2*Y^4)/(Z)) + ((4*X)/(Z)) + (((-2)*X*Y*a)/(Z)) + ((2*X*Y^2)/(Z)))*v 520 + ((((-2))/(X^2*Y^2)) + (((-6))/(X^2)) + ((2*a^2)/(X^2)) + ((6*Y*a)/(X^2)) + (((-4))/(X*Y^2)) + (((-2)*a)/(X*Y)) + (((-8))/(X)) + ((2*a^2)/(X)) + ((2*Y*a)/(X)) + (((-8))/(Y^2)) + ((-4)) + (((-4)*X)/(Y^2)) + (((-4)*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 316
  change (((-1)))*v 20 + ((1))*v 40 + (((-1)))*v 80 + ((1))*v 100 + (((-1)))*v 120 + ((1))*v 160 + (((-1)))*v 200 + ((1))*v 220 + (((-1)))*v 260 + ((1))*v 280 + (((-1)))*v 320 + ((1))*v 340 + (((-1)))*v 380 + ((1))*v 400 + (((-1)))*v 440 + ((1))*v 460 + (((-1)))*v 500 + ((1))*v 520 + (((-1)))*v 560 + ((1))*v 580 + (((-1)))*v 620 + ((1))*v 660 + (((-1)))*v 680 + ((1))*v 700 + (((-1)))*v 740 + ((1))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p25 - (((-1)))*p28 - ((1))*p37 - (((-1)))*p43 - ((1))*p74 - ((1))*p90 - (((-1)))*p101 - (((-1)))*p154 - (((-1)))*p160 - ((1))*p187 - ((1))*p198 - (((-1)))*p237 - ((((-1))/(Y^2)) + ((-1)))*p238 - ((1))*p246 - (((1*X)/(Y^2)))*p248 - ((((-1)*X)/(Y^2)))*p249 - ((((-2)*X)/(Y^2)))*p261 - ((1))*p268 - (((-1)))*p270 - (((2*X)/(Y^2)))*p272 - ((1))*p273 - (((-1)))*p278 - (((-2)))*p285 - ((((-1))/(X)) + ((-1)))*p290 - (((1)/(X)) + (1))*p291 - ((((-2)*X^2)/(Y^2*Z)) + (((-2)*X^2*a)/(Y*Z)) + (((-2)*X^2)/(Z)) + (((-4)*X^3)/(Y^2*Z)) + (((-2)*X^3*a)/(Y*Z)) + (((-2)*X^3)/(Z)) + (((-2)*X^4)/(Y^2*Z)))*p295 - ((1))*p297 - (((-1)))*p300 - ((1))*p301 - (((-1)))*p302 - (((-2)))*p303 - ((2))*p308

theorem residual_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((4*Y^2)/(X^3*Z)) + (((-4)*Y^4)/(X^3*Z)) + ((2)/(X^2*Z)) + ((2*Y*a)/(X^2*Z)) + (((-2)*Y^3*a)/(X^2*Z)) + ((2*Y^4)/(X^2*Z)) + ((6)/(X*Z)) + ((2)/(X)) + ((4*Y*a)/(X*Z)) + (((-2)*Y^2)/(X*Z)) + ((2*Y^3*a)/(X*Z)) + ((2*Y^4)/(X*Z)) + ((6)/(Z)) + (((-2)*Y*a)/(Z)) + ((2*Y^2)/(Z)))*v 520 + ((((-4))/(X^3)) + ((4*Y*a)/(X^3)) + (((-2))/(X^2*Y^2)) + (((-6))/(X^2)) + ((2*a^2)/(X^2)) + ((2*Y*a)/(X^2)) + (((-8))/(X*Y^2)) + (((-4))/(X)) + (((-4))/(Y^2)) + (((-4)*X)/(Y^2)))*v 540=0 := by
  have h:=hv 317
  change ((1))*v 10 + (((-1)))*v 20 + ((1))*v 40 + (((-1)))*v 50 + ((1))*v 60 + (((-1)))*v 80 + ((1))*v 100 + (((-1)))*v 110 + ((1))*v 130 + (((-1)))*v 140 + ((1))*v 160 + (((-1)))*v 170 + ((1))*v 190 + (((-1)))*v 200 + ((1))*v 220 + (((-1)))*v 230 + ((1))*v 250 + (((-1)))*v 260 + ((1))*v 280 + (((-1)))*v 290 + ((1))*v 310 + (((-1)))*v 330 + ((1))*v 340 + (((-1)))*v 350 + ((1))*v 370 + (((-1)))*v 380 + ((1))*v 400 + (((-1)))*v 410 + ((1))*v 430 + (((-1)))*v 440 + ((1))*v 450 + (((-1)))*v 470 + ((1))*v 490 + (((-1)))*v 500 + ((1))*v 520 + (((-1)))*v 530 + ((1))*v 550 + (((-1)))*v 560 + ((1))*v 580 + (((-1)))*v 590 + ((1))*v 610 + (((-1)))*v 620 + ((1))*v 640 + (((-1)))*v 650 + ((1))*v 670 + (((-1)))*v 680 + ((1))*v 700 + (((-1)))*v 720 + ((1))*v 730 + (((-1)))*v 740 + ((1))*v 760 + (((-1)))*v 770=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p8 - (((-1)))*p11 - ((1))*p25 - (((-1)))*p28 - ((1))*p29 - (((-1)))*p30 - ((1))*p37 - (((-1)))*p43 - ((1))*p74 - (((-1)))*p76 - ((1))*p86 - (((-1)))*p89 - ((1))*p99 - (((-1)))*p101 - ((((-1)*W^2)/(X*Y^2*Z)))*p148 - (((-1)))*p151 - (((-1)))*p153 - (((-1)))*p154 - ((1))*p155 - (((-1)))*p160 - (((-1)))*p162 - ((1))*p165 - ((1))*p177 - ((1))*p187 - (((1*W^2)/(X*Y^2*Z)))*p188 - ((1))*p198 - (((-1)))*p237 - ((((-1))/(X*Y^2)) + (((-1))/(X)) + (((-1))/(Y^2)))*p238 - (((-1)))*p239 - ((1))*p240 - (((1*Z)/(X*Y^2)))*p245 - ((1))*p246 - (((1*X)/(Y^2)))*p248 - ((((-1)*X)/(Y^2)))*p249 - ((((-2)*Z)/(X*Y^2)))*p252 - (((-1)))*p253 - ((1))*p254 - ((((-2)*X)/(Y^2)))*p261 - (((-1)))*p264 - ((1))*p265 - (((-2)) + ((2*X)/(Y^2)))*p272 - ((1))*p273 - ((1))*p276 - (((-1)))*p277 - (((-1)))*p278 - ((((-1))/(X)) + ((-1)))*p290 - (((1)/(X)) + (1))*p291 - ((((-4)*X^2)/(Y^2*Z)) + (((-2)*X^2*a)/(Y*Z)) + (((-2)*X^2)/(Z)) + (((-4)*X^3)/(Y^2*Z)) + (((-2)*X^3*a)/(Y*Z)) + (((-2)*X^4)/(Y^2*Z)))*p295 - ((1))*p297 - ((1))*p298 - (((-1)))*p299 - ((((-1))/(X)))*p302 - (((-2)))*p303 - ((1))*p305 - (((-1)))*p306 - (((-1)))*p307 - (((2)/(X)))*p308 - ((2))*p312

theorem residual_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-4)*Y^2)/(X^3*Z)) + ((4*Y^4)/(X^3*Z)) + (((-2))/(X^2*Z)) + (((-2)*Y*a)/(X^2*Z)) + ((2*Y^3*a)/(X^2*Z)) + (((-2)*Y^4)/(X^2*Z)) + (((-6))/(X*Z)) + (((-2))/(X)) + (((-4)*Y*a)/(X*Z)) + ((2*Y^2)/(X*Z)) + (((-2)*Y^3*a)/(X*Z)) + (((-2)*Y^4)/(X*Z)) + (((-6))/(Z)) + ((2*Y*a)/(Z)) + (((-2)*Y^2)/(Z)))*v 520 + (((4)/(X^3)) + (((-4)*Y*a)/(X^3)) + ((2)/(X^2*Y^2)) + ((6)/(X^2)) + (((-2)*a^2)/(X^2)) + (((-2)*Y*a)/(X^2)) + ((8)/(X*Y^2)) + ((4)/(X)) + ((4)/(Y^2)) + ((4*X)/(Y^2)))*v 540=0 := by
  have h:=hv 318
  change (((-1)))*v 10 + ((1))*v 20 + (((-1)))*v 40 + ((1))*v 50 + (((-1)))*v 60 + ((1))*v 80 + (((-1)))*v 100 + ((1))*v 110 + (((-1)))*v 130 + ((1))*v 140 + (((-1)))*v 160 + ((1))*v 170 + (((-1)))*v 190 + ((1))*v 200 + (((-1)))*v 220 + ((1))*v 230 + (((-1)))*v 250 + ((1))*v 260 + (((-1)))*v 280 + ((1))*v 290 + (((-1)))*v 310 + ((1))*v 330 + (((-1)))*v 340 + ((1))*v 350 + (((-1)))*v 370 + ((1))*v 380 + (((-1)))*v 400 + ((1))*v 410 + (((-1)))*v 430 + ((1))*v 440 + (((-1)))*v 450 + ((1))*v 470 + (((-1)))*v 490 + ((1))*v 500 + (((-1)))*v 520 + ((1))*v 530 + (((-1)))*v 550 + ((1))*v 560 + (((-1)))*v 580 + ((1))*v 590 + (((-1)))*v 610 + ((1))*v 620 + (((-1)))*v 640 + ((1))*v 650 + (((-1)))*v 670 + ((1))*v 680 + (((-1)))*v 700 + ((1))*v 720 + (((-1)))*v 730 + ((1))*v 740 + (((-1)))*v 760 + ((1))*v 770=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((-1)))*p8 - ((1))*p11 - (((-1)))*p25 - ((1))*p28 - (((-1)))*p29 - ((1))*p30 - (((-1)))*p37 - ((1))*p43 - (((-1)))*p74 - ((1))*p76 - (((-1)))*p86 - ((1))*p89 - (((-1)))*p99 - ((1))*p101 - (((1*W^2)/(X*Y^2*Z)))*p148 - ((1))*p151 - ((1))*p153 - ((1))*p154 - (((-1)))*p155 - ((1))*p160 - ((1))*p162 - (((-1)))*p165 - (((-1)))*p177 - (((-1)))*p187 - ((((-1)*W^2)/(X*Y^2*Z)))*p188 - (((-1)))*p198 - ((1))*p237 - (((1)/(X*Y^2)) + ((1)/(X)) + ((1)/(Y^2)))*p238 - ((1))*p239 - (((-1)))*p240 - ((((-1)*Z)/(X*Y^2)))*p245 - (((-1)))*p246 - ((((-1)*X)/(Y^2)))*p248 - (((1*X)/(Y^2)))*p249 - (((2*Z)/(X*Y^2)))*p252 - ((1))*p253 - (((-1)))*p254 - (((2*X)/(Y^2)))*p261 - ((1))*p264 - (((-1)))*p265 - ((2) + (((-2)*X)/(Y^2)))*p272 - (((-1)))*p273 - (((-1)))*p276 - ((1))*p277 - ((1))*p278 - (((1)/(X)) + (1))*p290 - ((((-1))/(X)) + ((-1)))*p291 - (((4*X^2)/(Y^2*Z)) + ((2*X^2*a)/(Y*Z)) + ((2*X^2)/(Z)) + ((4*X^3)/(Y^2*Z)) + ((2*X^3*a)/(Y*Z)) + ((2*X^4)/(Y^2*Z)))*p295 - (((-1)))*p297 - (((-1)))*p298 - ((1))*p299 - (((1)/(X)))*p302 - ((2))*p303 - (((-1)))*p305 - ((1))*p306 - ((1))*p307 - ((((-2))/(X)))*p308 - (((-2)))*p312

#print axioms residual_31

theorem residual_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^4)) + (((-1)*Y*a)/(X^4)) + ((1*Y^3*a)/(X^4)) + ((1*Y^4)/(X^4)) + (((-1)*Y^2)/(X^3)) + (((-1)*Y^3*a)/(X^3)) + (((-1)*Y^4)/(X^3)) + (((-1))/(X^2)) + ((1)/(X)))*v 520 + (((1*Z)/(X^4*Y^2)) + ((1*Z)/(X^4)) + (((-1)*Z*a^2)/(X^4)) + (((-1)*Y*Z*a)/(X^4)) + ((1*Z)/(X^3*Y^2)) + ((1*Z*a)/(X^3*Y)) + ((1*Z)/(X^3)))*v 540=0 := by
  have h:=hv 356
  change (((1)/(Y^2)) + (1))*v 195 + ((1))*v 455 + ((((-1)*a)/(Y)))*v 585 + ((1))*v 715=0 at h
  have p19:=pivot_19 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p19 - ((((-1)*a)/(Y)))*p85 - ((1))*p193 - (((1*Z*a)/(X^3*Y)))*p238 - ((((-1)*Z)/(X^2*Y^2)))*p243 - (((1*Z)/(X^2*Y^2)))*p252 - (((1)/(Y^2)) + ((1*a)/(Y)) + (1))*p295

theorem residual_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + ((1*X)/(Z)))*v 520 + (((1)/(X^2*Y^2)) + ((1)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X*Y^2)) + ((1*a)/(X*Y)) + ((1)/(X)))*v 540=0 := by
  have h:=hv 359
  change ((1))*v 240 + ((1))*v 500 + (((1)/(Y^2)))*v 600 + ((((-1)*a)/(Y)))*v 720 + ((1))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p25 - ((((-1)*a)/(Y)))*p30 - ((1))*p247 - (((1)/(Y^2)))*p252 - ((1))*p278 - ((((-1))/(X)))*p291 - (((1*X^2)/(Y^2*Z)) + ((1*X^2*a)/(Y*Z)))*p295 - (((-1)))*p301

theorem residual_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)) + ((1*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((2)/(W^2)) + ((1*b)/(W)) + (1) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)))*v 520 + (((2*Z)/(X^2*Y^2*W^2)) + (((-2)*Z*a)/(X^2*Y*W^2)) + (((-1)*Z)/(X*Y^2*W^2)) + ((1*Z*a)/(X*Y*W^2)) + ((1*Z)/(X*W^2)) + (((-2)*Z)/(W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((1*X*Z*a)/(Y*W^2)) + ((1*X*Z)/(W^2)))*v 540=0 := by
  have h:=hv 360
  change ((1))*v 26 + ((((-1)*b)/(W)))*v 130 + ((1))*v 182 + ((1))*v 338 + ((1))*v 494 + (((1)/(W^2)) + (1))*v 650=0 at h
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p260:=pivot_260 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p71 - ((((-1)*b)/(W)))*p86 - (((1)/(W^2)) + (1))*p89 - ((((-1)*Z)/(X*Y^2*W^2)))*p90 - ((1))*p242 - ((((-1)*Z)/(X*Y^2*W^2)) + (((-1)*Z)/(X*Y^2)))*p245 - (((1*Z)/(X*Y^2*W^2)) + ((1*Z*b)/(X*Y^2*W)) + ((1*Z)/(X*Y^2)))*p252 - ((1))*p260 - ((1))*p282 - (((1*Y^2*Z)/(X*W^2)))*p285 - ((((-1))/(X)))*p294 - (((1*X^2)/(Y^2*W^2)) + (((-1)*X^3)/(Y^2*W^2)))*p295 - ((((-1)*Z)/(X*W^2)))*p303 - (((-1)))*p304

theorem residual_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^4)/(X^5*W^2)) + (((-2)*Y^6)/(X^5*W^2)) + (((-1)*Y^2)/(X^4*W^2)) + ((1*Y^2*b)/(X^4*W)) + (((-1)*Y^2)/(X^4)) + ((1*Y^4)/(X^4*W^2)) + (((-1)*Y^4*b)/(X^4*W)) + ((1*Y^4)/(X^4)) + ((2*Y^6)/(X^4*W^2)) + ((2*Y^3*a)/(X^3*W^2)) + (((-1)*Y^4)/(X^3*W^2)) + ((1*Y^4*b)/(X^3*W)) + (((-1)*Y^4)/(X^3)) + ((1*Y^2)/(X^2*W^2)) + (((-2)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)))*v 520 + ((((-2)*Y^2*Z)/(X^5*W^2)) + ((2*Y^3*Z*a)/(X^5*W^2)) + ((1*Z)/(X^4*W^2)) + (((-1)*Z*b)/(X^4*W)) + ((1*Z)/(X^4)) + (((-1)*Y*Z*a)/(X^4*W^2)) + ((1*Y*Z*a*b)/(X^4*W)) + (((-1)*Y*Z*a)/(X^4)) + (((-2)*Y^2*Z)/(X^4*W^2)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Z*b)/(X^3*W)) + ((1*Z)/(X^3)) + ((1*Z)/(X^2*W^2)) + ((1*Z)/(W^2)))*v 540=0 := by
  have h:=hv 361
  change ((1))*v 39 + (((1)/(W^2)) + (((-1)*b)/(W)) + (1))*v 195 + ((1))*v 351 + ((1))*v 507 + ((1))*v 663=0 at h
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p73 - ((1))*p91 - ((1))*p200 - ((1))*p231 - (((1*Y^2)/(X^3*W^2)))*p237 - ((((-1)*Z)/(X^3*W^2)))*p245 - (((1*Z)/(X^3*W^2)))*p252 - ((((-1)*Y^2*Z)/(X^2*W^2)))*p277 - (((1*Y^2*Z)/(X^2*W^2)))*p285 - (((1)/(W^2)) + (((-1)*b)/(W)) + (1))*p295 - ((((-1)*Y^2*Z)/(X^3*W^2)))*p302 - (((2*Y^2*Z)/(X^3*W^2)))*p308

theorem residual_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((2)/(W^2)) + ((1*b)/(W)) + (1) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)))*v 520 + ((((-2)*Z)/(X*Y^2*W^2)) + ((2*Z*a)/(X*Y*W^2)) + (((-1)*Z)/(Y^2*W^2)) + ((1*Z*a)/(Y*W^2)) + (((-1)*Z)/(W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((1*X*Z*a)/(Y*W^2)) + ((1*X*Z)/(W^2)))*v 540=0 := by
  have h:=hv 362
  change ((1))*v 52 + ((1))*v 208 + ((((-1)*b)/(W)))*v 260 + ((1))*v 364 + (((1)/(W^2)) + (1))*v 520 + ((1))*v 676=0 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p296:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p55 - ((1))*p77 - ((((-1)*X*Z)/(Y^2*W^2)))*p162 - ((((-1)*b)/(W)))*p237 - ((((-1)*Z)/(Y^2*W^2)))*p238 - ((1))*p294 - ((((-1)*X^3)/(Y^2*W^2)))*p295 - ((1))*p296 - (((-1)))*p304

theorem residual_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + ((-1)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 520 + (((2*Z)/(X*Y^2*W^2)) + (((-2)*Z*a)/(X*Y*W^2)) + ((1*Z)/(Y^2*W^2)) + (((-1)*Z*a)/(Y*W^2)) + ((1*Z)/(W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + (((-1)*X*Z)/(W^2)))*v 540=0 := by
  have h:=hv 363
  change ((1))*v 104 + (((1)/(W^2)) + (1))*v 260 + ((1))*v 416 + ((((-1)*b)/(W)))*v 520 + ((1))*v 572 + ((1))*v 728=0 at h
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p47 - ((1))*p98 - ((((-1)*X*Z)/(Y^2*W^2)))*p155 - (((1)/(W^2)) + (1))*p237 - ((1))*p274 - (((-1)*X))*p286 - (((1*X^3)/(Y^2*W^2)) + ((1*X^4)/(Y^2*W^2)))*p295 - ((1))*p304

theorem residual_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^4)/(X^5*W^2)) + ((2*Y^6)/(X^5*W^2)) + ((1*Y^2)/(X^4*W^2)) + (((-1)*Y^2*b)/(X^4*W)) + ((1*Y^2)/(X^4)) + (((-1)*Y^4)/(X^4*W^2)) + ((1*Y^4*b)/(X^4*W)) + (((-1)*Y^4)/(X^4)) + (((-2)*Y^6)/(X^4*W^2)) + (((-2)*Y^3*a)/(X^3*W^2)) + ((1*Y^4)/(X^3*W^2)) + (((-1)*Y^4*b)/(X^3*W)) + ((1*Y^4)/(X^3)) + (((-1)*Y^2)/(X^2*W^2)) + ((2*Y^3*a)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)))*v 520 + (((2*Y^2*Z)/(X^5*W^2)) + (((-2)*Y^3*Z*a)/(X^5*W^2)) + (((-1)*Z)/(X^4*W^2)) + ((1*Z*b)/(X^4*W)) + (((-1)*Z)/(X^4)) + ((1*Y*Z*a)/(X^4*W^2)) + (((-1)*Y*Z*a*b)/(X^4*W)) + ((1*Y*Z*a)/(X^4)) + ((2*Y^2*Z)/(X^4*W^2)) + ((1*Z)/(X^3*W^2)) + ((1*Z*b)/(X^3*W)) + (((-1)*Z)/(X^3)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Z)/(W^2)))*v 540=0 := by
  have h:=hv 364
  change ((1))*v 117 + ((1))*v 273 + ((1))*v 429 + (((1)/(W^2)) + (((-1)*b)/(W)) + (1))*v 585 + ((1))*v 741=0 at h
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p176:=pivot_176 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p84 - (((1)/(W^2)) + (((-1)*b)/(W)) + (1))*p85 - ((1))*p102 - ((1))*p176 - ((1))*p230 - ((((-1)*Z)/(X^3*W^2)) + ((1*Z*b)/(X^3*W)) + (((-1)*Z)/(X^3)))*p238 - ((((-1)*Z)/(X^3*W^2)))*p252 - ((((-1)*Y^2*Z)/(X^2*W^2)))*p276 - ((((-1)*Y^2*Z)/(X^2*W^2)))*p285 - ((((-1))/(W^2)) + ((1*b)/(W)) + ((-1)))*p295 - (((1*Y^2*Z)/(X^3*W^2)))*p302 - ((((-2)*Y^2*Z)/(X^3*W^2)))*p308

theorem residual_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + (((-1)*Y*a)/(X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + ((-1)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 520 + ((((-2)*Z)/(X^2*Y^2*W^2)) + ((2*Z*a)/(X^2*Y*W^2)) + ((1*Z)/(X*Y^2*W^2)) + (((-1)*Z*a)/(X*Y*W^2)) + (((-1)*Z)/(X*W^2)) + ((2*Z)/(W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + (((-1)*X*Z)/(W^2)))*v 540=0 := by
  have h:=hv 365
  change (((1)/(W^2)) + (1))*v 130 + ((1))*v 286 + ((1))*v 442 + ((1))*v 598 + ((((-1)*b)/(W)))*v 650 + ((1))*v 754=0 at h
  have p61:=pivot_61 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p296:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p61 - (((1)/(W^2)) + (1))*p86 - ((((-1)*b)/(W)))*p89 - ((((-1)*Z)/(X*Y^2*W^2)))*p238 - ((1))*p241 - (((1*Z*b)/(X*Y^2*W)))*p245 - ((((-1)*Z)/(X*Y^2*W^2)) + (((-1)*Z*b)/(X*Y^2*W)) + (((-1)*Z)/(X*Y^2)))*p252 - ((1))*p259 - ((((-1)*Y^2*Z)/(X*W^2)))*p285 - ((1))*p286 - ((((-1)*X^2)/(Y^2*W^2)))*p295 - (((-1)))*p296 - ((((-1)*Z)/(X*W^2)))*p297 - (((1*Z)/(X*W^2)))*p303 - ((1))*p304

#print axioms residual_47

theorem residual_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^3*Z)) + (((-2)*Y^4)/(X^3*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((4*Y^4)/(X^2*Z)) + ((2)/(X*Z)) + ((1)/(X)) + ((1*Y*a)/(X*Z)) + (((-2)*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + ((-1)) + (((-3)*Y*a)/(Z)) + ((2*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + ((((-2))/(X^3)) + ((2*Y*a)/(X^3)) + (((-2)*Y*a)/(X^2)) + (((-2))/(X*Y^2)) + ((1*a)/(X*Y)) + ((2)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((2)/(Y^2)) + (2) + ((2*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 366
  change ((1))*v 10 + ((1))*v 70 + ((((-1))/(Z)) + (1))*v 130 + ((1))*v 190 + ((1))*v 250 + ((1))*v 310 + ((1))*v 370 + ((1))*v 430 + ((1))*v 490 + ((1))*v 550 + ((1))*v 610 + ((1))*v 670 + ((1))*v 730=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p8 - ((((-1))/(Z)) + (1))*p86 - ((1))*p99 - ((((-1)*W^2)/(X*Y^2*Z)))*p148 - ((1))*p165 - ((1))*p177 - ((1))*p192 - ((1))*p240 - (((1)/(X*Y^2)))*p245 - (((1)/(X*Y^2)))*p247 - ((((-1)*Z)/(X*Y^2)))*p252 - ((1))*p254 - (((-1)))*p272 - ((1))*p276 - ((1))*p285 - ((((-1)*X^2)/(Y^2*Z)) + ((1*X^3)/(Z)))*p295 - ((1))*p298 - ((1))*p300 - ((((-1))/(X)))*p302 - ((1))*p305 - (((1)/(X)) + ((-1)))*p308 - ((1))*p312

theorem residual_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((3*Y^4)/(X^2*Z)) + (((-1))/(X*Z)) + (((-1)*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-2)*Y^4)/(X*Z)) + (((-4))/(Z)) + ((-1)) + (((-2)*Y*a)/(Z)) + ((1*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + (((1)/(X^2*Y^2)) + ((3)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-3)*Y*a)/(X^2)) + ((2)/(X*Y^2)) + ((1*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((4)/(Y^2)) + (2) + ((2*X)/(Y^2)) + ((2*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 367
  change ((1))*v 20 + ((1))*v 80 + ((1))*v 140 + ((1))*v 200 + ((((-1))/(Z)) + (1))*v 260 + ((1))*v 320 + ((1))*v 380 + ((1))*v 440 + ((1))*v 500 + ((1))*v 560 + ((1))*v 620 + ((1))*v 680 + ((1))*v 740=0 at h
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p28 - ((1))*p43 - ((1))*p101 - ((1))*p154 - ((1))*p160 - ((((-1))/(Z)) + (1))*p237 - (((1)/(Y^2)))*p238 - (((1*X)/(Y^2)))*p249 - (((1*X)/(Y^2)))*p261 - ((1))*p264 - ((1))*p270 - ((((-1)*X)/(Y^2)))*p272 - ((1))*p278 - ((1))*p285 - ((1))*p290 - ((((-1))/(X)))*p291 - (((1*X^2)/(Y^2*Z)) + ((1*X^2*a)/(Y*Z)) + ((1*X^2)/(Z)) + ((2*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)) + ((1*X^3)/(Z)) + ((1*X^4)/(Y^2*Z)))*p295 - (((-1)))*p301 - ((1))*p302 - ((1))*p303 - (((-1)))*p308

theorem residual_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + ((2*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-3)*Y^4)/(X^2*Z)) + ((1)/(X*Z)) + ((1*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + ((2*Y^4)/(X*Z)) + ((4)/(Z)) + (1) + ((2*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + ((1*Y^4)/(Z)) + ((2*X)/(Z)) + (((-1)*X*Y*a)/(Z)) + ((1*X*Y^2)/(Z)))*v 520 + ((((-1))/(X^2*Y^2)) + (((-3))/(X^2)) + ((1*a^2)/(X^2)) + ((3*Y*a)/(X^2)) + (((-2))/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-4))/(X)) + ((1*a^2)/(X)) + ((1*Y*a)/(X)) + (((-4))/(Y^2)) + ((-2)) + (((-2)*X)/(Y^2)) + (((-2)*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 368
  change ((1))*v 40 + ((1))*v 100 + ((1))*v 160 + ((1))*v 220 + ((1))*v 280 + ((1))*v 340 + ((1))*v 400 + ((1))*v 460 + ((((-1))/(Z)) + (1))*v 520 + ((1))*v 580 + ((1))*v 640 + ((1))*v 700 + ((1))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p25 - ((1))*p37 - ((1))*p74 - ((1))*p187 - ((1))*p198 - ((1))*p246 - (((1*X)/(Y^2)))*p248 - ((((-1)*X)/(Y^2)))*p261 - ((1))*p265 - ((1))*p268 - (((1*X)/(Y^2)))*p272 - ((1))*p273 - (((-1)))*p285 - ((((-1))/(X)))*p290 - ((1))*p291 - ((((-1)*X^2)/(Y^2*Z)) + (((-1)*X^2*a)/(Y*Z)) + (((-1)*X^2)/(Z)) + (((-2)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)) + (((-1)*X^3)/(Z)) + (((-1)*X^4)/(Y^2*Z)))*p295 - ((1))*p297 - (((-1)))*p300 - (((-1)))*p303 - ((1))*p308

theorem residual_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X^3*Z)) + ((2*Y^4)/(X^3*Z)) + ((2*Y^2)/(X^2*Z)) + (((-4)*Y^4)/(X^2*Z)) + (((-2))/(X*Z)) + (((-1))/(X)) + (((-1)*Y*a)/(X*Z)) + ((2*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((1)/(Z)) + (1) + ((3*Y*a)/(Z)) + (((-2)*Y^2)/(Z)) + ((1*Y^3*a)/(Z)) + ((1*Y^4)/(Z)) + ((2*X)/(Z)) + (((-1)*X*Y*a)/(Z)) + ((1*X*Y^2)/(Z)))*v 520 + (((2)/(X^3)) + (((-2)*Y*a)/(X^3)) + ((2*Y*a)/(X^2)) + ((2)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-2))/(X)) + ((1*a^2)/(X)) + ((1*Y*a)/(X)) + (((-2))/(Y^2)) + ((-2)) + (((-2)*X^2)/(Y^2)))*v 540=0 := by
  have h:=hv 369
  change ((1))*v 50 + ((1))*v 110 + ((1))*v 170 + ((1))*v 230 + ((1))*v 290 + ((1))*v 350 + ((1))*v 410 + ((1))*v 470 + ((1))*v 530 + ((1))*v 590 + ((((-1))/(Z)) + (1))*v 650 + ((1))*v 710 + ((1))*v 770=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p11 - ((1))*p76 - ((((-1))/(Z)) + (1))*p89 - ((1))*p151 - ((1))*p153 - ((1))*p157 - ((((-1)*W^2)/(X*Y^2*Z)))*p188 - (((1)/(X*Y^2)))*p238 - ((1))*p239 - (((1)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)))*p245 - (((1)/(X*Y^2)))*p247 - (((1*Z)/(X*Y^2)))*p252 - ((1))*p253 - ((1))*p272 - ((1))*p277 - (((-1)))*p285 - (((1*X^2)/(Y^2*Z)) + (((-1)*X^3)/(Z)))*p295 - ((1))*p299 - ((1))*p301 - (((-1)))*p302 - ((1))*p306 - ((1))*p307 - ((((-1))/(X)) + (1))*p308 - (((-1)))*p312

#print axioms residual_51

end SmallLevelTwentySixUnitMMP
