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

theorem residual_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*b)/(W)) + (2) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(W)) + (((-1)*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-7)*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-5)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-17)*X^4)/(2*W^2)) + ((3*X^4*Z)/(2*W^2)) + (((-2)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 545
  change ((1))*v 24 + ((1))*v 54 + ((1))*v 84 + ((1))*v 114 + ((1))*v 144 + ((1))*v 174 + ((1))*v 204 + ((1))*v 234 + ((1))*v 264 + ((1))*v 294 + ((1))*v 324 + ((1))*v 354 + ((1))*v 384 + (((1)/(Z)))*v 408 + ((1))*v 414 + ((1))*v 444 + ((1))*v 474 + ((1))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p47 - ((1))*p104 - ((1))*p109 - (((1)/(Z)))*p120 - ((1))*p126 - ((1))*p152 - ((1))*p158 - ((1))*p165 - ((((-1)*X)/(W^2)))*p194 - (((1*X)/(W^2)))*p198 - (((1*X)/(W^2)))*p202 - ((1))*p220 - ((1))*p224 - ((((-1)*Z)/(W^2)))*p230 - (((1*X)/(W^2)))*p236 - ((((-1)*Y^2)/(W^2)))*p256 - (((1*X)/(W^2)))*p257 - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p267 - (((-1)*X))*p274 - ((1))*p288 - ((1))*p293 - (((-1)*X))*p313 - ((1))*p339 - ((1))*p342 - ((((-1))/(X)))*p353 - ((((-1))/(X)))*p354 - (((-1)*X))*p355 - ((1))*p357 - ((((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*p358

#print axioms residual_120

end SmallLevelThirtyFourUnitMMM
