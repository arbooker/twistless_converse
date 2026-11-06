module
public meta import Lean.Elab.Command
public import SmallLevelThirtyFourSparseResidualEightV4

public meta section
open Lean Elab Command
/-- Check each ordinary elimination proof synchronously, without retaining
editor information for the large generated algebra expressions. -/
elab "compact_residual_elimination " proofDecl:command : command => do
  if let some source := proofDecl.raw.reprint then
    let output ← IO.getStderr
    output.putStrLn (source.splitOn "\n").head!
    output.flush
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) <|
    withEnableInfoTree false <| elabCommand proofDecl
end

set_option Elab.async false
set_option linter.unusedTactic false
set_option stderrAsMessages false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourUnitMMM
open Complex

compact_residual_elimination
theorem residual_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + (((-1))/(X^2*W^2)) + ((1)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-3)*X)/(2*W^2)) + ((3*X)/(2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-9)*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + ((15*X^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((19*X^3)/(2*W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  exact residual_8_sparse X Y Z W a b hX hY hZ hW v hv

compact_residual_elimination
theorem residual_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^3)) + ((1)/(X^2)) + ((1)/(X)) + (1))*v 370 + (((1*W^2)/(X^4*Y^2)) + (((-1))/(X^3*Y^2)) + ((1*W^2)/(X^3*Y^2)) + ((2)/(X^3)) + ((3)/(X^2*Y^2)) + (((-1)*W*b)/(X^2*Y^2)) + (((-2)*W^2)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + ((1*Y^2)/(X^2)) + (((-4))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((1*a)/(X*Y)) + (((-3))/(X)) + (((-3))/(Y^2)) + ((1*Z)/(Y^2)) + ((1*a)/(Y)) + ((-5)) + ((1*X)/(Y^2)) + ((-1)*X))*v 390 + ((((-1))/(2*X^3*Y^2)) + (((-1)*a)/(2*X^3*Y)) + (((-1)*Y*a)/(2*X^3)) + (((-1)*Y^2)/(2*X^3)) + (((-1)*a)/(2*X^2*Y)) + ((3)/(X^2)) + (((-1)*a^2)/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*W*b)/(X*Y^2)) + ((1*W^2)/(2*X*Y^2)) + (((-1)*Z)/(2*X*Y^2)) + ((1*W^2*a)/(2*X*Y)) + (((-1)*Z*a)/(2*X*Y)) + ((1)/(X)) + (((-1)*a^2)/(X)) + ((1*W^2)/(2*X)) + (((-1)*Z)/(2*X)) + ((2*Y^2)/(X)) + (((-3))/(2*Y^2)) + ((3*W^2)/(2*Y^2)) + ((2*a)/(Y)) + ((1*W^2*a)/(2*Y)) + (((-9))/(2)) + ((3*a^2)/(2)) + ((1*W^2)/(2)) + (1*Y*a) + (((-1)*Y^2*a^2)/(2)) + (((-1)*Y^3*a)/(2)) + ((15*X)/(2*Y^2)) + ((1*X*W^2)/(2*Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*W^2*a)/(2*Y)) + (((-9)*X)/(2)) + ((3*X*a^2)/(2)) + ((1*X*W^2)/(2)) + ((5*X*Y*a)/(2)) + (1*X*Y^2) + ((19*X^2)/(2*Y^2)) + (((-3)*X^2*Z)/(2*Y^2)) + ((5*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + ((3*X^2)/(2)) + (2*X^2*a^2) + (((-1)*X^2*Z)/(2)) + (3*X^2*Y*a) + (1*X^2*Y^2) + ((2*X^3)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2)) + ((3*X^3*a)/(2*Y)) + (((-1)*X^3*Z*a)/(2*Y)) + ((3*X^3)/(2)) + ((1*X^3*a^2)/(2)) + (((-1)*X^3*Z)/(2)) + (1*X^3*Y*a) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 231
  change (((1*W^2)/(X*Y^2)))*v 12 + (((1*W^2)/(X*Y^2)))*v 42 + ((1))*v 55 + (((1*W^2)/(X*Y^2)))*v 72 + ((1))*v 85 + (((1*W^2)/(X*Y^2)))*v 102 + ((1))*v 115 + (((1*W^2)/(X*Y^2)))*v 132 + ((1))*v 145 + (((1*W^2)/(X*Y^2)))*v 162 + ((1))*v 175 + (((1*W^2)/(X*Y^2)))*v 192 + ((1))*v 205 + (((1*W^2)/(X*Y^2)))*v 222 + ((1))*v 235 + (((1*W^2)/(X*Y^2)))*v 252 + ((1))*v 265 + (((1*W^2)/(X*Y^2)))*v 282 + ((1))*v 295 + (((1*W^2)/(X*Y^2)))*v 312 + ((1))*v 325 + (((1*W^2)/(X*Y^2)))*v 342 + ((1))*v 355 + (((1*W^2)/(X*Y^2)))*v 372 + ((1))*v 385 + (((1*W^2)/(X*Y^2)))*v 402 + ((1))*v 415 + (((1*W^2)/(X*Y^2)))*v 432 + ((1))*v 445 + (((1*W^2)/(X*Y^2)))*v 462 + ((1))*v 475 + ((1))*v 505=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p44:=pivot_44 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p149:=pivot_149 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p215:=pivot_215 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p250:=pivot_250 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p323:=pivot_323 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p11 - ((1))*p44 - (((1*W^2)/(X*Y^2)))*p45 - (((1*W^2)/(X*Y^2)))*p70 - ((1))*p82 - ((1))*p90 - ((1))*p101 - ((1))*p105 - ((1))*p111 - (((1*W^2)/(X*Y^2)))*p113 - (((1*W^2)/(X*Y^2)))*p124 - ((1))*p141 - ((1))*p149 - ((1))*p155 - (((1*W^2)/(X*Y^2)))*p170 - (((1)/(X*Y^2)))*p195 - ((1))*p215 - ((((-1))/(X*Y^2)))*p230 - (((1)/(X*Y^2)))*p232 - (((1)/(X*Y^2)))*p235 - ((1))*p250 - (((1*W^2)/(Y^2)))*p253 - ((1))*p255 - (((1*Y^2)/(X)))*p256 - ((((-1))/(Y^2)))*p257 - (((1*W^2)/(X*Y^2)))*p261 - (((1)/(X)))*p264 - (((2*W^2)/(X*Y^2)))*p268 - (((2*W^2)/(X*Y^2)))*p274 - (((-1)))*p277 - ((1))*p294 - (((2*W^2)/(X*Y^2)))*p299 - (((1*W^2)/(X*Y^2)))*p313 - ((1))*p323 - (((1*W^2)/(Y^2)))*p331 - (((2*W^2)/(X*Y^2)) + (((-1)*W^2)/(Y^2)))*p335 - (((1*W^2)/(X*Y^2)))*p336 - (((1*W^2)/(X*Y^2)))*p352 - (((1*W^2)/(X^3*Y^2)))*p354 - (((1*W^2)/(X*Y^2)))*p355 - (((1)/(X)) + (3))*p358 - ((1))*p359 - (((1*W^2)/(X*Y^2)))*p403 - (((1*W^2)/(X*Y^2)))*p404

#print axioms residual_9

compact_residual_elimination
theorem residual_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^3)) + ((1)/(X^2)) + ((1)/(X)) + (1))*v 370 + ((((-1)*W^2)/(X^4*Y^2)) + (((-4))/(X^3*Y^2)) + (((-1)*W^2)/(X^3*Y^2)) + ((1*Z)/(X^3*Y^2)) + ((1*a)/(X^3*Y)) + (((-4))/(X^3)) + (((-5))/(X^2*Y^2)) + ((1*W*b)/(X^2*Y^2)) + ((2*W^2)/(X^2*Y^2)) + ((1*Z)/(X^2*Y^2)) + ((2*a)/(X^2*Y)) + (((-3))/(X^2)) + (((-1)*Y^2)/(X^2)) + (((-1))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)) + (2))*v 390 + (((1)/(2*X^3*Y^2)) + ((1*a)/(2*X^3*Y)) + ((1*Y*a)/(2*X^3)) + ((1*Y^2)/(2*X^3)) + ((3)/(2*X^2*Y^2)) + ((3*a)/(2*X^2*Y)) + (((-4))/(X^2)) + ((1*a^2)/(X^2)) + ((3*Y*a)/(2*X^2)) + ((1*Y^2)/(2*X^2)) + ((8)/(X*Y^2)) + ((1*W*b)/(X*Y^2)) + (((-1)*W^2)/(2*X*Y^2)) + (((-1)*Z)/(2*X*Y^2)) + ((1*a)/(X*Y)) + (((-1)*W^2*a)/(2*X*Y)) + ((1*Z*a)/(2*X*Y)) + (((-2))/(X)) + ((2*a^2)/(X)) + (((-1)*W^2)/(2*X)) + ((1*Z)/(2*X)) + ((2*Y*a)/(X)) + (((-1)*Y^2)/(X)) + ((10)/(Y^2)) + (((-3)*W^2)/(2*Y^2)) + (((-3)*Z)/(2*Y^2)) + ((1*a)/(Y)) + (((-1)*W^2*a)/(2*Y)) + (((-1)*Z*a)/(2*Y)) + ((11)/(2)) + (((-1)*W^2)/(2)) + (((-1)*Z)/(2)) + (2*Y*a) + ((3*Y^2)/(2)) + ((1*Y^2*a^2)/(2)) + ((1*Y^3*a)/(2)) + ((3*X)/(Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + (((-3)*X*Z)/(2*Y^2)) + ((2*X*a)/(Y)) + (((-1)*X*W^2*a)/(2*Y)) + (((-1)*X*Z*a)/(2*Y)) + ((9*X)/(2)) + (((-1)*X*W^2)/(2)) + (((-1)*X*Z)/(2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2)/(2)) + (((-3)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + ((-1)*X^2*a^2) + (((-1)*X^2*Z)/(2)) + ((-1)*X^2*Y*a) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 232
  change ((1))*v 5 + ((1))*v 35 + (((1*W^2)/(X*Y^2)))*v 48 + ((1))*v 65 + (((1*W^2)/(X*Y^2)))*v 78 + ((1))*v 95 + (((1*W^2)/(X*Y^2)))*v 108 + ((1))*v 125 + (((1*W^2)/(X*Y^2)))*v 138 + ((1))*v 155 + (((1*W^2)/(X*Y^2)))*v 168 + ((1))*v 185 + (((1*W^2)/(X*Y^2)))*v 198 + ((1))*v 215 + (((1*W^2)/(X*Y^2)))*v 228 + ((1))*v 245 + (((1*W^2)/(X*Y^2)))*v 258 + ((1))*v 275 + (((1*W^2)/(X*Y^2)))*v 288 + ((1))*v 305 + (((1*W^2)/(X*Y^2)))*v 318 + ((1))*v 335 + (((1*W^2)/(X*Y^2)))*v 348 + ((1))*v 365 + (((1*W^2)/(X*Y^2)))*v 378 + ((1))*v 395 + (((1*W^2)/(X*Y^2)))*v 408 + ((1))*v 425 + (((1*W^2)/(X*Y^2)))*v 438 + ((1))*v 455 + (((1*W^2)/(X*Y^2)))*v 468 + (((1*W^2)/(X*Y^2)))*v 498=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p12 - ((1))*p35 - (((1*W^2)/(X*Y^2)))*p46 - (((1*W^2)/(X*Y^2)))*p58 - ((1))*p89 - ((1))*p95 - ((1))*p100 - (((1*W^2)/(X*Y^2)))*p120 - ((1))*p142 - ((1))*p145 - ((1))*p147 - ((1))*p148 - ((1))*p154 - (((1*W^2)/(X*Y^2)))*p180 - (((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*p194 - ((1))*p210 - (((1)/(X*Y^2)))*p230 - (((1)/(X*Y^2)))*p233 - ((1))*p251 - (((1*W^2)/(X*Y^2)))*p252 - ((1))*p254 - ((((-1)*Y^2)/(X)))*p256 - (((1)/(Y^2)))*p257 - (((2*W^2)/(X*Y^2)))*p262 - ((1))*p273 - (((2*W^2)/(X*Y^2)))*p302 - ((1))*p304 - (((1*W^2)/(X*Y^2)))*p310 - ((1))*p317 - (((-1)))*p319 - (((2*W^2)/(X*Y^2)))*p322 - (((1)/(X)) + ((-1)))*p330 - (((2*W^2)/(X*Y^2)))*p331 - (((1*W^2)/(X*Y^2)))*p333 - ((((-2)*W^2)/(X*Y^2)) + ((1*W^2)/(Y^2)))*p335 - (((1*W^2)/(X*Y^2)))*p337 - (((1*W^2)/(X*Y^2)))*p353 - (((1*W^2)/(X*Y^2)))*p354 - (((1*W^2)/(X^3*Y^2)))*p355 - (((1)/(X^3)) + ((1)/(X)) + ((-2)))*p358 - (((1*W^2)/(X*Y^2)))*p393 - (((1*W^2)/(X*Y^2)))*p394

#print axioms residual_10

compact_residual_elimination
theorem residual_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2)) + (((-1))/(X)) + (1*X^2) + (1*X^3))*v 370 + ((((-1)*W^2)/(X^3*Y^2)) + ((1)/(X^2*Y^2)) + (((-1)*W^2)/(X^2*Y^2)) + (((-2))/(X^2)) + (((-3))/(X*Y^2)) + ((1*W*b)/(X*Y^2)) + ((1*W^2)/(X*Y^2)) + ((1*a)/(X*Y)) + (((-1)*Y^2)/(X)) + (((-5))/(Y^2)) + ((2*W^2)/(Y^2)) + ((1*Z)/(Y^2)) + ((1*a)/(Y)) + ((-3)) + ((1*X*W*b)/(Y^2)) + ((1*X*W^2)/(Y^2)) + ((1*X*Z)/(Y^2)) + ((2*X*a)/(Y)) + ((-1)*X) + ((-1)*X*Y^2) + (((-1)*X^2)/(Y^2)))*v 390 + (((1)/(2*X^2*Y^2)) + ((1*a)/(2*X^2*Y)) + ((1*Y*a)/(2*X^2)) + ((1*Y^2)/(2*X^2)) + ((1*a)/(2*X*Y)) + (((-3))/(X)) + ((1*a^2)/(2*X)) + ((1*Y*a)/(2*X)) + ((1)/(2*Y^2)) + ((1*W*b)/(Y^2)) + (((-1)*W^2)/(2*Y^2)) + ((1*Z)/(2*Y^2)) + ((1*a)/(2*Y)) + (((-1)*W^2*a)/(2*Y)) + ((1*Z*a)/(2*Y)) + ((-1)) + (1*a^2) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + ((1*Y*a)/(2)) + (((-3)*Y^2)/(2)) + ((7*X)/(2*Y^2)) + (((-3)*X*W^2)/(2*Y^2)) + (((-1)*X*a)/(2*Y)) + (((-1)*X*W^2*a)/(2*Y)) + (((-3)*X)/(2)) + (((-1)*X*W^2)/(2)) + ((3*X*Y*a)/(2)) + (1*X*Y^2) + ((1*X*Y^2*a^2)/(2)) + ((1*X*Y^3*a)/(2)) + ((17*X^2)/(2*Y^2)) + ((1*X^2*W*b)/(Y^2)) + (((-2)*X^2*W^2)/(Y^2)) + (((-1)*X^2*Z)/(2*Y^2)) + ((2*X^2*a)/(Y)) + (((-1)*X^2*W^2*a)/(Y)) + ((1*X^2*Z*a)/(2*Y)) + ((3*X^2)/(2)) + ((3*X^2*a^2)/(2)) + ((-1)*X^2*W^2) + ((1*X^2*Z)/(2)) + ((3*X^2*Y*a)/(2)) + ((-1)*X^2*Y^2) + ((7*X^3)/(2*Y^2)) + (((-1)*X^3*W^2)/(Y^2)) + (((-3)*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + (((-1)*X^3*W^2*a)/(Y)) + (((-1)*X^3*Z*a)/(2*Y)) + (6*X^3) + ((-1)*X^3*a^2) + ((-1)*X^3*W^2) + (((-1)*X^3*Z)/(2)) + (1*X^3*Y*a) + ((3*X^3*Y^2)/(2)) + ((1*X^3*Y^2*a^2)/(2)) + ((1*X^3*Y^3*a)/(2)) + ((3*X^4)/(2*Y^2)) + (((-1)*X^4*Z)/(2*Y^2)) + ((1*X^4*a)/(2*Y)) + (((-1)*X^4*Z*a)/(2*Y)) + (1*X^4) + (((-1)*X^4*Z)/(2)) + ((1*X^4*Y*a)/(2)) + ((1*X^4*Y^2)/(2)))*v 435=0 := by
  have h:=hv 233
  change ((1))*v 20 + (((1*X*W^2)/(Y^2)))*v 21 + (((1*X*W^2)/(Y^2)))*v 51 + ((1))*v 80 + (((1*X*W^2)/(Y^2)))*v 81 + ((1))*v 110 + (((1*X*W^2)/(Y^2)))*v 111 + ((1))*v 140 + (((1*X*W^2)/(Y^2)))*v 141 + ((1))*v 170 + (((1*X*W^2)/(Y^2)))*v 171 + ((1))*v 200 + (((1*X*W^2)/(Y^2)))*v 201 + ((1))*v 230 + (((1*X*W^2)/(Y^2)))*v 231 + ((1))*v 260 + (((1*X*W^2)/(Y^2)))*v 261 + ((1))*v 290 + (((1*X*W^2)/(Y^2)))*v 291 + ((1))*v 320 + (((1*X*W^2)/(Y^2)))*v 321 + ((1))*v 350 + (((1*X*W^2)/(Y^2)))*v 351 + ((1))*v 380 + (((1*X*W^2)/(Y^2)))*v 381 + ((1))*v 410 + (((1*X*W^2)/(Y^2)))*v 411 + ((1))*v 440 + (((1*X*W^2)/(Y^2)))*v 441 + ((1))*v 470 + (((1*X*W^2)/(Y^2)))*v 471 + ((1))*v 500=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p1 - ((1))*p21 - ((1))*p64 - (((1*X*W^2)/(Y^2)))*p65 - (((1*X*W^2)/(Y^2)))*p66 - ((1))*p78 - (((1*X*W^2)/(Y^2)))*p80 - (((1)/(Y^2)))*p91 - ((1))*p92 - ((1))*p93 - (((1*X*W^2)/(Y^2)))*p103 - ((1))*p117 - (((2*W^2)/(Y^2)))*p126 - (((1*X*W^2)/(Y^2)))*p130 - (((1*X*W^2)/(Y^2)))*p151 - ((1))*p156 - (((1*X*W^2)/(Y^2)))*p157 - ((1))*p164 - (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*p189 - ((1))*p192 - (((3*X)/(Y^2)))*p194 - (((-1)))*p195 - (((1*X)/(Y^2)))*p196 - (((1*X*W^2)/(Y^2)))*p211 - ((2))*p219 - (((1*X*W^2)/(Y^2)))*p222 - ((1))*p227 - (((2)/(Y^2)) + (1) + (2*X))*p230 - ((((-1)*Z)/(Y^2)))*p232 - (((2*X)/(Y^2)))*p236 - ((1))*p242 - (((2*W^2)/(Y^2)))*p252 - (((-2)))*p256 - ((((-2)*X)/(Y^2)) + ((1*X*Z)/(Y^2)))*p257 - (((1*X*W^2)/(Y^2)))*p258 - (((1*X*W^2)/(Y^2)))*p265 - (((1*X*W^2)/(Y^2)))*p278 - (((1*X*W^2)/(Y^2)))*p291 - ((((-1)*W^2)/(Y^2)))*p313 - (((1*X*W^2)/(Y^2)))*p318 - ((1))*p319 - (((1*X^2*W^2)/(Y^2)))*p322 - ((1))*p330 - (((1*X*W^2)/(Y^2)))*p333 - ((((-2)*W^2)/(Y^2)))*p335 - ((((-1)*W^2)/(Y^2)))*p336 - ((((-1)*X*W^2)/(Y^2)))*p341 - (((1*X*W^2)/(Y^2)))*p345 - (((1*X*W^2)/(Y^2)))*p351 - ((((-1)*W^2)/(X^2*Y^2)) + ((1*X^2*W^2)/(Y^2)))*p354 - ((2))*p358 - ((((-1)*W^2)/(Y^2)))*p403 - ((((-1)*W^2)/(Y^2)))*p404

#print axioms residual_11

compact_residual_elimination
theorem residual_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2)) + (1*X^2))*v 370 + (((1*W^2)/(X^3*Y^2)) + ((4)/(X^2*Y^2)) + ((2*W^2)/(X^2*Y^2)) + (((-1)*Z)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + ((4)/(X^2)) + ((2)/(X*Y^2)) + (((-2)*W*b)/(X*Y^2)) + (((-4)*W^2)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)) + (((-2)*a)/(X*Y)) + ((1)/(X)) + ((1*Y^2)/(X)) + (((-1))/(Y^2)) + ((2*W*b)/(Y^2)) + ((1*a)/(Y)) + (2) + ((-1)*Y^2) + (((-2)*X)/(Y^2)) + (((-1)*X*W*b)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + ((-3)*X) + (((-5)*X^2)/(Y^2)) + ((2*X^2*Z)/(Y^2)) + ((2*X^2*a)/(Y)) + ((-3)*X^2) + ((2*X^3)/(Y^2)) + ((-2)*X^3))*v 390 + ((((-1))/(2*X^2*Y^2)) + (((-1)*a)/(2*X^2*Y)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^2)/(2*X^2)) + (((-2))/(X*Y^2)) + (((-2)*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-2)*Y*a)/(X)) + (((-1)*Y^2)/(X)) + (((-15))/(2*Y^2)) + (((-1)*W*b)/(Y^2)) + ((1*W^2)/(2*Y^2)) + ((1*Z)/(2*Y^2)) + (((-1)*a)/(2*Y)) + ((1*W^2*a)/(2*Y)) + (((-1)*Z*a)/(2*Y)) + ((-2)*a^2) + ((1*W^2)/(2)) + (((-1)*Z)/(2)) + (((-3)*Y*a)/(2)) + ((3*Y^2)/(2)) + (((-13)*X)/(2*Y^2)) + ((2*X*W*b)/(Y^2)) + ((2*X*W^2)/(Y^2)) + ((2*X*Z)/(Y^2)) + ((1*X*Z*a)/(Y)) + (((-5)*X)/(2)) + ((1*X*a^2)/(2)) + (1*X*Z) + ((-2)*X*Y*a) + ((-3)*X*Y^2) + (((-1)*X*Y^2*a^2)/(2)) + (((-1)*X*Y^3*a)/(2)) + (((-5)*X^2)/(2*Y^2)) + (((-1)*X^2*W*b)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*W^2*a)/(Y)) + (((-3)*X^2*a^2)/(2)) + (1*X^2*W^2) + (((-1)*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^3*a)/(2)) + ((3*X^3)/(2*Y^2)) + (((-1)*X^3*W^2)/(Y^2)) + ((1*X^3*Z)/(Y^2)) + ((1*X^3*a)/(Y)) + (((-7)*X^3)/(2)) + ((5*X^3*a^2)/(2)) + ((5*X^3*Y*a)/(2)) + ((15*X^4)/(2*Y^2)) + (((-1)*X^4*W^2)/(2*Y^2)) + (((-3)*X^4*Z)/(2*Y^2)) + (((-1)*X^4*a)/(Y)) + (((-1)*X^4*W^2*a)/(2*Y)) + ((1*X^4*Z*a)/(2*Y)) + ((-1)*X^4) + ((1*X^4*a^2)/(2)) + (((-1)*X^4*W^2)/(2)) + ((1*X^4*Z)/(2)) + (1*X^4*Y*a) + ((1*X^4*Y^2)/(2)) + ((4*X^5)/(Y^2)) + (((-1)*X^5*Z)/(Y^2)) + ((3*X^5*a)/(Y)) + (((-1)*X^5*Z*a)/(Y)) + (3*X^5) + (1*X^5*a^2) + ((-1)*X^5*Z) + (2*X^5*Y*a) + (1*X^5*Y^2))*v 435=0 := by
  have h:=hv 234
  change ((1))*v 10 + (((1*X*W^2)/(Y^2)))*v 39 + ((1))*v 40 + (((1*X*W^2)/(Y^2)))*v 69 + ((1))*v 70 + (((1*X*W^2)/(Y^2)))*v 99 + ((1))*v 100 + (((1*X*W^2)/(Y^2)))*v 129 + ((1))*v 130 + (((1*X*W^2)/(Y^2)))*v 159 + ((1))*v 160 + (((1*X*W^2)/(Y^2)))*v 189 + ((1))*v 190 + (((1*X*W^2)/(Y^2)))*v 219 + ((1))*v 220 + (((1*X*W^2)/(Y^2)))*v 249 + ((1))*v 250 + (((1*X*W^2)/(Y^2)))*v 279 + ((1))*v 280 + (((1*X*W^2)/(Y^2)))*v 309 + ((1))*v 310 + (((1*X*W^2)/(Y^2)))*v 339 + ((1))*v 340 + (((1*X*W^2)/(Y^2)))*v 369 + ((1))*v 370 + (((1*X*W^2)/(Y^2)))*v 399 + ((1))*v 400 + (((1*X*W^2)/(Y^2)))*v 429 + ((1))*v 430 + (((1*X*W^2)/(Y^2)))*v 459 + (((1*X*W^2)/(Y^2)))*v 489 + ((1))*v 490=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p31 - ((1))*p43 - ((1))*p60 - ((1))*p62 - (((1*X*W^2)/(Y^2)))*p87 - ((1))*p88 - (((1*X*W^2)/(Y^2)))*p97 - ((1))*p98 - (((1*X*W^2)/(Y^2)))*p116 - ((1))*p118 - (((1*X*W^2)/(Y^2)))*p135 - ((1))*p144 - (((1*X*W^2)/(Y^2)))*p153 - (((1*X*W^2)/(Y^2)))*p163 - ((1))*p193 - (((1*X*W^2)/(Y^2)))*p201 - ((2))*p205 - (((1*X)/(Y^2)))*p208 - (((1*X*W^2)/(Y^2)))*p214 - ((((-2))/(Y^2)) + ((-1)) + ((-2)*X))*p230 - ((((-1)*Z)/(Y^2)))*p233 - ((((-1)*X)/(Y^2)))*p235 - ((1))*p239 - ((1))*p246 - (((2*X*W^2)/(Y^2)))*p253 - ((2))*p256 - (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*p257 - (((1*X*W^2)/(Y^2)))*p259 - (((1*X*W^2)/(Y^2)))*p261 - ((1))*p264 - ((1))*p277 - (((1*X*W^2)/(Y^2)))*p279 - (((1*X*W^2)/(Y^2)))*p298 - (((1*X*W^2)/(Y^2)))*p306 - ((((-1)*W^2)/(Y^2)))*p310 - (((1*X*W^2)/(Y^2)))*p329 - (((-1)))*p330 - ((((-2)*W^2)/(Y^2)))*p331 - (((2*W^2)/(Y^2)))*p335 - ((((-1)*W^2)/(Y^2)))*p337 - ((((-1)*X*W^2)/(Y^2)))*p339 - ((((-1)*X*W^2)/(Y^2)))*p342 - (((1*X*W^2)/(Y^2)))*p350 - ((((-1)*W^2)/(X^2*Y^2)) + ((1*X^2*W^2)/(Y^2)))*p355 - ((((-1))/(X^2)) + ((-2)) + (1*X^2))*p358 - ((((-1)*W^2)/(Y^2)))*p394 - (((1*X*W^2)/(Y^2)))*p395

#print axioms residual_12

compact_residual_elimination
theorem residual_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X^2)) + (((-2)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 370 + ((((-1)*W^2)/(X^3)) + ((1)/(X^2)) + (((-2)*Y^2)/(X^2)) + (((-1))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Y*a)/(X)) + (((-1)*Y^4)/(X)) + (3) + ((-1)*Z) + ((-1)*Y*a) + (3*Y^2) + (3*X) + ((-1)*X*Z) + ((-1)*X*Y*a) + (4*X*Y^2) + ((-1)*X^2) + (1*X^2*Y^2))*v 390 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + (((-1))/(2*X)) + (((-7)*Y^2)/(2*X)) + ((1*Y^2*a^2)/(2*X)) + ((1*Y^3*a)/(2*X)) + (1*W*b) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-1)*Y^2) + (1*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + ((-2)*Y^4) + (((-1)*X)/(2)) + (((-3)*X*W^2)/(2)) + ((-2)*X*Y*a) + (((-1)*X*Y*W^2*a)/(2)) + ((9*X*Y^2)/(2)) + (((-3)*X*Y^2*a^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + ((-1)*X*Y^3*a) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + ((-7)*X^2) + (((-1)*X^2*W^2)/(2)) + (1*X^2*Z) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*W^2*a)/(2)) + (3*X^2*Y^2) + (((-3)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-5)*X^2*Y^3*a)/(2)) + ((-1)*X^2*Y^4) + (((-17)*X^3)/(2)) + ((3*X^3*Z)/(2)) + ((-2)*X^3*Y*a) + ((1*X^3*Y*Z*a)/(2)) + (((-3)*X^3*Y^2)/(2)) + (((-3)*X^3*Y^2*a^2)/(2)) + ((1*X^3*Y^2*Z)/(2)) + (((-5)*X^3*Y^3*a)/(2)) + ((-1)*X^3*Y^4) + ((-2)*X^4) + ((1*X^4*Z)/(2)) + (((-3)*X^4*Y*a)/(2)) + ((1*X^4*Y*Z*a)/(2)) + (((-3)*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*a^2)/(2)) + ((1*X^4*Y^2*Z)/(2)) + ((-1)*X^4*Y^3*a) + (((-1)*X^4*Y^4)/(2)))*v 435=0 := by
  have h:=hv 235
  change ((1))*v 15 + (((1*W^2)/(X)))*v 24 + ((1))*v 45 + (((1*W^2)/(X)))*v 54 + (((1*W^2)/(X)))*v 84 + ((1))*v 105 + (((1*W^2)/(X)))*v 114 + ((1))*v 135 + (((1*W^2)/(X)))*v 144 + ((1))*v 165 + (((1*W^2)/(X)))*v 174 + ((1))*v 195 + (((1*W^2)/(X)))*v 204 + ((1))*v 225 + (((1*W^2)/(X)))*v 234 + ((1))*v 255 + (((1*W^2)/(X)))*v 264 + ((1))*v 285 + (((1*W^2)/(X)))*v 294 + ((1))*v 315 + (((1*W^2)/(X)))*v 324 + ((1))*v 345 + (((1*W^2)/(X)))*v 354 + ((1))*v 375 + (((1*W^2)/(X)))*v 384 + ((1))*v 405 + (((1*W^2)/(X)))*v 414 + ((1))*v 435 + (((1*W^2)/(X)))*v 444 + ((1))*v 465 + (((1*W^2)/(X)))*v 474 + ((1))*v 495=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*W^2)/(X)))*p0 - ((1))*p2 - ((1))*p5 - ((1))*p6 - ((1))*p83 - ((1))*p99 - ((1))*p102 - (((1*W^2)/(X)))*p104 - (((1*W^2)/(X)))*p109 - (((1*W^2)/(X)))*p126 - ((1))*p131 - ((1))*p137 - (((1*W^2)/(X)))*p152 - (((1*W^2)/(X)))*p158 - (((1*W^2)/(X)))*p165 - ((1))*p189 - ((1))*p194 - ((1))*p196 - ((2))*p198 - ((2))*p202 - ((1))*p208 - (((1*W^2)/(X)))*p220 - (((1*W^2)/(X)))*p224 - ((((-1)*Z)/(X)))*p230 - (((1)/(X)) + ((-1)))*p235 - ((2))*p236 - ((((-1)*Y^2)/(X)))*p256 - ((1))*p257 - (((1*W^2)/(X)))*p263 - (((-1)*Y^2))*p264 - (((1*W^2)/(X)))*p267 - (((-1)*W^2))*p274 - (((1*W^2)/(X)))*p288 - (((1*W^2)/(X)))*p293 - (((-1)*W^2))*p313 - (((1*W^2)/(X)))*p339 - (((1*W^2)/(X)))*p342 - ((((-1)*W^2)/(X^2)))*p353 - ((((-1)*W^2)/(X^2)))*p354 - (((-1)*W^2))*p355 - (((1*W^2)/(X)))*p357 - (((-1)*Y^2) + ((-1)*X*Y^2))*p358

#print axioms residual_13

compact_residual_elimination
theorem residual_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2)) + (((-1)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 370 + (((1*W^2)/(X^3)) + ((4)/(X^2)) + ((1*W^2)/(X^2)) + (((-1)*Z)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((4*Y^2)/(X^2)) + ((5)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Z)/(X)) + (((-2)*Y*a)/(X)) + ((3*Y^2)/(X)) + ((1*Y^4)/(X)) + ((-1)) + ((-2)*X*Y^2))*v 390 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + (((-3))/(2*X)) + (((-3)*Y*a)/(2*X)) + ((4*Y^2)/(X)) + (((-1)*Y^2*a^2)/(X)) + (((-3)*Y^3*a)/(2*X)) + (((-1)*Y^4)/(2*X)) + ((-8)) + ((-1)*W*b) + ((1*W^2)/(2)) + ((1*Z)/(2)) + ((-1)*Y*a) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (2*Y^2) + ((-2)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + ((-2)*Y^3*a) + (1*Y^4) + ((-10)*X) + ((3*X*W^2)/(2)) + ((3*X*Z)/(2)) + ((-1)*X*Y*a) + ((1*X*Y*W^2*a)/(2)) + ((1*X*Y*Z*a)/(2)) + (((-11)*X*Y^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + ((1*X*Y^2*Z)/(2)) + ((-2)*X*Y^3*a) + (((-3)*X*Y^4)/(2)) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + ((-1)*X^2) + ((1*X^2*W^2)/(2)) + ((1*X^2*Z)/(2)) + ((-2)*X^2*Y*a) + ((1*X^2*Y*W^2*a)/(2)) + ((1*X^2*Y*Z*a)/(2)) + (((-9)*X^2*Y^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((1*X^2*Y^2*Z)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-1)*X^2*Y^4)/(2)) + (2*X^3) + (1*X^3*Y*a) + (1*X^3*Y^2*a^2) + (1*X^3*Y^3*a))*v 435=0 := by
  have h:=hv 236
  change ((1))*v 15 + (((1*W^2)/(X)))*v 36 + ((1))*v 45 + (((1*W^2)/(X)))*v 66 + ((1))*v 75 + (((1*W^2)/(X)))*v 96 + ((1))*v 105 + (((1*W^2)/(X)))*v 126 + ((1))*v 135 + (((1*W^2)/(X)))*v 156 + ((1))*v 165 + (((1*W^2)/(X)))*v 186 + ((1))*v 195 + (((1*W^2)/(X)))*v 216 + ((1))*v 225 + (((1*W^2)/(X)))*v 246 + ((1))*v 255 + (((1*W^2)/(X)))*v 276 + ((1))*v 285 + (((1*W^2)/(X)))*v 306 + ((1))*v 315 + (((1*W^2)/(X)))*v 336 + ((1))*v 345 + (((1*W^2)/(X)))*v 366 + ((1))*v 375 + (((1*W^2)/(X)))*v 396 + ((1))*v 405 + (((1*W^2)/(X)))*v 426 + (((1*W^2)/(X)))*v 456 + ((1))*v 465 + (((1*W^2)/(X)))*v 486 + ((1))*v 495=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p2 - ((1))*p5 - ((1))*p6 - (((1*W^2)/(X)))*p16 - ((1))*p83 - (((1*W^2)/(X)))*p96 - ((1))*p99 - ((1))*p102 - (((1*W^2)/(X)))*p114 - (((1*W^2)/(X)))*p115 - (((1*W^2)/(X)))*p127 - ((1))*p131 - ((1))*p137 - (((1*W^2)/(X)))*p143 - (((1*W^2)/(X)))*p162 - ((2))*p189 - ((2))*p194 - ((((-1)*Z)/(X)))*p195 - ((1))*p196 - ((2))*p198 - (((1*W^2)/(X)))*p199 - ((2))*p202 - (((1*W^2)/(X)))*p204 - ((1))*p208 - (((1*Z)/(X)))*p230 - (((2)/(X)) + ((-1)))*p235 - ((1))*p236 - (((1*Y^2)/(X)))*p256 - (((-1)))*p257 - (((1*W^2)/(X)))*p269 - (((1*W^2)/(X)))*p309 - (((-1)*W^2))*p310 - (((-1)*W^2))*p322 - (((1*W^2)/(X)))*p327 - (((1*W^2)/(X)))*p332 - (((1*W^2)/(X)))*p341 - (((1*W^2)/(X)))*p346 - (((-1)*W^2))*p354 - ((((-1)*W^2)/(X^2)))*p355 - (((1*W^2)/(X)))*p356 - ((((-1)*Y^2)/(X^2)) + (((-1)*Y^2)/(X)))*p358

#print axioms residual_14

compact_residual_elimination
theorem residual_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-2)) + (1*Z) + (2*X) + ((-1)*X*Z))*v 390 + ((2*X^2) + ((-1)*X^2*Z) + ((-1)*X^3) + ((1*X^3*Z)/(2)) + (1*X^3*Y*a) + (((-1)*X^3*Y*Z*a)/(2)) + (1*X^3*Y^2) + (((-1)*X^3*Y^2*Z)/(2)) + ((-1)*X^4) + ((1*X^4*Z)/(2)) + ((-1)*X^4*Y*a) + ((1*X^4*Y*Z*a)/(2)) + ((-1)*X^4*Y^2) + ((1*X^4*Y^2*Z)/(2)))*v 435=0 := by
  have h:=hv 237
  change ((1))*v 0 + ((1))*v 30 + ((1*X*Y^2))*v 35 + ((1))*v 60 + ((1*X*Y^2))*v 65 + ((1))*v 90 + ((1*X*Y^2))*v 95 + ((1))*v 120 + ((1*X*Y^2))*v 125 + ((1))*v 150 + ((1*X*Y^2))*v 155 + ((1))*v 180 + ((1*X*Y^2))*v 185 + ((1))*v 210 + ((1*X*Y^2))*v 215 + ((1))*v 240 + ((1*X*Y^2))*v 245 + ((1))*v 270 + ((1*X*Y^2))*v 275 + ((1))*v 300 + ((1*X*Y^2))*v 305 + ((1))*v 330 + ((1*X*Y^2))*v 335 + ((1))*v 360 + ((1*X*Y^2))*v 365 + ((1))*v 390 + ((1*X*Y^2))*v 395 + ((1*X*Y^2))*v 425 + ((1))*v 450 + ((1*X*Y^2))*v 455 + ((1))*v 480 + ((1*X*Y^2))*v 485=0 at h
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p3 - ((1))*p9 - ((1))*p10 - ((1*X*Y^2))*p12 - ((1))*p13 - ((1))*p15 - ((1))*p27 - ((1))*p77 - ((1*X*Y^2))*p89 - ((1))*p91 - ((1*X*Y^2))*p95 - ((1*X*Y^2))*p100 - ((1))*p121 - ((1*X*Y^2))*p138 - ((1*X*Y^2))*p142 - ((((-1)*W^2)/(Z)))*p143 - ((1*X*Y^2))*p145 - ((1*X*Y^2))*p147 - ((1*X*Y^2))*p148 - ((1))*p150 - ((1*X*Y^2))*p154 - ((1*X))*p189 - ((2*X))*p194 - ((2))*p195 - ((1*X*Y^2))*p210 - ((1))*p232 - ((2))*p233 - ((1))*p235 - ((1*X*Y^2))*p251 - ((1*X*Y^2))*p254 - (((-1)*Y^4))*p256 - ((1*X))*p257 - ((1*W^2))*p262 - ((1*X*Y^2))*p273 - ((1*W^2))*p302 - ((1*X*Y^2))*p304 - ((1*X*Y^2))*p317 - (((-1)*X*Y^2))*p319 - ((1*W^2))*p322 - (((-1)*X*Y^2))*p330 - ((1*W^2))*p331 - (((-1)*W^2) + (1*X*W^2))*p335 - ((1*Y^2) + ((-1)*X*Y^2))*p358

#print axioms residual_15

compact_residual_elimination
theorem residual_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + ((((-1))/(X^3)) + (((-4))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 390 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((10*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((11*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-2)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(W^2)))*v 435=0 := by
  have h:=hv 239
  change (((1)/(W^2)))*v 0 + ((1))*v 18 + (((1)/(W^2)))*v 30 + ((1))*v 48 + (((1)/(W^2)))*v 60 + ((1))*v 78 + (((1)/(W^2)))*v 90 + ((1))*v 108 + (((1)/(W^2)))*v 120 + ((1))*v 138 + (((1)/(W^2)))*v 150 + ((1))*v 168 + ((1))*v 198 + (((1)/(W^2)))*v 210 + ((1))*v 228 + (((1)/(W^2)))*v 240 + (((1)/(W^2)))*v 270 + ((1))*v 288 + (((1)/(W^2)))*v 300 + ((1))*v 318 + (((1)/(W^2)))*v 330 + ((1))*v 348 + (((1)/(W^2)))*v 360 + ((1))*v 378 + (((1)/(W^2)))*v 390 + ((1))*v 408 + (((1)/(W^2)))*v 420 + ((1))*v 438 + (((1)/(W^2)))*v 450 + ((1))*v 468 + (((1)/(W^2)))*v 480 + ((1))*v 498=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p3 - (((1)/(W^2)))*p4 - ((1))*p8 - (((1)/(W^2)))*p9 - (((1)/(W^2)))*p10 - (((1)/(W^2)))*p13 - (((1)/(W^2)))*p15 - (((1)/(W^2)))*p27 - ((1))*p58 - (((1)/(W^2)))*p77 - (((1)/(W^2)))*p91 - ((1))*p120 - (((1)/(W^2)))*p121 - (((1)/(W^2)))*p150 - ((1))*p180 - (((1*X)/(W^2)))*p189 - (((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)))*p194 - (((1)/(W^2)))*p230 - (((1)/(W^2)))*p232 - (((1)/(W^2)))*p233 - (((1)/(W^2)))*p235 - ((1))*p252 - ((1))*p262 - ((1))*p302 - ((1))*p310 - ((1))*p322 - (((1*Y^2)/(W^2)))*p330 - ((1))*p331 - ((1))*p333 - (((-1)))*p335 - ((1))*p337 - ((1))*p353 - ((1))*p354 - (((1)/(X^2)))*p355 - (((1*Y^2)/(X^2*W^2)) + (((-1)*X*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394

#print axioms residual_16

compact_residual_elimination
theorem residual_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + (((-1))/(X^2*W^2)) + ((1)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-3)*X)/(2*W^2)) + ((3*X)/(2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-9)*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + ((15*X^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((19*X^3)/(2*W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 240
  change (((1)/(W^2)))*v 0 + ((1))*v 12 + (((1)/(W^2)))*v 30 + ((1))*v 42 + (((1)/(W^2)))*v 60 + ((1))*v 72 + (((1)/(W^2)))*v 90 + ((1))*v 102 + (((1)/(W^2)))*v 120 + ((1))*v 132 + (((1)/(W^2)))*v 150 + ((1))*v 162 + (((1)/(W^2)))*v 180 + ((1))*v 192 + (((1)/(W^2)))*v 210 + ((1))*v 222 + (((1)/(W^2)))*v 240 + (((1)/(W^2)))*v 270 + ((1))*v 282 + (((1)/(W^2)))*v 300 + ((1))*v 312 + ((1))*v 342 + (((1)/(W^2)))*v 360 + ((1))*v 372 + (((1)/(W^2)))*v 390 + ((1))*v 402 + (((1)/(W^2)))*v 420 + ((1))*v 432 + (((1)/(W^2)))*v 450 + ((1))*v 462 + (((1)/(W^2)))*v 480 + ((1))*v 492=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p3 - (((1)/(W^2)))*p4 - (((1)/(W^2)))*p9 - (((1)/(W^2)))*p10 - (((1)/(W^2)))*p13 - (((1)/(W^2)))*p15 - (((1)/(W^2)))*p27 - ((1))*p37 - ((1))*p70 - (((1)/(W^2)))*p77 - (((1)/(W^2)))*p91 - ((1))*p113 - (((1)/(W^2)))*p121 - ((1))*p124 - (((1)/(W^2)))*p150 - ((1))*p170 - (((1*X)/(W^2)))*p189 - (((1*X)/(W^2)))*p194 - (((1)/(W^2)))*p195 - ((((-1))/(W^2)))*p230 - (((1)/(W^2)))*p232 - (((1)/(W^2)))*p233 - (((1)/(W^2)))*p235 - ((1*X))*p253 - ((1))*p261 - (((1*Y^2)/(W^2)))*p264 - ((1))*p268 - ((1))*p274 - ((1))*p299 - ((1))*p313 - ((1))*p335 - ((1))*p336 - ((1))*p352 - (((1)/(X^2)))*p354 - ((1))*p355 - (((1*Y^2)/(W^2)) + ((2*X*Y^2)/(W^2)))*p358 - ((1))*p403 - ((1))*p404

#print axioms residual_17

compact_residual_elimination
theorem residual_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*b)/(W)) + (2) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(W)) + (((-1)*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-7)*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-5)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-17)*X^4)/(2*W^2)) + ((3*X^4*Z)/(2*W^2)) + (((-2)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 241
  change (((1*Y^2)/(W^2)))*v 20 + ((1))*v 24 + (((1*Y^2)/(W^2)))*v 50 + ((1))*v 54 + (((1*Y^2)/(W^2)))*v 80 + ((1))*v 84 + (((1*Y^2)/(W^2)))*v 110 + ((1))*v 114 + (((1*Y^2)/(W^2)))*v 140 + ((1))*v 144 + (((1*Y^2)/(W^2)))*v 170 + ((1))*v 174 + (((1*Y^2)/(W^2)))*v 200 + ((1))*v 204 + ((1))*v 234 + (((1*Y^2)/(W^2)))*v 260 + (((1*Y^2)/(W^2)))*v 290 + ((1))*v 294 + (((1*Y^2)/(W^2)))*v 320 + ((1))*v 324 + (((1*Y^2)/(W^2)))*v 350 + ((1))*v 354 + (((1*Y^2)/(W^2)))*v 380 + ((1))*v 384 + (((1*Y^2)/(W^2)))*v 410 + ((1))*v 414 + (((1*Y^2)/(W^2)))*v 440 + ((1))*v 444 + (((1*Y^2)/(W^2)))*v 470 + ((1))*v 474 + (((1*Y^2)/(W^2)))*v 500 + ((1))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - (((1*Y^2)/(W^2)))*p1 - (((1*Y^2)/(W^2)))*p21 - ((1))*p47 - (((1*Y^2)/(W^2)))*p64 - (((1*Y^2)/(W^2)))*p78 - (((1*Y^2)/(W^2)))*p92 - (((1*Y^2)/(W^2)))*p93 - ((1))*p104 - (((1*Y^2)/(W^2)))*p117 - ((2))*p126 - (((1*Y^2)/(W^2)))*p134 - ((1))*p152 - ((1))*p158 - (((1*Y^2)/(W^2)))*p164 - ((1))*p165 - (((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)))*p189 - (((1*Y^2)/(W^2)))*p192 - (((1*X)/(W^2)))*p194 - ((((-1)*Y^2)/(W^2)))*p195 - (((1*X)/(W^2)))*p196 - (((1*X)/(W^2)))*p198 - (((1*X)/(W^2)))*p202 - (((1*Y^2)/(W^2)))*p219 - ((1))*p220 - ((1))*p224 - (((1*Y^2)/(W^2)))*p227 - (((1)/(W^2)) + (((-1)*Z)/(W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*p230 - ((((-1)*X)/(Z)))*p231 - (((2*X)/(W^2)))*p236 - (((1*Y^2)/(W^2)))*p242 - ((1))*p252 - ((((-2)*Y^2)/(W^2)))*p256 - ((((-1)*X)/(W^2)) + ((1*X*Z)/(W^2)))*p257 - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p267 - (((-1)*X))*p274 - ((1))*p288 - ((1))*p293 - (((-1)*X))*p313 - (((1*Y^2)/(W^2)))*p319 - (((1*Y^2)/(W^2)))*p330 - (((-1)))*p335 - ((1))*p339 - ((1))*p342 - ((((-1))/(X)))*p353 - ((((-1))/(X)))*p354 - (((-1)*X))*p355 - ((1))*p357 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*p358

#print axioms residual_18

compact_residual_elimination
theorem residual_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^2)) + ((4)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((5)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-8)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-10)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-9)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)))*v 435=0 := by
  have h:=hv 242
  change ((1))*v 6 + (((1*Y^2)/(W^2)))*v 10 + ((1))*v 36 + (((1*Y^2)/(W^2)))*v 40 + ((1))*v 66 + (((1*Y^2)/(W^2)))*v 70 + ((1))*v 96 + (((1*Y^2)/(W^2)))*v 100 + ((1))*v 126 + (((1*Y^2)/(W^2)))*v 130 + ((1))*v 156 + (((1*Y^2)/(W^2)))*v 160 + ((1))*v 186 + (((1*Y^2)/(W^2)))*v 190 + ((1))*v 216 + (((1*Y^2)/(W^2)))*v 220 + (((1*Y^2)/(W^2)))*v 250 + ((1))*v 276 + ((1))*v 306 + (((1*Y^2)/(W^2)))*v 310 + ((1))*v 336 + (((1*Y^2)/(W^2)))*v 340 + ((1))*v 366 + (((1*Y^2)/(W^2)))*v 370 + ((1))*v 396 + (((1*Y^2)/(W^2)))*v 400 + ((1))*v 426 + (((1*Y^2)/(W^2)))*v 430 + ((1))*v 456 + (((1*Y^2)/(W^2)))*v 460 + ((1))*v 486 + (((1*Y^2)/(W^2)))*v 490=0 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p16 - (((1*Y^2)/(W^2)))*p31 - ((1))*p36 - (((1*Y^2)/(W^2)))*p43 - (((1*Y^2)/(W^2)))*p60 - (((1*Y^2)/(W^2)))*p88 - ((1))*p96 - (((1*Y^2)/(W^2)))*p98 - ((1))*p114 - ((1))*p115 - (((1*Y^2)/(W^2)))*p118 - ((1))*p127 - (((1*Y^2)/(W^2)))*p136 - ((1))*p143 - (((1*Y^2)/(W^2)))*p144 - (((1*Y^2)/(W^2)))*p193 - ((((-1)*Z)/(W^2)))*p195 - (((1*X)/(W^2)))*p198 - ((1))*p199 - (((1*X)/(W^2)))*p202 - ((1))*p204 - (((1*Y^2)/(W^2)))*p205 - (((1*X)/(W^2)))*p208 - ((((-1))/(W^2)) + ((1*Z)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p230 - ((((-1)*X)/(Z)))*p234 - (((1)/(W^2)) + (((-1)*X)/(W^2)))*p235 - (((1*Y^2)/(W^2)))*p239 - (((1*Y^2)/(W^2)))*p246 - ((1*X))*p253 - (((2*Y^2)/(W^2)))*p256 - (((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)))*p257 - (((1*Y^2)/(W^2)))*p264 - ((1))*p269 - (((1*Y^2)/(W^2)))*p277 - ((1))*p309 - (((-1)*X))*p310 - (((-1)*X))*p322 - ((1))*p327 - (((-1)))*p331 - ((1))*p332 - ((1))*p335 - ((1))*p341 - ((1))*p346 - (((-1)*X))*p354 - ((((-1))/(X)))*p355 - ((1))*p356 - ((((-1)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)))*p358

#print axioms residual_19

compact_residual_elimination
theorem residual_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)) + ((-1)) + ((-1)*X) + ((-1)*X^2))*v 370 + (((1*W^2)/(X^2*Y^2)) + ((4)/(X*Y^2)) + ((1*W^2)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((4)/(X)) + ((5)/(Y^2)) + (((-1)*W*b)/(Y^2)) + (((-2)*W^2)/(Y^2)) + (((-1)*Z)/(Y^2)) + (((-2)*a)/(Y)) + (3) + (1*Y^2) + (((-1)*X)/(Y^2)) + ((-2)*X^2))*v 390 + ((((-1))/(2*X*Y^2)) + (((-1)*a)/(2*X*Y)) + (((-1)*Y*a)/(2*X)) + (((-1)*Y^2)/(2*X)) + (((-3))/(2*Y^2)) + (((-3)*a)/(2*Y)) + (4) + ((-1)*a^2) + (((-3)*Y*a)/(2)) + (((-1)*Y^2)/(2)) + (((-8)*X)/(Y^2)) + (((-1)*X*W*b)/(Y^2)) + ((1*X*W^2)/(2*Y^2)) + ((1*X*Z)/(2*Y^2)) + (((-1)*X*a)/(Y)) + ((1*X*W^2*a)/(2*Y)) + (((-1)*X*Z*a)/(2*Y)) + (2*X) + ((-2)*X*a^2) + ((1*X*W^2)/(2)) + (((-1)*X*Z)/(2)) + ((-2)*X*Y*a) + (1*X*Y^2) + (((-10)*X^2)/(Y^2)) + ((3*X^2*W^2)/(2*Y^2)) + ((3*X^2*Z)/(2*Y^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*W^2*a)/(2*Y)) + ((1*X^2*Z*a)/(2*Y)) + (((-11)*X^2)/(2)) + ((1*X^2*W^2)/(2)) + ((1*X^2*Z)/(2)) + ((-2)*X^2*Y*a) + (((-3)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*W^2)/(2*Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-2)*X^3*a)/(Y)) + ((1*X^3*W^2*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + (((-9)*X^3)/(2)) + ((1*X^3*W^2)/(2)) + ((1*X^3*Z)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)) + ((2*X^4)/(Y^2)) + ((1*X^4*a)/(Y)) + (1*X^4*a^2) + (1*X^4*Y*a))*v 435=0 := by
  have h:=hv 243
  change (((1*W^2)/(Y^2)))*v 6 + ((1))*v 10 + (((1*W^2)/(Y^2)))*v 36 + ((1))*v 40 + (((1*W^2)/(Y^2)))*v 66 + ((1))*v 70 + (((1*W^2)/(Y^2)))*v 96 + ((1))*v 100 + (((1*W^2)/(Y^2)))*v 126 + ((1))*v 130 + (((1*W^2)/(Y^2)))*v 156 + ((1))*v 160 + (((1*W^2)/(Y^2)))*v 186 + ((1))*v 190 + (((1*W^2)/(Y^2)))*v 216 + ((1))*v 220 + ((1))*v 250 + (((1*W^2)/(Y^2)))*v 276 + (((1*W^2)/(Y^2)))*v 306 + ((1))*v 310 + (((1*W^2)/(Y^2)))*v 336 + ((1))*v 340 + (((1*W^2)/(Y^2)))*v 366 + ((1))*v 370 + (((1*W^2)/(Y^2)))*v 396 + ((1))*v 400 + (((1*W^2)/(Y^2)))*v 426 + ((1))*v 430 + (((1*W^2)/(Y^2)))*v 456 + ((1))*v 460 + (((1*W^2)/(Y^2)))*v 486 + ((1))*v 490=0 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*W^2)/(Y^2)))*p16 - ((1))*p31 - (((1*W^2)/(Y^2)))*p36 - ((1))*p43 - ((1))*p60 - ((1))*p88 - (((1*W^2)/(Y^2)))*p96 - ((1))*p98 - (((1*W^2)/(Y^2)))*p114 - (((1*W^2)/(Y^2)))*p115 - ((1))*p118 - (((1*W^2)/(Y^2)))*p127 - ((1))*p136 - (((1*W^2)/(Y^2)))*p143 - ((1))*p144 - ((1))*p193 - ((((-1)*Z)/(Y^2)))*p195 - (((1*X)/(Y^2)))*p198 - (((1*W^2)/(Y^2)))*p199 - (((1*X)/(Y^2)))*p202 - (((1*W^2)/(Y^2)))*p204 - ((1))*p205 - (((1*X)/(Y^2)))*p208 - ((((-1))/(Y^2)) + ((1*Z)/(Y^2)) + ((-1)) + ((-1)*X))*p230 - ((((-1)*X*W^2)/(Y^2*Z)))*p234 - (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*p235 - ((1))*p239 - ((1))*p246 - (((1*X*W^2)/(Y^2)))*p253 - ((2))*p256 - (((1*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*p257 - ((1))*p264 - (((1*W^2)/(Y^2)))*p269 - ((1))*p277 - (((1*W^2)/(Y^2)))*p309 - ((((-1)*X*W^2)/(Y^2)))*p310 - ((((-1)*X*W^2)/(Y^2)))*p322 - (((1*W^2)/(Y^2)))*p327 - ((((-1)*W^2)/(Y^2)))*p331 - (((1*W^2)/(Y^2)))*p332 - (((1*W^2)/(Y^2)))*p335 - (((1*W^2)/(Y^2)))*p341 - (((1*W^2)/(Y^2)))*p346 - ((((-1)*X*W^2)/(Y^2)))*p354 - ((((-1)*W^2)/(X*Y^2)))*p355 - (((1*W^2)/(Y^2)))*p356 - ((((-1))/(X)) + ((-2)))*p358

#print axioms residual_20

compact_residual_elimination
theorem residual_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X)) + ((-2)) + ((-1)*X) + ((-1)*X^2))*v 370 + ((((-1)*W^2)/(X^2*Y^2)) + ((1)/(X*Y^2)) + (((-2))/(X)) + (((-1))/(Y^2)) + ((1*W*b)/(Y^2)) + ((2*W^2)/(Y^2)) + ((1*a)/(Y)) + ((-1)*Y^2) + ((3*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X*a)/(Y)) + (3*X) + ((3*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^2*a)/(Y)) + (4*X^2) + (((-1)*X^3)/(Y^2)) + (1*X^3))*v 390 + (((1)/(2*X*Y^2)) + ((1*a)/(2*X*Y)) + ((1*Y*a)/(2*X)) + ((1*Y^2)/(2*X)) + (((-1))/(2*Y^2)) + (((-7))/(2)) + ((1*a^2)/(2)) + ((1*Y*a)/(2)) + ((1*X*W*b)/(Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + ((1*X*Z)/(2*Y^2)) + (((-1)*X*W^2*a)/(2*Y)) + ((1*X*Z*a)/(2*Y)) + ((-1)*X) + (1*X*a^2) + (((-1)*X*W^2)/(2)) + ((1*X*Z)/(2)) + ((-2)*X*Y^2) + (((-1)*X^2)/(2*Y^2)) + (((-3)*X^2*W^2)/(2*Y^2)) + (((-2)*X^2*a)/(Y)) + (((-1)*X^2*W^2*a)/(2*Y)) + ((9*X^2)/(2)) + (((-3)*X^2*a^2)/(2)) + (((-1)*X^2*W^2)/(2)) + ((-1)*X^2*Y*a) + ((1*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^3*a)/(2)) + (((-7)*X^3)/(Y^2)) + (((-1)*X^3*W^2)/(2*Y^2)) + ((1*X^3*Z)/(Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*W^2*a)/(2*Y)) + (3*X^3) + (((-3)*X^3*a^2)/(2)) + (((-1)*X^3*W^2)/(2)) + (((-5)*X^3*Y*a)/(2)) + ((-1)*X^3*Y^2) + (((-17)*X^4)/(2*Y^2)) + ((3*X^4*Z)/(2*Y^2)) + (((-2)*X^4*a)/(Y)) + ((1*X^4*Z*a)/(2*Y)) + (((-3)*X^4)/(2)) + (((-3)*X^4*a^2)/(2)) + ((1*X^4*Z)/(2)) + (((-5)*X^4*Y*a)/(2)) + ((-1)*X^4*Y^2) + (((-2)*X^5)/(Y^2)) + ((1*X^5*Z)/(2*Y^2)) + (((-3)*X^5*a)/(2*Y)) + ((1*X^5*Z*a)/(2*Y)) + (((-3)*X^5)/(2)) + (((-1)*X^5*a^2)/(2)) + ((1*X^5*Z)/(2)) + ((-1)*X^5*Y*a) + (((-1)*X^5*Y^2)/(2)))*v 435=0 := by
  have h:=hv 244
  change ((1))*v 20 + (((1*W^2)/(Y^2)))*v 24 + ((1))*v 50 + (((1*W^2)/(Y^2)))*v 54 + ((1))*v 80 + (((1*W^2)/(Y^2)))*v 84 + ((1))*v 110 + (((1*W^2)/(Y^2)))*v 114 + ((1))*v 140 + (((1*W^2)/(Y^2)))*v 144 + ((1))*v 170 + (((1*W^2)/(Y^2)))*v 174 + ((1))*v 200 + (((1*W^2)/(Y^2)))*v 204 + (((1*W^2)/(Y^2)))*v 234 + ((1))*v 260 + ((1))*v 290 + (((1*W^2)/(Y^2)))*v 294 + ((1))*v 320 + (((1*W^2)/(Y^2)))*v 324 + ((1))*v 350 + (((1*W^2)/(Y^2)))*v 354 + ((1))*v 380 + (((1*W^2)/(Y^2)))*v 384 + ((1))*v 410 + (((1*W^2)/(Y^2)))*v 414 + ((1))*v 440 + (((1*W^2)/(Y^2)))*v 444 + ((1))*v 470 + (((1*W^2)/(Y^2)))*v 474 + ((1))*v 500 + (((1*W^2)/(Y^2)))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1*W^2)/(Y^2)))*p0 - ((1))*p1 - ((1))*p21 - (((1*W^2)/(Y^2)))*p47 - ((1))*p64 - ((1))*p78 - ((1))*p92 - ((1))*p93 - (((1*W^2)/(Y^2)))*p104 - ((1))*p117 - (((2*W^2)/(Y^2)))*p126 - ((1))*p134 - (((1*W^2)/(Y^2)))*p152 - (((1*W^2)/(Y^2)))*p158 - ((1))*p164 - (((1*W^2)/(Y^2)))*p165 - (((1*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*p189 - ((1))*p192 - (((1*X)/(Y^2)))*p194 - (((-1)))*p195 - (((1*X)/(Y^2)))*p196 - (((1*X)/(Y^2)))*p198 - (((1*X)/(Y^2)))*p202 - ((1))*p219 - (((1*W^2)/(Y^2)))*p220 - (((1*W^2)/(Y^2)))*p224 - ((1))*p227 - (((1)/(Y^2)) + (((-1)*Z)/(Y^2)) + (1) + (1*X))*p230 - ((((-1)*X*W^2)/(Y^2*Z)))*p231 - (((2*X)/(Y^2)))*p236 - ((1))*p242 - (((1*W^2)/(Y^2)))*p252 - (((-2)))*p256 - ((((-1)*X)/(Y^2)) + ((1*X*Z)/(Y^2)))*p257 - (((1*W^2)/(Y^2)))*p263 - (((-1)*X))*p264 - (((1*W^2)/(Y^2)))*p267 - ((((-1)*X*W^2)/(Y^2)))*p274 - (((1*W^2)/(Y^2)))*p288 - (((1*W^2)/(Y^2)))*p293 - ((((-1)*X*W^2)/(Y^2)))*p313 - ((1))*p319 - ((1))*p330 - ((((-1)*W^2)/(Y^2)))*p335 - (((1*W^2)/(Y^2)))*p339 - (((1*W^2)/(Y^2)))*p342 - ((((-1)*W^2)/(X*Y^2)))*p353 - ((((-1)*W^2)/(X*Y^2)))*p354 - ((((-1)*X*W^2)/(Y^2)))*p355 - (((1*W^2)/(Y^2)))*p357 - ((1) + ((-1)*X) + ((-1)*X^2))*p358

#print axioms residual_21

compact_residual_elimination
theorem residual_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2)) + ((1*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 370 + (((1*W^2)/(X^3)) + (((-1))/(X^2)) + ((1*W^2)/(X^2)) + ((2*Y^2)/(X^2)) + ((3)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Y*a)/(X)) + ((1*Y^4)/(X)) + ((-4)) + (1*Z) + (1*Y*a) + ((-3)*Y^2) + ((-3)*X) + (1*X*Z) + (1*X*Y*a) + ((-5)*X*Y^2) + (1*X^2) + ((-1)*X^2*Y^2))*v 390 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + (((-1)*Y*a)/(2*X)) + ((3*Y^2)/(X)) + (((-1)*Y^2*a^2)/(2*X)) + (((-1)*Y^3*a)/(2*X)) + ((-1)*W*b) + ((1*W^2)/(2)) + (((-1)*Z)/(2)) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (1*Y^2) + ((-1)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + (2*Y^4) + (((-3)*X)/(2)) + ((3*X*W^2)/(2)) + (2*X*Y*a) + ((1*X*Y*W^2*a)/(2)) + (((-9)*X*Y^2)/(2)) + ((3*X*Y^2*a^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + (1*X*Y^3*a) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + ((15*X^2)/(2)) + ((1*X^2*W^2)/(2)) + ((-1)*X^2*Z) + ((1*X^2*Y*W^2*a)/(2)) + (((-9)*X^2*Y^2)/(2)) + ((3*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((5*X^2*Y^3*a)/(2)) + (1*X^2*Y^4) + ((19*X^3)/(2)) + (((-3)*X^3*Z)/(2)) + ((5*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2)) + ((3*X^3*Y^2)/(2)) + (2*X^3*Y^2*a^2) + (((-1)*X^3*Y^2*Z)/(2)) + (3*X^3*Y^3*a) + (1*X^3*Y^4) + (2*X^4) + (((-1)*X^4*Z)/(2)) + ((3*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2)) + ((3*X^4*Y^2)/(2)) + ((1*X^4*Y^2*a^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2)) + (1*X^4*Y^3*a) + ((1*X^4*Y^4)/(2)))*v 435=0 := by
  have h:=hv 245
  change ((1))*v 0 + ((1*W^2))*v 12 + ((1))*v 30 + ((1*W^2))*v 42 + ((1))*v 60 + ((1*W^2))*v 72 + ((1))*v 90 + ((1*W^2))*v 102 + ((1))*v 120 + ((1*W^2))*v 132 + ((1))*v 150 + ((1*W^2))*v 162 + ((1))*v 180 + ((1*W^2))*v 192 + ((1))*v 210 + ((1*W^2))*v 222 + ((1))*v 240 + ((1))*v 270 + ((1*W^2))*v 282 + ((1))*v 300 + ((1*W^2))*v 312 + ((1*W^2))*v 342 + ((1))*v 360 + ((1*W^2))*v 372 + ((1))*v 390 + ((1*W^2))*v 402 + ((1))*v 420 + ((1*W^2))*v 432 + ((1))*v 450 + ((1*W^2))*v 462 + ((1))*v 480 + ((1*W^2))*v 492=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p3 - ((1))*p4 - ((1))*p9 - ((1))*p10 - ((1))*p13 - ((1))*p15 - ((1))*p27 - ((1*W^2))*p37 - ((1*W^2))*p70 - ((1))*p77 - ((1))*p91 - ((1*W^2))*p113 - ((1))*p121 - ((1*W^2))*p124 - ((1))*p150 - ((1*W^2))*p170 - ((1*X))*p189 - ((1*X))*p194 - ((1))*p195 - (((-1)))*p230 - ((1))*p232 - ((1))*p233 - ((1))*p235 - ((1*X*W^2))*p253 - ((1*W^2))*p261 - ((1*Y^2))*p264 - ((1*W^2))*p268 - ((1*W^2))*p274 - ((1*W^2))*p299 - ((1*W^2))*p313 - ((1*W^2))*p335 - ((1*W^2))*p336 - ((1*W^2))*p352 - (((1*W^2)/(X^2)))*p354 - ((1*W^2))*p355 - ((1*Y^2) + (2*X*Y^2))*p358 - ((1*W^2))*p403 - ((1*W^2))*p404

#print axioms residual_22

compact_residual_elimination
theorem residual_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2)) + ((1*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 370 + ((((-1)*W^2)/(X^3)) + (((-4))/(X^2)) + (((-1)*W^2)/(X^2)) + ((1*Z)/(X^2)) + ((1*Y*a)/(X^2)) + (((-4)*Y^2)/(X^2)) + (((-5))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Z)/(X)) + ((2*Y*a)/(X)) + (((-3)*Y^2)/(X)) + (((-1)*Y^4)/(X)) + (1) + (2*X*Y^2))*v 390 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + ((3)/(2*X)) + ((3*Y*a)/(2*X)) + (((-4)*Y^2)/(X)) + ((1*Y^2*a^2)/(X)) + ((3*Y^3*a)/(2*X)) + ((1*Y^4)/(2*X)) + (8) + (1*W*b) + (((-1)*W^2)/(2)) + (((-1)*Z)/(2)) + (1*Y*a) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-2)*Y^2) + (2*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + (2*Y^3*a) + ((-1)*Y^4) + (10*X) + (((-3)*X*W^2)/(2)) + (((-3)*X*Z)/(2)) + (1*X*Y*a) + (((-1)*X*Y*W^2*a)/(2)) + (((-1)*X*Y*Z*a)/(2)) + ((11*X*Y^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + (((-1)*X*Y^2*Z)/(2)) + (2*X*Y^3*a) + ((3*X*Y^4)/(2)) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + (1*X^2) + (((-1)*X^2*W^2)/(2)) + (((-1)*X^2*Z)/(2)) + (2*X^2*Y*a) + (((-1)*X^2*Y*W^2*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2)) + ((9*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2)) + ((1*X^2*Y^3*a)/(2)) + ((1*X^2*Y^4)/(2)) + ((-2)*X^3) + ((-1)*X^3*Y*a) + ((-1)*X^3*Y^2*a^2) + ((-1)*X^3*Y^3*a))*v 435=0 := by
  have h:=hv 246
  change ((1))*v 0 + ((1*W^2))*v 18 + ((1))*v 30 + ((1*W^2))*v 48 + ((1))*v 60 + ((1*W^2))*v 78 + ((1))*v 90 + ((1*W^2))*v 108 + ((1))*v 120 + ((1*W^2))*v 138 + ((1))*v 150 + ((1*W^2))*v 168 + ((1*W^2))*v 198 + ((1))*v 210 + ((1*W^2))*v 228 + ((1))*v 240 + ((1))*v 270 + ((1*W^2))*v 288 + ((1))*v 300 + ((1*W^2))*v 318 + ((1))*v 330 + ((1*W^2))*v 348 + ((1))*v 360 + ((1*W^2))*v 378 + ((1))*v 390 + ((1*W^2))*v 408 + ((1))*v 420 + ((1*W^2))*v 438 + ((1))*v 450 + ((1*W^2))*v 468 + ((1))*v 480 + ((1*W^2))*v 498=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p3 - ((1))*p4 - ((1*W^2))*p8 - ((1))*p9 - ((1))*p10 - ((1))*p13 - ((1))*p15 - ((1))*p27 - ((1*W^2))*p58 - ((1))*p77 - ((1))*p91 - ((1*W^2))*p120 - ((1))*p121 - ((1))*p150 - ((1*W^2))*p180 - ((1*X))*p189 - ((2*X) + ((-1)*X*Z))*p194 - ((1))*p230 - ((1))*p232 - ((1))*p233 - ((1))*p235 - ((1*W^2))*p252 - ((1*W^2))*p262 - ((1*W^2))*p302 - ((1*W^2))*p310 - ((1*W^2))*p322 - ((1*Y^2))*p330 - ((1*W^2))*p331 - ((1*W^2))*p333 - (((-1)*W^2))*p335 - ((1*W^2))*p337 - ((1*W^2))*p353 - ((1*W^2))*p354 - (((1*W^2)/(X^2)))*p355 - (((1*Y^2)/(X^2)) + ((-1)*X*Y^2))*p358 - ((1*W^2))*p393 - ((1*W^2))*p394

#print axioms residual_23

compact_residual_elimination
theorem residual_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 248
  change (((1)/(X)))*v 0 + ((1))*v 5 + ((1))*v 15 + (((1)/(X)))*v 20 + (((1)/(X)))*v 30 + ((1))*v 35 + ((1))*v 45 + (((1)/(X)))*v 50 + (((1)/(X)))*v 60 + ((1))*v 65 + ((1))*v 75 + (((1)/(X)))*v 80 + (((1)/(X)))*v 90 + ((1))*v 95 + ((1))*v 105 + (((1)/(X)))*v 110 + (((1)/(X)))*v 120 + ((1))*v 125 + ((1))*v 135 + (((1)/(X)))*v 140 + (((1)/(X)))*v 150 + ((1))*v 155 + (((1)/(X)))*v 170 + ((1))*v 185 + ((1))*v 195 + (((1)/(X)))*v 200 + (((1)/(X)))*v 210 + ((1))*v 215 + ((1))*v 225 + (((1)/(X)))*v 230 + (((1)/(X)))*v 240 + ((1))*v 245 + ((1))*v 255 + (((1)/(X)))*v 260 + (((1)/(X)))*v 270 + ((1))*v 275 + ((1))*v 285 + (((1)/(X)))*v 290 + (((1)/(X)))*v 300 + ((1))*v 305 + ((1))*v 315 + (((1)/(X)))*v 320 + (((1)/(X)))*v 330 + ((1))*v 345 + (((1)/(X)))*v 360 + ((1))*v 365 + ((1))*v 375 + (((1)/(X)))*v 380 + (((1)/(X)))*v 390 + ((1))*v 395 + ((1))*v 405 + (((1)/(X)))*v 410 + (((1)/(X)))*v 420 + ((1))*v 425 + ((1))*v 435 + (((1)/(X)))*v 440 + (((1)/(X)))*v 450 + ((1))*v 455 + ((1))*v 465 + (((1)/(X)))*v 470 + (((1)/(X)))*v 480 + ((1))*v 485 + ((1))*v 495 + (((1)/(X)))*v 500=0 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p1 - ((1))*p2 - (((1)/(X)))*p3 - (((1)/(X)))*p4 - ((1))*p5 - ((1))*p6 - (((1)/(X)))*p9 - (((1)/(X)))*p10 - ((1))*p12 - (((1)/(X)))*p13 - (((1)/(X)))*p15 - (((1)/(X)))*p21 - (((1)/(X)))*p27 - ((1))*p35 - (((1)/(X)))*p64 - (((1)/(X)))*p77 - (((1)/(X)))*p78 - ((1))*p83 - ((1))*p89 - (((1)/(X)))*p91 - (((1)/(X)))*p92 - (((1)/(X)))*p93 - ((1))*p95 - ((1))*p99 - ((1))*p100 - ((1))*p102 - (((1)/(X)))*p117 - (((1)/(X)))*p121 - (((1*W^2)/(X*Y^2)))*p126 - ((1))*p131 - (((1)/(X)))*p134 - ((1))*p137 - ((1))*p138 - ((1))*p142 - ((((-1)*W^2)/(X*Y^2*Z)))*p143 - ((1))*p145 - ((1))*p147 - ((1))*p148 - (((1)/(X)))*p150 - ((1))*p154 - (((1)/(X)))*p156 - (((1)/(X)))*p164 - (((1)/(Y^2)) + (((-1)*Z)/(Y^2)) + (2))*p189 - (((3)/(Y^2)) + (3))*p194 - (((1)/(X*Y^2)))*p195 - (((1)/(Y^2)) + (1))*p196 - ((1))*p202 - ((1))*p208 - ((1))*p210 - (((1)/(X)))*p219 - (((1)/(X)))*p227 - (((1)/(X*Y^2)) + ((2)/(X)) + (1))*p230 - ((((-1)*W^2)/(Y^2*Z)))*p231 - (((1)/(X)))*p232 - (((1)/(X*Y^2)) + ((1)/(X)))*p233 - (((2)/(X)) + ((-1)))*p235 - (((1)/(Y^2)) + (1))*p236 - (((1)/(X)))*p242 - (((1*W^2)/(X*Y^2)))*p252 - ((1))*p254 - ((((-1))/(X)) + (((-1)*Y^2)/(X)))*p256 - ((((-1))/(Y^2)) + ((1*Z)/(Y^2)))*p257 - (((1*W^2)/(X*Y^2)))*p262 - ((1))*p273 - (((1*W^2)/(X*Y^2)))*p302 - ((1))*p304 - ((1))*p317 - (((1)/(X)) + ((-1)))*p319 - (((1*W^2)/(X*Y^2)))*p322 - (((1)/(X)) + ((-1)))*p330 - (((1*W^2)/(X*Y^2)))*p331 - ((((-2)*W^2)/(X*Y^2)) + ((1*W^2)/(Y^2)))*p335 - (((2)/(X)) + ((-1)))*p358

#print axioms residual_24

compact_residual_elimination
theorem residual_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(Y^2)) + ((1*Z)/(Y^2)) + ((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*v 390 + (((2*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(Y)) + (((-1)*X^3*Z*a)/(2*Y)) + (1*X^3) + (((-1)*X^3*Z)/(2)) + (((-1)*X^4)/(Y^2)) + ((1*X^4*Z)/(2*Y^2)) + (((-1)*X^4*a)/(Y)) + ((1*X^4*Z*a)/(2*Y)) + ((-1)*X^4) + ((1*X^4*Z)/(2)))*v 435=0 := by
  have h:=hv 249
  change ((1))*v 0 + ((1*X))*v 5 + ((1*X))*v 15 + ((1))*v 20 + ((1))*v 30 + ((1*X))*v 35 + ((1*X))*v 45 + ((1))*v 50 + ((1))*v 60 + ((1*X))*v 65 + ((1*X))*v 75 + ((1))*v 80 + ((1))*v 90 + ((1*X))*v 95 + ((1*X))*v 105 + ((1))*v 110 + ((1))*v 120 + ((1*X))*v 125 + ((1*X))*v 135 + ((1))*v 140 + ((1))*v 150 + ((1*X))*v 155 + ((1))*v 170 + ((1*X))*v 185 + ((1*X))*v 195 + ((1))*v 200 + ((1))*v 210 + ((1*X))*v 215 + ((1*X))*v 225 + ((1))*v 230 + ((1))*v 240 + ((1*X))*v 245 + ((1*X))*v 255 + ((1))*v 260 + ((1))*v 270 + ((1*X))*v 275 + ((1*X))*v 285 + ((1))*v 290 + ((1))*v 300 + ((1*X))*v 305 + ((1*X))*v 315 + ((1))*v 320 + ((1))*v 330 + ((1*X))*v 345 + ((1))*v 360 + ((1*X))*v 365 + ((1*X))*v 375 + ((1))*v 380 + ((1))*v 390 + ((1*X))*v 395 + ((1*X))*v 405 + ((1))*v 410 + ((1))*v 420 + ((1*X))*v 425 + ((1*X))*v 435 + ((1))*v 440 + ((1))*v 450 + ((1*X))*v 455 + ((1*X))*v 465 + ((1))*v 470 + ((1))*v 480 + ((1*X))*v 485 + ((1*X))*v 495 + ((1))*v 500=0 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p1 - ((1*X))*p2 - ((1))*p3 - ((1))*p4 - ((1*X))*p5 - ((1*X))*p6 - ((1))*p9 - ((1))*p10 - ((1*X))*p12 - ((1))*p13 - ((1))*p15 - ((1))*p21 - ((1))*p27 - ((1*X))*p35 - ((1))*p64 - ((1))*p77 - ((1))*p78 - ((1*X))*p83 - ((1*X))*p89 - ((1))*p91 - ((1))*p92 - ((1))*p93 - ((1*X))*p95 - ((1*X))*p99 - ((1*X))*p100 - ((1*X))*p102 - ((1))*p117 - ((1))*p121 - (((1*W^2)/(Y^2)))*p126 - ((1*X))*p131 - ((1))*p134 - ((1*X))*p137 - ((1*X))*p138 - ((1*X))*p142 - ((((-1)*W^2)/(Y^2*Z)))*p143 - ((1*X))*p145 - ((1*X))*p147 - ((1*X))*p148 - ((1))*p150 - ((1*X))*p154 - ((1))*p156 - ((1))*p164 - (((1*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (2*X))*p189 - (((3*X)/(Y^2)) + (3*X))*p194 - (((1)/(Y^2)))*p195 - (((1*X)/(Y^2)) + (1*X))*p196 - ((1*X))*p202 - ((1*X))*p208 - ((1*X))*p210 - ((1))*p219 - ((1))*p227 - (((1)/(Y^2)) + (2) + (1*X))*p230 - ((((-1)*X*W^2)/(Y^2*Z)))*p231 - ((1))*p232 - (((1)/(Y^2)) + (1))*p233 - ((2) + ((-1)*X))*p235 - (((1*X)/(Y^2)) + (1*X))*p236 - ((1))*p242 - (((1*W^2)/(Y^2)))*p252 - ((1*X))*p254 - (((-1)) + ((-1)*Y^2))*p256 - ((((-1)*X)/(Y^2)) + ((1*X*Z)/(Y^2)))*p257 - (((1*W^2)/(Y^2)))*p262 - ((1*X))*p273 - (((1*W^2)/(Y^2)))*p302 - ((1*X))*p304 - ((1*X))*p317 - ((1) + ((-1)*X))*p319 - (((1*W^2)/(Y^2)))*p322 - ((1) + ((-1)*X))*p330 - (((1*W^2)/(Y^2)))*p331 - ((((-2)*W^2)/(Y^2)) + ((1*X*W^2)/(Y^2)))*p335 - ((2) + ((-1)*X))*p358

#print axioms residual_25

compact_residual_elimination
theorem residual_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 370 + ((((-5))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + ((1)/(X)) + (((-1)*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*X)/(W^2)) + ((4*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((6)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((1*X)/(2*W^2)) + (((-1)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-2)*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-9)*X^4)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 250
  change ((1))*v 6 + ((1))*v 12 + ((1))*v 18 + ((1))*v 24 + ((1))*v 36 + ((1))*v 42 + ((1))*v 48 + ((1))*v 54 + ((1))*v 66 + ((1))*v 72 + ((1))*v 78 + ((1))*v 84 + ((1))*v 96 + ((1))*v 108 + ((1))*v 114 + ((1))*v 126 + ((1))*v 132 + ((1))*v 138 + ((1))*v 144 + ((1))*v 156 + ((1))*v 162 + ((1))*v 168 + ((1))*v 174 + ((1))*v 186 + ((1))*v 192 + ((1))*v 198 + ((1))*v 216 + ((1))*v 222 + ((1))*v 228 + ((1))*v 234 + ((1))*v 246 + ((1))*v 252 + ((1))*v 258 + ((1))*v 264 + ((1))*v 276 + ((1))*v 282 + ((1))*v 288 + ((1))*v 294 + ((1))*v 312 + ((1))*v 318 + ((1))*v 324 + ((1))*v 336 + ((1))*v 342 + ((1))*v 348 + ((1))*v 354 + ((1))*v 366 + ((1))*v 372 + ((1))*v 378 + ((1))*v 384 + ((1))*v 396 + ((1))*v 402 + ((1))*v 414 + ((1))*v 426 + ((1))*v 432 + ((1))*v 438 + ((1))*v 444 + ((1))*v 456 + ((1))*v 462 + ((1))*v 468 + ((1))*v 474 + ((1))*v 486 + ((1))*v 492 + ((1))*v 498 + ((1))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1))*p8 - ((1))*p16 - ((1))*p36 - ((1))*p37 - ((1))*p45 - ((1))*p46 - ((1))*p47 - ((1))*p58 - ((1))*p70 - ((1))*p96 - ((1))*p104 - ((1))*p109 - ((1))*p114 - ((1))*p115 - ((1))*p124 - ((1))*p126 - ((1))*p127 - ((1))*p152 - ((1))*p158 - ((1))*p162 - ((1))*p170 - ((1))*p180 - (((1*X)/(W^2)))*p189 - (((1*X)/(W^2)))*p194 - (((2*X)/(W^2)))*p198 - ((1))*p199 - (((2*X)/(W^2)))*p202 - ((1))*p204 - ((1))*p220 - ((1))*p224 - (((1)/(W^2)))*p235 - (((1*X)/(W^2)))*p236 - ((1))*p252 - ((1*X))*p253 - ((1))*p261 - ((1))*p262 - ((1))*p263 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p267 - ((1))*p268 - ((1))*p269 - ((1) + ((-1)*X))*p274 - ((1))*p288 - ((1))*p293 - ((1))*p299 - ((1))*p302 - ((1))*p309 - ((1) + ((-1)*X))*p310 - ((1) + ((-1)*X))*p313 - ((1) + ((-1)*X))*p322 - ((1))*p327 - (((1*Y^2)/(W^2)))*p330 - ((1))*p331 - ((1))*p332 - ((1))*p333 - ((1))*p336 - ((1))*p337 - ((1))*p339 - ((1))*p341 - ((1))*p342 - ((1))*p346 - ((1))*p352 - ((((-1))/(X)) + (1))*p353 - (((1)/(X^2)) + (((-1))/(X)) + (1) + ((-1)*X))*p354 - (((1)/(X^2)) + (((-1))/(X)) + (1) + ((-1)*X))*p355 - ((1))*p356 - ((1))*p357 - (((1*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394 - ((1))*p403 - ((1))*p404

#print axioms residual_26

compact_residual_elimination
theorem residual_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + (((2)/(X^3)) + ((1)/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((1*b)/(X*W)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-6))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((4*Y*a)/(W^2)) + (((-7)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-5)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-6)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-5))/(2*W^2)) + ((1*b)/(W)) + (1) + ((1*Z)/(W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + ((9*X)/(2*W^2)) + (((-1)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-4)*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((23*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(W^2)) + ((2*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((13*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-5)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((7*X^3*Y^3*a)/(2*W^2)) + ((3*X^3*Y^4)/(2*W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 251
  change (((1)/(X)))*v 0 + (((1)/(X)))*v 6 + ((1))*v 9 + (((1)/(X)))*v 12 + ((1))*v 15 + (((1)/(X)))*v 18 + ((1))*v 21 + ((1))*v 27 + (((1)/(X)))*v 30 + (((1)/(X)))*v 36 + ((1))*v 39 + (((1)/(X)))*v 42 + ((1))*v 45 + (((1)/(X)))*v 48 + ((1))*v 51 + ((1))*v 57 + (((1)/(X)))*v 60 + (((1)/(X)))*v 66 + ((1))*v 69 + (((1)/(X)))*v 72 + ((1))*v 75 + (((1)/(X)))*v 78 + ((1))*v 81 + ((1))*v 87 + (((1)/(X)))*v 90 + ((1))*v 99 + (((1)/(X)))*v 102 + (((1)/(X)))*v 108 + ((1))*v 111 + ((1))*v 117 + (((1)/(X)))*v 120 + (((1)/(X)))*v 126 + ((1))*v 129 + (((1)/(X)))*v 132 + ((1))*v 135 + (((1)/(X)))*v 138 + ((1))*v 141 + ((1))*v 147 + (((1)/(X)))*v 150 + (((1)/(X)))*v 156 + ((1))*v 159 + (((1)/(X)))*v 162 + ((1))*v 165 + (((1)/(X)))*v 168 + ((1))*v 171 + ((1))*v 177 + (((1)/(X)))*v 180 + (((1)/(X)))*v 186 + ((1))*v 189 + (((1)/(X)))*v 192 + ((1))*v 195 + ((1))*v 201 + (((1)/(X)))*v 210 + (((1)/(X)))*v 216 + ((1))*v 219 + (((1)/(X)))*v 222 + ((1))*v 225 + (((1)/(X)))*v 228 + ((1))*v 231 + ((1))*v 237 + (((1)/(X)))*v 240 + (((1)/(X)))*v 246 + ((1))*v 249 + (((1)/(X)))*v 252 + ((1))*v 255 + (((1)/(X)))*v 258 + ((1))*v 261 + ((1))*v 267 + (((1)/(X)))*v 270 + (((1)/(X)))*v 276 + ((1))*v 279 + (((1)/(X)))*v 282 + ((1))*v 285 + (((1)/(X)))*v 288 + ((1))*v 291 + ((1))*v 297 + (((1)/(X)))*v 306 + (((1)/(X)))*v 312 + ((1))*v 315 + (((1)/(X)))*v 318 + ((1))*v 321 + ((1))*v 327 + (((1)/(X)))*v 330 + (((1)/(X)))*v 336 + ((1))*v 339 + (((1)/(X)))*v 342 + ((1))*v 345 + (((1)/(X)))*v 348 + ((1))*v 351 + ((1))*v 357 + (((1)/(X)))*v 360 + (((1)/(X)))*v 366 + ((1))*v 369 + (((1)/(X)))*v 372 + ((1))*v 375 + (((1)/(X)))*v 378 + ((1))*v 381 + ((1))*v 387 + (((1)/(X)))*v 390 + (((1)/(X)))*v 396 + ((1))*v 399 + ((1))*v 405 + (((1)/(X)))*v 408 + ((1))*v 417 + (((1)/(X)))*v 420 + (((1)/(X)))*v 426 + ((1))*v 429 + (((1)/(X)))*v 432 + ((1))*v 435 + (((1)/(X)))*v 438 + ((1))*v 441 + ((1))*v 447 + (((1)/(X)))*v 450 + (((1)/(X)))*v 456 + ((1))*v 459 + (((1)/(X)))*v 462 + ((1))*v 465 + (((1)/(X)))*v 468 + ((1))*v 471 + ((1))*v 477 + (((1)/(X)))*v 480 + (((1)/(X)))*v 486 + ((1))*v 489 + (((1)/(X)))*v 492 + ((1))*v 495 + (((1)/(X)))*v 498 + ((1))*v 501 + ((1))*v 507=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p49:=pivot_49 X Y Z W a b hX hY hZ hW v hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p347:=pivot_347 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v hv
  have p365:=pivot_365 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p2 - (((1)/(X)))*p3 - (((1)/(X)))*p4 - ((1))*p5 - ((1))*p6 - (((1)/(X)))*p8 - (((1)/(X)))*p9 - (((1)/(X)))*p10 - (((1)/(X)))*p13 - (((1)/(X)))*p15 - (((1)/(X)))*p16 - ((1))*p26 - (((1)/(X)))*p27 - (((1)/(X)))*p36 - (((1)/(X)))*p37 - ((1))*p39 - (((1)/(X)))*p45 - (((1)/(X)))*p46 - ((1))*p49 - ((1))*p55 - (((1)/(X)))*p58 - ((1))*p65 - ((1))*p66 - ((1))*p69 - (((1)/(X)))*p70 - (((1)/(X)))*p77 - ((1))*p80 - ((1))*p83 - ((1))*p85 - ((1))*p87 - (((1)/(X*W^2)) + ((1)/(X)))*p91 - ((1))*p97 - ((1))*p102 - ((1))*p110 - (((1)/(X)))*p113 - (((1)/(X)))*p114 - (((1)/(X)))*p115 - ((1))*p116 - (((1)/(X)))*p120 - (((1)/(X*W^2)) + ((1)/(X)))*p121 - (((1)/(X)))*p124 - (((1)/(X)))*p126 - (((1)/(X)))*p127 - ((1))*p130 - ((1))*p131 - ((1))*p135 - ((1))*p137 - (((1)/(X)))*p143 - ((1))*p151 - ((1))*p153 - ((1))*p157 - ((1))*p159 - (((1)/(X)))*p162 - ((1))*p163 - ((1))*p166 - (((1)/(X)))*p170 - (((1)/(X)))*p180 - (((3)/(W^2)) + (1))*p189 - (((2)/(W^2)) + (3) + (((-1)*Z)/(W^2)))*p194 - (((1)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)))*p195 - ((1))*p196 - (((1)/(W^2)) + (1))*p198 - (((1)/(X)))*p199 - ((1))*p200 - ((1))*p201 - ((1))*p202 - (((1)/(X)))*p204 - (((1*Y^2)/(X*W^2)))*p205 - ((1))*p208 - ((1))*p211 - ((1))*p214 - (((1*Y^2)/(X*W^2)))*p219 - ((1))*p222 - ((((-2))/(X*W^2)) + ((1*Z)/(X*W^2)))*p230 - ((1))*p231 - (((1)/(X)) + (((-1)*Z)/(X*W^2)))*p232 - (((1)/(X)) + (((-1)*Z)/(X*W^2)))*p233 - (((2)/(X*W^2)) + ((2)/(X)) + ((-1)))*p235 - (((1)/(W^2)) + (1))*p236 - (((2)/(X)))*p252 - ((2))*p253 - (((1*Y^2)/(X*W^2)))*p256 - ((((-1))/(W^2)) + (1))*p257 - ((1))*p258 - ((1))*p259 - (((1)/(X)))*p261 - (((1)/(X)))*p262 - (((1*Y^2)/(X*W^2)))*p264 - ((1))*p265 - (((1)/(X)))*p268 - (((1)/(X)))*p269 - (((1)/(X)))*p274 - ((1))*p275 - ((1))*p278 - ((1))*p279 - ((1))*p281 - ((1))*p291 - ((1))*p298 - ((1))*p300 - (((1)/(X)))*p302 - ((1))*p306 - (((1)/(X)))*p309 - (((-1)))*p310 - ((1))*p318 - ((1))*p320 - (((1)/(X)) + ((-1)) + (1*X))*p322 - (((1)/(X)))*p327 - ((1))*p329 - (((1)/(X)))*p332 - (((1)/(X)) + (1))*p333 - (((-1)))*p335 - (((-1)))*p336 - ((((-1))/(X)) + ((-1)))*p339 - (((1)/(X)) + ((-1)))*p341 - ((((-1))/(X)) + ((-1)))*p342 - ((1))*p345 - (((1)/(X)))*p346 - ((1))*p347 - ((1))*p351 - (((1)/(X)) + ((-1)))*p352 - (((1)/(X)) + ((-1)) + (1*X))*p354 - ((((-1))/(X^2)) + ((1)/(X)) + (1*X))*p355 - (((1)/(X)))*p356 - ((((-1))/(X)))*p357 - ((((-1)*Y^2)/(X^2*W^2)) + ((1*Y^2)/(W^2)))*p358 - ((1))*p364 - ((1))*p365 - (((1)/(X)))*p393 - ((1))*p395 - (((-1)))*p403 - (((-1)))*p404

#print axioms residual_27

compact_residual_elimination
theorem residual_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + ((((-2))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-10))/(X*W^2)) + ((3*b)/(X*W)) + ((4)/(X)) + ((2*Z)/(X*W^2)) + ((4*Y*a)/(X*W^2)) + (((-4)*Y^2)/(X*W^2)) + (((-2)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-11)*Y^2)/(2*X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + ((11)/(2*W^2)) + ((3*b)/(W)) + ((1*Z)/(W^2)) + ((5*Y*a)/(2*W^2)) + ((-1)*Y*a) + ((1*Y*Z*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(W^2)) + ((-1)*Y^2) + ((1*Y^2*Z)/(W^2)) + ((5*Y^3*a)/(2*W^2)) + (((-5)*Y^4)/(2*W^2)) + ((14*X)/(W^2)) + (((-7)*X)/(2)) + (((-3)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + ((6*X*Y^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((3*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + ((1*X*Y^4*a^2)/(W^2)) + ((1*X*Y^5*a)/(W^2)) + ((11*X^2)/(2*W^2)) + (((-5)*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((5*X^2*Y*a)/(2*W^2)) + (((-3)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(W^2)) + ((7*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-3)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(W^2)) + ((3*X^2*Y^3*a)/(W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 252
  change (((1)/(X)))*v 0 + ((1))*v 3 + ((1))*v 9 + (((1)/(X)))*v 12 + ((1))*v 15 + (((1)/(X)))*v 18 + ((1))*v 21 + (((1)/(X)))*v 24 + (((1)/(X)))*v 30 + ((1))*v 33 + ((1))*v 39 + (((1)/(X)))*v 42 + ((1))*v 45 + (((1)/(X)))*v 48 + ((1))*v 51 + (((1)/(X)))*v 54 + (((1)/(X)))*v 60 + ((1))*v 63 + ((1))*v 69 + (((1)/(X)))*v 72 + ((1))*v 75 + (((1)/(X)))*v 78 + ((1))*v 81 + (((1)/(X)))*v 84 + (((1)/(X)))*v 90 + ((1))*v 93 + (((1)/(X)))*v 102 + ((1))*v 105 + ((1))*v 111 + (((1)/(X)))*v 114 + (((1)/(X)))*v 120 + ((1))*v 123 + ((1))*v 129 + (((1)/(X)))*v 132 + ((1))*v 135 + (((1)/(X)))*v 138 + ((1))*v 141 + (((1)/(X)))*v 144 + (((1)/(X)))*v 150 + ((1))*v 153 + ((1))*v 159 + (((1)/(X)))*v 162 + ((1))*v 165 + (((1)/(X)))*v 168 + ((1))*v 171 + (((1)/(X)))*v 174 + (((1)/(X)))*v 180 + ((1))*v 183 + ((1))*v 189 + (((1)/(X)))*v 192 + ((1))*v 195 + (((1)/(X)))*v 198 + (((1)/(X)))*v 204 + ((1))*v 213 + ((1))*v 219 + (((1)/(X)))*v 222 + ((1))*v 225 + (((1)/(X)))*v 228 + ((1))*v 231 + (((1)/(X)))*v 234 + (((1)/(X)))*v 240 + ((1))*v 243 + ((1))*v 249 + (((1)/(X)))*v 252 + ((1))*v 255 + (((1)/(X)))*v 258 + ((1))*v 261 + (((1)/(X)))*v 264 + (((1)/(X)))*v 270 + ((1))*v 273 + ((1))*v 279 + (((1)/(X)))*v 282 + ((1))*v 285 + (((1)/(X)))*v 288 + ((1))*v 291 + (((1)/(X)))*v 294 + (((1)/(X)))*v 300 + ((1))*v 309 + ((1))*v 315 + (((1)/(X)))*v 318 + ((1))*v 321 + (((1)/(X)))*v 324 + (((1)/(X)))*v 330 + ((1))*v 333 + ((1))*v 339 + (((1)/(X)))*v 342 + ((1))*v 345 + (((1)/(X)))*v 348 + ((1))*v 351 + (((1)/(X)))*v 354 + (((1)/(X)))*v 360 + ((1))*v 363 + ((1))*v 369 + (((1)/(X)))*v 372 + ((1))*v 375 + (((1)/(X)))*v 378 + ((1))*v 381 + (((1)/(X)))*v 384 + (((1)/(X)))*v 390 + ((1))*v 393 + ((1))*v 399 + (((1)/(X)))*v 402 + (((1)/(X)))*v 408 + ((1))*v 411 + (((1)/(X)))*v 420 + ((1))*v 423 + ((1))*v 429 + (((1)/(X)))*v 432 + ((1))*v 435 + (((1)/(X)))*v 438 + ((1))*v 441 + (((1)/(X)))*v 444 + (((1)/(X)))*v 450 + ((1))*v 453 + ((1))*v 459 + (((1)/(X)))*v 462 + ((1))*v 465 + (((1)/(X)))*v 468 + ((1))*v 471 + (((1)/(X)))*v 474 + (((1)/(X)))*v 480 + ((1))*v 483 + ((1))*v 489 + (((1)/(X)))*v 492 + ((1))*v 495 + (((1)/(X)))*v 498 + ((1))*v 501 + (((1)/(X)))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p34:=pivot_34 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p315:=pivot_315 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p321:=pivot_321 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p363:=pivot_363 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p0 - ((1))*p2 - (((1)/(X)))*p3 - (((1)/(X)))*p4 - ((1))*p5 - ((1))*p6 - (((1)/(X)))*p8 - (((1)/(X)))*p9 - (((1)/(X)))*p10 - (((1)/(X)))*p13 - (((1)/(X)))*p15 - ((1))*p18 - (((1)/(X)))*p27 - ((1))*p34 - (((1)/(X)))*p37 - ((1))*p38 - (((1)/(X)))*p45 - (((1)/(X)))*p46 - (((1)/(X)))*p47 - ((1))*p54 - (((1)/(X)))*p58 - ((1))*p65 - ((1))*p66 - ((1))*p69 - (((1)/(X)))*p70 - ((1))*p74 - (((1)/(X)))*p77 - ((1))*p80 - ((1))*p83 - ((1))*p85 - ((1))*p87 - (((1)/(X*W^2)) + ((1)/(X)))*p91 - ((1))*p99 - ((1))*p103 - (((1)/(X)))*p109 - (((1)/(X)))*p113 - (((1)/(X)))*p114 - ((1))*p116 - (((1)/(X)))*p120 - (((1)/(X*W^2)))*p121 - (((1)/(X)))*p124 - (((2)/(X)))*p126 - ((1))*p130 - ((1))*p131 - ((1))*p135 - ((1))*p137 - ((1))*p146 - (((1)/(X)))*p150 - ((1))*p151 - (((1)/(X)))*p152 - ((1))*p153 - ((1))*p157 - (((1)/(X)))*p158 - ((1))*p161 - ((1))*p163 - (((1)/(X)))*p165 - (((1)/(X)))*p170 - (((1)/(X)))*p180 - (((2)/(W^2)) + (2))*p189 - (((3)/(W^2)) + (3) + (((-1)*Z)/(W^2)))*p194 - (((1)/(X)))*p195 - ((1))*p196 - ((1))*p198 - ((1))*p201 - (((1)/(W^2)) + (1))*p202 - (((1*Y^2)/(X*W^2)))*p205 - ((1))*p208 - ((1))*p211 - ((1))*p214 - (((1*Y^2)/(X*W^2)))*p219 - (((1)/(X)))*p220 - ((1))*p222 - ((1))*p223 - (((1)/(X)))*p224 - (((2)/(X*W^2)) + (((-1)*Z)/(X*W^2)))*p230 - (((1)/(X)) + (((-1)*Z)/(X*W^2)))*p232 - (((1)/(X)) + (((-1)*Z)/(X*W^2)))*p233 - ((1))*p234 - (((1)/(X*W^2)) + ((1)/(X)) + ((-1)))*p235 - (((2)/(W^2)) + (1))*p236 - (((2)/(X)))*p252 - ((2))*p253 - ((((-1)*Y^2)/(X*W^2)))*p256 - (((1)/(W^2)) + ((-1)))*p257 - ((1))*p258 - ((1))*p259 - (((1)/(X)) + (1))*p261 - (((1)/(X)))*p262 - (((1)/(X)))*p263 - (((1*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p264 - ((1))*p265 - (((1)/(X)))*p267 - (((1)/(X)))*p268 - (((1)/(X)) + ((-1)))*p274 - ((1))*p276 - ((1))*p278 - ((1))*p279 - ((1))*p284 - (((1)/(X)))*p288 - ((1))*p291 - (((1)/(X)))*p293 - ((1))*p297 - ((1))*p298 - (((1)/(X)))*p299 - ((1))*p301 - (((-1)))*p302 - ((1))*p306 - (((-1)))*p313 - ((1))*p315 - ((1))*p318 - ((1))*p321 - (((1)/(X)) + (1*X))*p322 - ((((-1))/(X)))*p327 - ((1))*p329 - (((-1)))*p331 - (((1)/(X)))*p333 - ((1))*p335 - (((-1)))*p337 - (((1)/(X)) + ((-1)))*p339 - ((((-1))/(X)) + ((-1)))*p341 - (((1)/(X)) + ((-1)))*p342 - ((1))*p345 - ((((-1))/(X)))*p346 - ((1))*p350 - ((((-1))/(X^2)) + ((1)/(X)) + ((-1)))*p353 - ((((-1))/(X^2)) + ((1)/(X)) + (1*X))*p354 - (((1)/(X)) + ((-1)) + (1*X))*p355 - ((((-1))/(X)))*p356 - (((1)/(X)))*p357 - (((2*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p358 - ((1))*p363 - (((1)/(X)) + ((-1)))*p393 - (((-1)))*p394 - ((1))*p395

#print axioms residual_28

compact_residual_elimination
theorem residual_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 370 + ((((-2))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-3))/(X)) + (((-4)*Y^2)/(X*W^2)) + (((-10))/(W^2)) + ((3*b)/(W)) + (4) + ((2*Z)/(W^2)) + ((4*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-2)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + (1*X) + ((3*X*Y*a)/(W^2)) + (((-4)*X*Y^2)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-11)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((11*X)/(2*W^2)) + ((3*X*b)/(W)) + ((1*X*Z)/(W^2)) + ((5*X*Y*a)/(2*W^2)) + ((-1)*X*Y*a) + ((1*X*Y*Z*a)/(W^2)) + (((-4)*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(W^2)) + ((-1)*X*Y^2) + ((1*X*Y^2*Z)/(W^2)) + ((5*X*Y^3*a)/(2*W^2)) + (((-5)*X*Y^4)/(2*W^2)) + ((14*X^2)/(W^2)) + (((-7)*X^2)/(2)) + (((-3)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((6*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(2)) + ((3*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(W^2)) + ((1*X^2*Y^5*a)/(W^2)) + ((11*X^3)/(2*W^2)) + (((-5)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(W^2)) + ((7*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-3)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((3*X^3*Y^4)/(2*W^2)) + ((1*X^3*Y^4*a^2)/(2*W^2)) + ((1*X^3*Y^5*a)/(2*W^2)) + ((5*X^4)/(2*W^2)) + (((-1)*X^4)/(2)) + (((-1)*X^4*Z)/(W^2)) + (((-1)*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*a)/(2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2)/(2)) + ((1*X^4*Y^4)/(2*W^2)) + ((2*X^5)/(W^2)) + (((-1)*X^5*Z)/(2*W^2)) + ((3*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y*Z*a)/(2*W^2)) + ((3*X^5*Y^2)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^2*Z)/(2*W^2)) + ((1*X^5*Y^3*a)/(W^2)) + ((1*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 253
  change ((1))*v 0 + ((1*X))*v 3 + ((1*X))*v 9 + ((1))*v 12 + ((1*X))*v 15 + ((1))*v 18 + ((1*X))*v 21 + ((1))*v 24 + ((1))*v 30 + ((1*X))*v 33 + ((1*X))*v 39 + ((1))*v 42 + ((1*X))*v 45 + ((1))*v 48 + ((1*X))*v 51 + ((1))*v 54 + ((1))*v 60 + ((1*X))*v 63 + ((1*X))*v 69 + ((1))*v 72 + ((1*X))*v 75 + ((1))*v 78 + ((1*X))*v 81 + ((1))*v 84 + ((1))*v 90 + ((1*X))*v 93 + ((1))*v 102 + ((1*X))*v 105 + ((1*X))*v 111 + ((1))*v 114 + ((1))*v 120 + ((1*X))*v 123 + ((1*X))*v 129 + ((1))*v 132 + ((1*X))*v 135 + ((1))*v 138 + ((1*X))*v 141 + ((1))*v 144 + ((1))*v 150 + ((1*X))*v 153 + ((1*X))*v 159 + ((1))*v 162 + ((1*X))*v 165 + ((1))*v 168 + ((1*X))*v 171 + ((1))*v 174 + ((1))*v 180 + ((1*X))*v 183 + ((1*X))*v 189 + ((1))*v 192 + ((1*X))*v 195 + ((1))*v 198 + ((1))*v 204 + ((1*X))*v 213 + ((1*X))*v 219 + ((1))*v 222 + ((1*X))*v 225 + ((1))*v 228 + ((1*X))*v 231 + ((1))*v 234 + ((1))*v 240 + ((1*X))*v 243 + ((1*X))*v 249 + ((1))*v 252 + ((1*X))*v 255 + ((1))*v 258 + ((1*X))*v 261 + ((1))*v 264 + ((1))*v 270 + ((1*X))*v 273 + ((1*X))*v 279 + ((1))*v 282 + ((1*X))*v 285 + ((1))*v 288 + ((1*X))*v 291 + ((1))*v 294 + ((1))*v 300 + ((1*X))*v 309 + ((1*X))*v 315 + ((1))*v 318 + ((1*X))*v 321 + ((1))*v 324 + ((1))*v 330 + ((1*X))*v 333 + ((1*X))*v 339 + ((1))*v 342 + ((1*X))*v 345 + ((1))*v 348 + ((1*X))*v 351 + ((1))*v 354 + ((1))*v 360 + ((1*X))*v 363 + ((1*X))*v 369 + ((1))*v 372 + ((1*X))*v 375 + ((1))*v 378 + ((1*X))*v 381 + ((1))*v 384 + ((1))*v 390 + ((1*X))*v 393 + ((1*X))*v 399 + ((1))*v 402 + ((1))*v 408 + ((1*X))*v 411 + ((1))*v 420 + ((1*X))*v 423 + ((1*X))*v 429 + ((1))*v 432 + ((1*X))*v 435 + ((1))*v 438 + ((1*X))*v 441 + ((1))*v 444 + ((1))*v 450 + ((1*X))*v 453 + ((1*X))*v 459 + ((1))*v 462 + ((1*X))*v 465 + ((1))*v 468 + ((1*X))*v 471 + ((1))*v 474 + ((1))*v 480 + ((1*X))*v 483 + ((1*X))*v 489 + ((1))*v 492 + ((1*X))*v 495 + ((1))*v 498 + ((1*X))*v 501 + ((1))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p34:=pivot_34 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p315:=pivot_315 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p321:=pivot_321 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p363:=pivot_363 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((1*X))*p2 - ((1))*p3 - ((1))*p4 - ((1*X))*p5 - ((1*X))*p6 - ((1))*p8 - ((1))*p9 - ((1))*p10 - ((1))*p13 - ((1))*p15 - ((1*X))*p18 - ((1))*p27 - ((1*X))*p34 - ((1))*p37 - ((1*X))*p38 - ((1))*p45 - ((1))*p46 - ((1))*p47 - ((1*X))*p54 - ((1))*p58 - ((1*X))*p65 - ((1*X))*p66 - ((1*X))*p69 - ((1))*p70 - ((1*X))*p74 - ((1))*p77 - ((1*X))*p80 - ((1*X))*p83 - ((1*X))*p85 - ((1*X))*p87 - (((1)/(W^2)) + (1))*p91 - ((1*X))*p99 - ((1*X))*p103 - ((1))*p109 - ((1))*p113 - ((1))*p114 - ((1*X))*p116 - ((1))*p120 - (((1)/(W^2)))*p121 - ((1))*p124 - ((2))*p126 - ((1*X))*p130 - ((1*X))*p131 - ((1*X))*p135 - ((1*X))*p137 - ((1*X))*p146 - ((1))*p150 - ((1*X))*p151 - ((1))*p152 - ((1*X))*p153 - ((1*X))*p157 - ((1))*p158 - ((1*X))*p161 - ((1*X))*p163 - ((1))*p165 - ((1))*p170 - ((1))*p180 - (((2*X)/(W^2)) + (2*X))*p189 - (((3*X)/(W^2)) + (3*X) + (((-1)*X*Z)/(W^2)))*p194 - ((1))*p195 - ((1*X))*p196 - ((1*X))*p198 - ((1*X))*p201 - (((1*X)/(W^2)) + (1*X))*p202 - (((1*Y^2)/(W^2)))*p205 - ((1*X))*p208 - ((1*X))*p211 - ((1*X))*p214 - (((1*Y^2)/(W^2)))*p219 - ((1))*p220 - ((1*X))*p222 - ((1*X))*p223 - ((1))*p224 - (((2)/(W^2)) + (((-1)*Z)/(W^2)))*p230 - ((1) + (((-1)*Z)/(W^2)))*p232 - ((1) + (((-1)*Z)/(W^2)))*p233 - ((1*X))*p234 - (((1)/(W^2)) + (1) + ((-1)*X))*p235 - (((2*X)/(W^2)) + (1*X))*p236 - ((2))*p252 - ((2*X))*p253 - ((((-1)*Y^2)/(W^2)))*p256 - (((1*X)/(W^2)) + ((-1)*X))*p257 - ((1*X))*p258 - ((1*X))*p259 - ((1) + (1*X))*p261 - ((1))*p262 - ((1))*p263 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p264 - ((1*X))*p265 - ((1))*p267 - ((1))*p268 - ((1) + ((-1)*X))*p274 - ((1*X))*p276 - ((1*X))*p278 - ((1*X))*p279 - ((1*X))*p284 - ((1))*p288 - ((1*X))*p291 - ((1))*p293 - ((1*X))*p297 - ((1*X))*p298 - ((1))*p299 - ((1*X))*p301 - (((-1)*X))*p302 - ((1*X))*p306 - (((-1)*X))*p313 - ((1*X))*p315 - ((1*X))*p318 - ((1*X))*p321 - ((1) + (1*X^2))*p322 - (((-1)))*p327 - ((1*X))*p329 - (((-1)*X))*p331 - ((1))*p333 - ((1*X))*p335 - (((-1)*X))*p337 - ((1) + ((-1)*X))*p339 - (((-1)) + ((-1)*X))*p341 - ((1) + ((-1)*X))*p342 - ((1*X))*p345 - (((-1)))*p346 - ((1*X))*p350 - ((((-1))/(X)) + (1) + ((-1)*X))*p353 - ((((-1))/(X)) + (1) + (1*X^2))*p354 - ((1) + ((-1)*X) + (1*X^2))*p355 - (((-1)))*p356 - ((1))*p357 - (((2*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*p358 - ((1*X))*p363 - ((1) + ((-1)*X))*p393 - (((-1)*X))*p394 - ((1*X))*p395

#print axioms residual_29

compact_residual_elimination
theorem residual_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 370 + (((2)/(X^2)) + ((1)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-4))/(W^2)) + ((1*b)/(W)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-6)*X)/(W^2)) + (1*X) + ((1*X*Z)/(W^2)) + ((4*X*Y*a)/(W^2)) + (((-7)*X*Y^2)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-5)*X^2)/(W^2)) + ((2*X^2*Z)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-6)*X^2*Y^2)/(W^2)) + ((2*X^3)/(W^2)) + (((-2)*X^3*Y^2)/(W^2)))*v 390 + ((((-1))/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((2*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-5)*X)/(2*W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X*Z)/(W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((9*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-4)*X^2*Y^2)/(W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((23*X^3)/(2*W^2)) + (((-3)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((5*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((5*X^3*Y^3*a)/(W^2)) + ((2*X^3*Y^4)/(W^2)) + ((1*X^3*Y^4*a^2)/(2*W^2)) + ((1*X^3*Y^5*a)/(2*W^2)) + ((13*X^4)/(W^2)) + (((-1)*X^4)/(2)) + (((-5)*X^4*Z)/(2*W^2)) + ((2*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((2*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((7*X^4*Y^3*a)/(2*W^2)) + ((3*X^4*Y^4)/(2*W^2)) + ((4*X^5)/(W^2)) + (((-1)*X^5*Z)/(W^2)) + ((3*X^5*Y*a)/(W^2)) + (((-1)*X^5*Y*Z*a)/(W^2)) + ((3*X^5*Y^2)/(W^2)) + ((1*X^5*Y^2*a^2)/(W^2)) + (((-1)*X^5*Y^2*Z)/(W^2)) + ((2*X^5*Y^3*a)/(W^2)) + ((1*X^5*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 254
  change ((1))*v 0 + ((1))*v 6 + ((1*X))*v 9 + ((1))*v 12 + ((1*X))*v 15 + ((1))*v 18 + ((1*X))*v 21 + ((1*X))*v 27 + ((1))*v 30 + ((1))*v 36 + ((1*X))*v 39 + ((1))*v 42 + ((1*X))*v 45 + ((1))*v 48 + ((1*X))*v 51 + ((1*X))*v 57 + ((1))*v 60 + ((1))*v 66 + ((1*X))*v 69 + ((1))*v 72 + ((1*X))*v 75 + ((1))*v 78 + ((1*X))*v 81 + ((1*X))*v 87 + ((1))*v 90 + ((1*X))*v 99 + ((1))*v 102 + ((1))*v 108 + ((1*X))*v 111 + ((1*X))*v 117 + ((1))*v 120 + ((1))*v 126 + ((1*X))*v 129 + ((1))*v 132 + ((1*X))*v 135 + ((1))*v 138 + ((1*X))*v 141 + ((1*X))*v 147 + ((1))*v 150 + ((1))*v 156 + ((1*X))*v 159 + ((1))*v 162 + ((1*X))*v 165 + ((1))*v 168 + ((1*X))*v 171 + ((1*X))*v 177 + ((1))*v 180 + ((1))*v 186 + ((1*X))*v 189 + ((1))*v 192 + ((1*X))*v 195 + ((1*X))*v 201 + ((1))*v 210 + ((1))*v 216 + ((1*X))*v 219 + ((1))*v 222 + ((1*X))*v 225 + ((1))*v 228 + ((1*X))*v 231 + ((1*X))*v 237 + ((1))*v 240 + ((1))*v 246 + ((1*X))*v 249 + ((1))*v 252 + ((1*X))*v 255 + ((1))*v 258 + ((1*X))*v 261 + ((1*X))*v 267 + ((1))*v 270 + ((1))*v 276 + ((1*X))*v 279 + ((1))*v 282 + ((1*X))*v 285 + ((1))*v 288 + ((1*X))*v 291 + ((1*X))*v 297 + ((1))*v 306 + ((1))*v 312 + ((1*X))*v 315 + ((1))*v 318 + ((1*X))*v 321 + ((1*X))*v 327 + ((1))*v 330 + ((1))*v 336 + ((1*X))*v 339 + ((1))*v 342 + ((1*X))*v 345 + ((1))*v 348 + ((1*X))*v 351 + ((1*X))*v 357 + ((1))*v 360 + ((1))*v 366 + ((1*X))*v 369 + ((1))*v 372 + ((1*X))*v 375 + ((1))*v 378 + ((1*X))*v 381 + ((1*X))*v 387 + ((1))*v 390 + ((1))*v 396 + ((1*X))*v 399 + ((1*X))*v 405 + ((1))*v 408 + ((1*X))*v 417 + ((1))*v 420 + ((1))*v 426 + ((1*X))*v 429 + ((1))*v 432 + ((1*X))*v 435 + ((1))*v 438 + ((1*X))*v 441 + ((1*X))*v 447 + ((1))*v 450 + ((1))*v 456 + ((1*X))*v 459 + ((1))*v 462 + ((1*X))*v 465 + ((1))*v 468 + ((1*X))*v 471 + ((1*X))*v 477 + ((1))*v 480 + ((1))*v 486 + ((1*X))*v 489 + ((1))*v 492 + ((1*X))*v 495 + ((1))*v 498 + ((1*X))*v 501 + ((1*X))*v 507=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p49:=pivot_49 X Y Z W a b hX hY hZ hW v hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p347:=pivot_347 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v hv
  have p365:=pivot_365 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1*X))*p2 - ((1))*p3 - ((1))*p4 - ((1*X))*p5 - ((1*X))*p6 - ((1))*p8 - ((1))*p9 - ((1))*p10 - ((1))*p13 - ((1))*p15 - ((1))*p16 - ((1*X))*p26 - ((1))*p27 - ((1))*p36 - ((1))*p37 - ((1*X))*p39 - ((1))*p45 - ((1))*p46 - ((1*X))*p49 - ((1*X))*p55 - ((1))*p58 - ((1*X))*p65 - ((1*X))*p66 - ((1*X))*p69 - ((1))*p70 - ((1))*p77 - ((1*X))*p80 - ((1*X))*p83 - ((1*X))*p85 - ((1*X))*p87 - (((1)/(W^2)) + (1))*p91 - ((1*X))*p97 - ((1*X))*p102 - ((1*X))*p110 - ((1))*p113 - ((1))*p114 - ((1))*p115 - ((1*X))*p116 - ((1))*p120 - (((1)/(W^2)) + (1))*p121 - ((1))*p124 - ((1))*p126 - ((1))*p127 - ((1*X))*p130 - ((1*X))*p131 - ((1*X))*p135 - ((1*X))*p137 - ((1))*p143 - ((1*X))*p151 - ((1*X))*p153 - ((1*X))*p157 - ((1*X))*p159 - ((1))*p162 - ((1*X))*p163 - ((1*X))*p166 - ((1))*p170 - ((1))*p180 - (((3*X)/(W^2)) + (1*X))*p189 - (((2*X)/(W^2)) + (3*X) + (((-1)*X*Z)/(W^2)))*p194 - (((1)/(W^2)) + (1) + (((-1)*Z)/(W^2)))*p195 - ((1*X))*p196 - (((1*X)/(W^2)) + (1*X))*p198 - ((1))*p199 - ((1*X))*p200 - ((1*X))*p201 - ((1*X))*p202 - ((1))*p204 - (((1*Y^2)/(W^2)))*p205 - ((1*X))*p208 - ((1*X))*p211 - ((1*X))*p214 - (((1*Y^2)/(W^2)))*p219 - ((1*X))*p222 - ((((-2))/(W^2)) + ((1*Z)/(W^2)))*p230 - ((1*X))*p231 - ((1) + (((-1)*Z)/(W^2)))*p232 - ((1) + (((-1)*Z)/(W^2)))*p233 - (((2)/(W^2)) + (2) + ((-1)*X))*p235 - (((1*X)/(W^2)) + (1*X))*p236 - ((2))*p252 - ((2*X))*p253 - (((1*Y^2)/(W^2)))*p256 - ((((-1)*X)/(W^2)) + (1*X))*p257 - ((1*X))*p258 - ((1*X))*p259 - ((1))*p261 - ((1))*p262 - (((1*Y^2)/(W^2)))*p264 - ((1*X))*p265 - ((1))*p268 - ((1))*p269 - ((1))*p274 - ((1*X))*p275 - ((1*X))*p278 - ((1*X))*p279 - ((1*X))*p281 - ((1*X))*p291 - ((1*X))*p298 - ((1*X))*p300 - ((1))*p302 - ((1*X))*p306 - ((1))*p309 - (((-1)*X))*p310 - ((1*X))*p318 - ((1*X))*p320 - ((1) + ((-1)*X) + (1*X^2))*p322 - ((1))*p327 - ((1*X))*p329 - ((1))*p332 - ((1) + (1*X))*p333 - (((-1)*X))*p335 - (((-1)*X))*p336 - (((-1)) + ((-1)*X))*p339 - ((1) + ((-1)*X))*p341 - (((-1)) + ((-1)*X))*p342 - ((1*X))*p345 - ((1))*p346 - ((1*X))*p347 - ((1*X))*p351 - ((1) + ((-1)*X))*p352 - ((1) + ((-1)*X) + (1*X^2))*p354 - ((((-1))/(X)) + (1) + (1*X^2))*p355 - ((1))*p356 - (((-1)))*p357 - ((((-1)*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p358 - ((1*X))*p364 - ((1*X))*p365 - ((1))*p393 - ((1*X))*p395 - (((-1)*X))*p403 - (((-1)*X))*p404

#print axioms residual_30

compact_residual_elimination
theorem residual_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 255
  change ((1))*v 5 + ((1))*v 25 + ((1))*v 35 + ((1))*v 55 + ((1))*v 65 + ((1))*v 95 + ((1))*v 115 + ((1))*v 125 + ((1))*v 145 + ((1))*v 155 + ((1))*v 175 + ((1))*v 185 + ((1))*v 205 + ((1))*v 215 + ((1))*v 235 + ((1))*v 245 + ((1))*v 265 + ((1))*v 275 + ((1))*v 295 + ((1))*v 305 + ((1))*v 325 + ((1))*v 335 + ((1))*v 355 + ((1))*v 365 + ((1))*v 385 + ((1))*v 395 + ((1))*v 415 + ((1))*v 445 + ((1))*v 455 + ((1))*v 475 + ((1))*v 485 + ((1))*v 505=0 at h
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  have p44:=pivot_44 X Y Z W a b hX hY hZ hW v hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v hv
  have p132:=pivot_132 X Y Z W a b hX hY hZ hW v hv
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p149:=pivot_149 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p215:=pivot_215 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p250:=pivot_250 X Y Z W a b hX hY hZ hW v hv
  have p251:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p323:=pivot_323 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p35 - ((1))*p44 - ((1))*p82 - ((1))*p89 - ((1))*p90 - ((1))*p95 - ((1))*p100 - ((1))*p101 - ((1))*p105 - ((1))*p111 - ((1))*p132 - ((1))*p138 - ((1))*p141 - ((1))*p142 - ((((-1)*W^2)/(X*Y^2*Z)))*p143 - ((1))*p145 - ((1))*p147 - ((1))*p148 - ((1))*p149 - ((1))*p154 - ((1))*p155 - ((((-1)*W^2)/(X*Y^2*Z)))*p165 - (((1)/(Y^2)))*p194 - (((2)/(X*Y^2)))*p195 - ((1))*p210 - ((1))*p215 - (((1)/(X*Y^2)))*p232 - (((1)/(X*Y^2)))*p233 - (((1)/(X*Y^2)))*p235 - ((1))*p250 - ((1))*p251 - ((1))*p254 - ((1))*p255 - (((1*W^2)/(X*Y^2)))*p262 - (((1*W^2)/(X*Y^2)))*p268 - ((1))*p273 - (((1*W^2)/(X*Y^2)))*p274 - (((-1)))*p277 - ((1))*p294 - (((1*W^2)/(X*Y^2)))*p299 - (((1*W^2)/(X*Y^2)))*p302 - ((1))*p304 - ((1))*p317 - (((-1)))*p319 - (((1*W^2)/(X*Y^2)))*p322 - ((1))*p323 - (((-1)))*p330 - (((1*W^2)/(X*Y^2)) + ((1*W^2)/(Y^2)))*p331 - (((1)/(X)))*p358 - ((1))*p359

#print axioms residual_31

compact_residual_elimination
theorem residual_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((2*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + (((5)/(X^3*W^2)) + ((1)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((2*Y^2)/(X^3*W^2)) + (((-1))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-6))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-6)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-2))/(X^2*W^2)) + (((-3)*Y*a)/(2*X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(2*X^2*W^2)) + (((-3)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-7))/(X*W^2)) + ((1*Z)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-3))/(W^2)) + ((2*b)/(W)) + ((1)/(2)) + ((2*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-2)*Y^4)/(W^2)) + ((6*X)/(W^2)) + ((-2)*X) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((5*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((3*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((5*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((7*X^2*Y^3*a)/(2*W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((9*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-2)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((3*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 256
  change ((1))*v 3 + ((1))*v 9 + ((1))*v 21 + ((1))*v 27 + ((1))*v 33 + ((1))*v 39 + ((1))*v 57 + ((1))*v 63 + ((1))*v 69 + ((1))*v 81 + ((1))*v 87 + ((1))*v 93 + ((1))*v 99 + ((1))*v 111 + ((1))*v 117 + ((1))*v 123 + ((1))*v 129 + ((1))*v 141 + ((1))*v 147 + ((1))*v 159 + ((1))*v 171 + ((1))*v 177 + ((1))*v 183 + ((1))*v 189 + ((1))*v 201 + ((1))*v 207 + ((1))*v 213 + ((1))*v 219 + ((1))*v 231 + ((1))*v 237 + ((1))*v 243 + ((1))*v 249 + ((1))*v 261 + ((1))*v 267 + ((1))*v 273 + ((1))*v 279 + ((1))*v 291 + ((1))*v 297 + ((1))*v 303 + ((1))*v 309 + ((1))*v 321 + ((1))*v 327 + ((1))*v 333 + ((1))*v 339 + ((1))*v 351 + ((1))*v 363 + ((1))*v 369 + ((1))*v 381 + ((1))*v 387 + ((1))*v 393 + ((1))*v 399 + ((1))*v 411 + ((1))*v 417 + ((1))*v 423 + ((1))*v 429 + ((1))*v 441 + ((1))*v 447 + ((1))*v 453 + ((1))*v 471 + ((1))*v 477 + ((1))*v 483 + ((1))*v 489 + ((1))*v 501 + ((1))*v 507=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v hv
  have p34:=pivot_34 X Y Z W a b hX hY hZ hW v hv
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p49:=pivot_49 X Y Z W a b hX hY hZ hW v hv
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p315:=pivot_315 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v hv
  have p321:=pivot_321 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p324:=pivot_324 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p347:=pivot_347 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p363:=pivot_363 X Y Z W a b hX hY hZ hW v hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v hv
  have p365:=pivot_365 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p18 - ((1))*p26 - ((1))*p34 - ((1))*p38 - ((1))*p39 - ((1))*p49 - ((1))*p54 - ((1))*p55 - ((1))*p65 - ((1))*p66 - ((1))*p69 - ((1))*p74 - ((1))*p80 - ((1))*p85 - ((1))*p87 - (((1)/(X*W^2)))*p91 - ((1))*p97 - ((1))*p103 - ((1))*p110 - (((1)/(X)))*p114 - ((1))*p116 - (((1)/(X*W^2)))*p121 - (((1)/(X)))*p126 - ((1))*p146 - ((1))*p151 - ((1))*p153 - ((1))*p157 - ((1))*p159 - ((1))*p161 - ((1))*p163 - ((1))*p166 - (((2)/(W^2)))*p189 - (((2)/(W^2)))*p194 - (((1)/(X*W^2)))*p195 - ((1))*p200 - ((1))*p201 - (((1*Y^2)/(X*W^2)))*p205 - ((1))*p211 - ((1))*p214 - (((1*Y^2)/(X*W^2)))*p219 - ((1))*p222 - ((1))*p223 - (((2)/(X*W^2)))*p235 - (((1)/(W^2)))*p236 - (((1)/(X)))*p252 - ((1))*p253 - ((1))*p258 - ((1))*p259 - ((1))*p265 - ((1))*p272 - ((1))*p275 - ((1))*p276 - ((1))*p278 - ((1))*p279 - ((1))*p281 - ((1))*p284 - ((1))*p291 - ((1))*p297 - ((1))*p298 - ((1))*p300 - ((1))*p301 - (((-1)))*p302 - ((1))*p306 - ((((-1))/(X)))*p310 - ((((-1))/(X)))*p313 - ((1))*p315 - ((1))*p318 - ((1))*p320 - ((1))*p321 - ((1*X))*p322 - ((1))*p324 - ((((-1))/(X)))*p327 - ((1))*p329 - ((((-1)*Y^2)/(X*W^2)))*p330 - ((((-1))/(X)) + ((-1)))*p331 - ((((-1))/(X)) + ((-1)))*p336 - ((((-1))/(X)) + ((-1)))*p337 - ((((-1))/(X)) + ((-1)))*p339 - ((((-1))/(X)) + ((-1)))*p341 - ((((-1))/(X)) + ((-1)))*p342 - ((1))*p345 - ((((-1))/(X)))*p346 - ((1))*p347 - ((1))*p350 - ((1))*p351 - (((-1)))*p352 - (((-1)))*p353 - ((((-1))/(X^3)) + (1*X))*p354 - ((((-1))/(X^3)) + (1*X))*p355 - ((((-1))/(X)))*p356 - ((((-1))/(X)))*p357 - ((((-1)*Y^2)/(X^3*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p358 - ((1))*p363 - ((1))*p364 - ((1))*p365 - (((-1)))*p393 - ((((-1))/(X)) + ((-1)))*p394 - ((1))*p395 - ((((-1))/(X)) + ((-1)))*p403 - ((((-1))/(X)) + ((-1)))*p404

#print axioms residual_32

compact_residual_elimination
theorem residual_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^2*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-3)*Y^2)/(W^2)) + (((-2)*X*Y^2)/(W^2)) + (((-4)*X^2*Y^2)/(W^2)))*v 370 + ((((-5))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((8)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((3)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((7*X^2)/(W^2)) + (((-2)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-2)*X^3)/(W^2)) + ((2*X^3*Y^2)/(W^2)))*v 390 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((9)/(2*W^2)) + (((-1)*Z)/(W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-15)*X)/(2*W^2)) + ((1*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-21)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-4)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-2)*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-9)*X^3)/(W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-2)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-4)*X^3*Y^3*a)/(W^2)) + (((-2)*X^3*Y^4)/(W^2)) + (((-12)*X^4)/(W^2)) + ((5*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-3)*X^4*Y^4)/(2*W^2)) + (((-4)*X^5)/(W^2)) + ((1*X^5*Z)/(W^2)) + (((-3)*X^5*Y*a)/(W^2)) + ((1*X^5*Y*Z*a)/(W^2)) + (((-3)*X^5*Y^2)/(W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^2*Z)/(W^2)) + (((-2)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 257
  change ((2))*v 0 + ((2))*v 6 + ((1))*v 12 + ((1))*v 18 + ((2))*v 24 + ((2))*v 30 + ((2))*v 36 + ((1))*v 42 + ((1))*v 54 + ((2))*v 60 + ((2))*v 66 + ((1))*v 72 + ((1))*v 78 + ((2))*v 84 + ((2))*v 90 + ((2))*v 96 + ((1))*v 102 + ((1))*v 108 + ((2))*v 114 + ((2))*v 120 + ((2))*v 126 + ((1))*v 132 + ((1))*v 138 + ((2))*v 144 + ((1))*v 150 + ((1))*v 156 + ((1))*v 162 + ((1))*v 168 + ((2))*v 174 + ((2))*v 180 + ((2))*v 186 + ((1))*v 192 + ((1))*v 198 + ((2))*v 204 + ((2))*v 210 + ((2))*v 216 + ((1))*v 222 + ((1))*v 228 + ((2))*v 234 + ((2))*v 240 + ((2))*v 246 + ((1))*v 252 + ((1))*v 258 + ((2))*v 264 + ((2))*v 270 + ((2))*v 276 + ((1))*v 282 + ((1))*v 288 + ((2))*v 294 + ((2))*v 300 + ((2))*v 306 + ((1))*v 312 + ((1))*v 318 + ((2))*v 324 + ((2))*v 330 + ((2))*v 336 + ((1))*v 342 + ((1))*v 348 + ((1))*v 354 + ((1))*v 360 + ((2))*v 366 + ((1))*v 372 + ((1))*v 378 + ((2))*v 384 + ((2))*v 390 + ((2))*v 396 + ((1))*v 402 + ((1))*v 408 + ((2))*v 414 + ((2))*v 420 + ((2))*v 426 + ((1))*v 432 + ((1))*v 438 + ((2))*v 444 + ((2))*v 450 + ((1))*v 456 + ((1))*v 468 + ((2))*v 474 + ((2))*v 480 + ((2))*v 486 + ((1))*v 492 + ((1))*v 498 + ((2))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((2))*p0 - ((2))*p3 - ((2))*p4 - ((1))*p8 - ((2))*p9 - ((2))*p10 - ((2))*p13 - ((2))*p15 - ((2))*p16 - ((2))*p27 - ((2))*p36 - ((1))*p37 - ((1))*p45 - ((1))*p46 - ((2))*p47 - ((1))*p58 - ((1))*p70 - ((2))*p77 - ((2))*p91 - ((2))*p96 - ((2))*p104 - ((2))*p109 - ((1))*p113 - ((2))*p114 - ((2))*p115 - ((1))*p120 - ((2))*p121 - ((1))*p124 - ((2))*p126 - ((2))*p127 - ((2))*p143 - ((2))*p150 - ((2))*p152 - ((2))*p158 - ((2))*p162 - ((2))*p165 - ((1))*p170 - ((1))*p180 - (((2*X)/(W^2)) + (2*X))*p189 - (((1*X)/(W^2)) + (2*X) + (((-1)*X*Z)/(W^2)))*p194 - ((2) + (((-2)*Z)/(W^2)))*p195 - (((4*X)/(W^2)))*p198 - ((2))*p199 - (((4*X)/(W^2)))*p202 - ((2))*p204 - ((2))*p220 - ((2))*p224 - ((1))*p232 - ((1))*p233 - (((2)/(W^2)) + (2))*p235 - (((2*X)/(W^2)))*p236 - ((1))*p252 - ((1*X))*p253 - ((1))*p261 - ((1))*p263 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p264 - ((2))*p267 - ((1))*p269 - ((1) + ((-2)*X))*p274 - ((2))*p288 - ((1))*p293 - ((1))*p299 - ((1))*p302 - ((2))*p309 - ((1) + ((-2)*X))*p310 - ((1) + ((-2)*X))*p313 - ((1) + ((-2)*X))*p322 - ((2))*p327 - (((1*Y^2)/(W^2)))*p330 - ((1))*p331 - ((1))*p332 - ((1))*p333 - ((1))*p336 - ((1))*p337 - ((2))*p339 - ((2))*p341 - ((2))*p342 - ((2))*p346 - ((1))*p352 - ((((-1))/(X)) + (1))*p353 - (((1)/(X^2)) + (((-2))/(X)) + (1) + ((-2)*X))*p354 - (((1)/(X^2)) + (((-2))/(X)) + (1) + ((-2)*X))*p355 - ((2))*p356 - ((2))*p357 - (((1*Y^2)/(X^2*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394 - ((1))*p403 - ((1))*p404

#print axioms residual_33

compact_residual_elimination
theorem residual_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((2*Y^2)/(X^2*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-3)*Y^2)/(W^2)) + (((-2)*X*Y^2)/(W^2)) + (((-4)*X^2*Y^2)/(W^2)))*v 370 + ((((-5))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((8)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((3)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((7*X^2)/(W^2)) + (((-2)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-2)*X^3)/(W^2)) + ((2*X^3*Y^2)/(W^2)))*v 390 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((9)/(2*W^2)) + (((-1)*Z)/(W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-15)*X)/(2*W^2)) + ((1*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-21)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-4)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-2)*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-9)*X^3)/(W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-2)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-4)*X^3*Y^3*a)/(W^2)) + (((-2)*X^3*Y^4)/(W^2)) + (((-12)*X^4)/(W^2)) + ((5*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-3)*X^4*Y^4)/(2*W^2)) + (((-4)*X^5)/(W^2)) + ((1*X^5*Z)/(W^2)) + (((-3)*X^5*Y*a)/(W^2)) + ((1*X^5*Y*Z*a)/(W^2)) + (((-3)*X^5*Y^2)/(W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^2*Z)/(W^2)) + (((-2)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 258
  change ((2))*v 0 + ((2))*v 6 + ((1))*v 12 + ((1))*v 18 + ((2))*v 24 + ((2))*v 30 + ((2))*v 36 + ((1))*v 42 + ((1))*v 54 + ((2))*v 60 + ((2))*v 66 + ((1))*v 72 + ((1))*v 78 + ((2))*v 84 + ((2))*v 90 + ((2))*v 96 + ((1))*v 102 + ((1))*v 108 + ((2))*v 114 + ((2))*v 120 + ((2))*v 126 + ((1))*v 132 + ((1))*v 138 + ((2))*v 144 + ((1))*v 150 + ((1))*v 156 + ((1))*v 162 + ((1))*v 168 + ((2))*v 174 + ((2))*v 180 + ((2))*v 186 + ((1))*v 192 + ((1))*v 198 + ((2))*v 204 + ((2))*v 210 + ((2))*v 216 + ((1))*v 222 + ((1))*v 228 + ((2))*v 234 + ((2))*v 240 + ((2))*v 246 + ((1))*v 252 + ((1))*v 258 + ((2))*v 264 + ((2))*v 270 + ((2))*v 276 + ((1))*v 282 + ((1))*v 288 + ((2))*v 294 + ((2))*v 300 + ((2))*v 306 + ((1))*v 312 + ((1))*v 318 + ((2))*v 324 + ((2))*v 330 + ((2))*v 336 + ((1))*v 342 + ((1))*v 348 + ((1))*v 354 + ((1))*v 360 + ((2))*v 366 + ((1))*v 372 + ((1))*v 378 + ((2))*v 384 + ((2))*v 390 + ((2))*v 396 + ((1))*v 402 + ((1))*v 408 + ((2))*v 414 + ((2))*v 420 + ((2))*v 426 + ((1))*v 432 + ((1))*v 438 + ((2))*v 444 + ((2))*v 450 + ((1))*v 456 + ((1))*v 468 + ((2))*v 474 + ((2))*v 480 + ((2))*v 486 + ((1))*v 492 + ((1))*v 498 + ((2))*v 504=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((2))*p0 - ((2))*p3 - ((2))*p4 - ((1))*p8 - ((2))*p9 - ((2))*p10 - ((2))*p13 - ((2))*p15 - ((2))*p16 - ((2))*p27 - ((2))*p36 - ((1))*p37 - ((1))*p45 - ((1))*p46 - ((2))*p47 - ((1))*p58 - ((1))*p70 - ((2))*p77 - ((2))*p91 - ((2))*p96 - ((2))*p104 - ((2))*p109 - ((1))*p113 - ((2))*p114 - ((2))*p115 - ((1))*p120 - ((2))*p121 - ((1))*p124 - ((2))*p126 - ((2))*p127 - ((2))*p143 - ((2))*p150 - ((2))*p152 - ((2))*p158 - ((2))*p162 - ((2))*p165 - ((1))*p170 - ((1))*p180 - (((2*X)/(W^2)) + (2*X))*p189 - (((1*X)/(W^2)) + (2*X) + (((-1)*X*Z)/(W^2)))*p194 - ((2) + (((-2)*Z)/(W^2)))*p195 - (((4*X)/(W^2)))*p198 - ((2))*p199 - (((4*X)/(W^2)))*p202 - ((2))*p204 - ((2))*p220 - ((2))*p224 - ((1))*p232 - ((1))*p233 - (((2)/(W^2)) + (2))*p235 - (((2*X)/(W^2)))*p236 - ((1))*p252 - ((1*X))*p253 - ((1))*p261 - ((1))*p263 - (((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p264 - ((2))*p267 - ((1))*p269 - ((1) + ((-2)*X))*p274 - ((2))*p288 - ((1))*p293 - ((1))*p299 - ((1))*p302 - ((2))*p309 - ((1) + ((-2)*X))*p310 - ((1) + ((-2)*X))*p313 - ((1) + ((-2)*X))*p322 - ((2))*p327 - (((1*Y^2)/(W^2)))*p330 - ((1))*p331 - ((1))*p332 - ((1))*p333 - ((1))*p336 - ((1))*p337 - ((2))*p339 - ((2))*p341 - ((2))*p342 - ((2))*p346 - ((1))*p352 - ((((-1))/(X)) + (1))*p353 - (((1)/(X^2)) + (((-2))/(X)) + (1) + ((-2)*X))*p354 - (((1)/(X^2)) + (((-2))/(X)) + (1) + ((-2)*X))*p355 - ((2))*p356 - ((2))*p357 - (((1*Y^2)/(X^2*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394 - ((1))*p403 - ((1))*p404

#print axioms residual_34

compact_residual_elimination
theorem residual_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + (((-1))/(W^2)))*v 390 + ((((-1)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=0 := by
  have h:=hv 263
  change ((1))*v 9 + (((1)/(X)))*v 18 + ((1))*v 264=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p8 - ((1))*p69 - ((1))*p109 - (((1)/(W^2)))*p189 - ((((-1))/(W^2)) + ((1*X)/(W^2)))*p257

#print axioms residual_35

compact_residual_elimination
theorem residual_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2*W^2)) + (((-1))/(Y^2*W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)))*v 435=0 := by
  have h:=hv 267
  change ((1))*v 14 + (((1)/(X)))*v 28 + ((1))*v 269=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p167:=pivot_167 X Y Z W a b hX hY hZ hW v hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p30 - (((1)/(X)))*p167 - ((1))*p171 - (((1)/(Y^2*W^2)))*p189 - ((((-1))/(Y^2*W^2)) + ((1*X)/(Y^2*W^2)))*p257

#print axioms residual_36

compact_residual_elimination
theorem residual_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)) + (1))*v 390 + ((1*X) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 286
  change ((1))*v 45 + (((1)/(X)))*v 90 + ((1))*v 300=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p3 - ((1))*p150 - ((1*X))*p189 - ((1) + ((-1)*X))*p257

#print axioms residual_37

compact_residual_elimination
theorem residual_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((4)/(X*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(W^2)) + (((-1)*Y*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-7)*X)/(W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-2)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-11)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-3)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-5)*X^3)/(2*W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 290
  change ((1))*v 54 + (((1)/(X)))*v 108 + ((1))*v 309=0 at h
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - (((1)/(X)))*p302 - ((1))*p350 - ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p358

#print axioms residual_38

compact_residual_elimination
theorem residual_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 298
  change ((1))*v 70 + (((1)/(X)))*v 140 + ((1))*v 325=0 at h
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p264 - (((1)/(X)))*p358 - ((1))*p359

#print axioms residual_39

compact_residual_elimination
theorem residual_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)) + ((1)/(Y^2)))*v 390 + (((1*X)/(Y^2)) + (((-1)*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)))*v 435=0 := by
  have h:=hv 306
  change ((1))*v 80 + (((1)/(X)))*v 160 + ((1))*v 335=0 at h
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p251:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p92 - (((1*X)/(Y^2)))*p189 - (((1)/(X)))*p193 - ((((-1))/(X)))*p230 - ((1))*p251 - (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*p257

#print axioms residual_40

compact_residual_elimination
theorem residual_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Z)/(X*Y^2)) + ((1*Z)/(Y^2)))*v 390 + (((1*X*Z)/(Y^2)) + (((-1)*X^2*Z)/(2*Y^2)) + ((1*X^2*Z*a)/(2*Y)) + ((1*X^2*Z)/(2)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 311
  change ((1))*v 85 + (((1)/(X)))*v 170 + ((1))*v 340=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p11 - (((1)/(X)))*p117 - ((1))*p118 - ((((-1)*Z)/(Y^2)))*p189 - (((1*Z)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*p257

#print axioms residual_41

compact_residual_elimination
theorem residual_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)) + ((1)/(Y^2*W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)))*v 435=0 := by
  have h:=hv 312
  change ((1))*v 86 + (((1)/(X)))*v 172 + ((1))*v 341=0 at h
  have p59:=pivot_59 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p190:=pivot_190 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p59 - (((1*X)/(Y^2*W^2)))*p189 - (((1)/(X)))*p190 - ((1))*p248 - (((1)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)))*p257

#print axioms residual_42

compact_residual_elimination
theorem residual_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X)) + ((-1)))*v 390 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 328
  change ((1))*v 111 + (((1)/(X)))*v 222 + ((1))*v 366=0 at h
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p258 - (((1)/(X)))*p274 - ((1))*p333 - ((1))*p356

#print axioms residual_43

compact_residual_elimination
theorem residual_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)) + (1))*v 390 + ((1*X) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 350
  change ((1))*v 144 + (((1)/(X)))*v 288 + ((1))*v 399=0 at h
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p259 - ((1))*p261 - (((1)/(X)))*p322 - ((1))*p357

#print axioms residual_44

compact_residual_elimination
theorem residual_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 370 + ((((-4))/(X*W^2)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(W^2)) + ((1*Y*a)/(2*W^2)) + (((-3)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((7*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + ((11*X^2)/(2*W^2)) + (((-3)*X^2*Z)/(2*W^2)) + ((3*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 357
  change ((1))*v 156 + (((1)/(X)))*v 312 + ((1))*v 411=0 at h
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p103 - ((1))*p269 - (((1)/(X)))*p352 - (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*p358

#print axioms residual_45

compact_residual_elimination
theorem residual_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2*W^2)) + (((-1))/(Y^2*W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)))*v 435=0 := by
  have h:=hv 367
  change ((1))*v 169 + (((1)/(X)))*v 338 + ((1))*v 424=0 at h
  have p108:=pivot_108 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p191:=pivot_191 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p108 - (((1)/(Y^2*W^2)))*p121 - (((1)/(X)))*p191 - ((1))*p249 - ((((-1))/(Y^2*W^2)) + ((1*X)/(Y^2*W^2)))*p257

#print axioms residual_46

compact_residual_elimination
theorem residual_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X*Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + ((((-1)*X*Z)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + (((-1)*X^2*Z*a)/(2*Y)) + (((-1)*X^2*Z)/(2)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 368
  change ((1))*v 170 + (((1)/(X)))*v 340 + ((1))*v 425=0 at h
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p12 - ((1))*p117 - (((1)/(X)))*p118 - ((((-1)*X*Z)/(Y^2)))*p189 - ((((-1)*Z)/(Y^2)) + ((1*X*Z)/(Y^2)))*p257

#print axioms residual_47

compact_residual_elimination
theorem residual_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2)) + (((-1))/(Y^2)))*v 390 + ((((-1)*X)/(Y^2)) + ((1*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)) + ((1*X^3)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3)/(2)))*v 435=0 := by
  have h:=hv 373
  change ((1))*v 175 + (((1)/(X)))*v 350 + ((1))*v 430=0 at h
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p250:=pivot_250 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p88 - (((1)/(X)))*p192 - ((((-1))/(X)))*p195 - (((1)/(X)))*p230 - ((1))*p250 - ((((-1))/(Y^2)) + ((1*X)/(Y^2)))*p257

#print axioms residual_48

compact_residual_elimination
theorem residual_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)))*v 370 + (((1)/(X^2)) + ((2)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + (((-2)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 375
  change ((1))*v 177 + (((1)/(X)))*v 354 + ((1))*v 432=0 at h
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p347:=pivot_347 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p124 - ((1*X))*p253 - (((1)/(X)))*p293 - ((1))*p347 - ((((-1))/(X^2)))*p353

#print axioms residual_49

compact_residual_elimination
theorem residual_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + (((-3))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((5*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((1)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((4)/(W^2)) + ((2*b)/(W)) + ((1)/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((13*X)/(2*W^2)) + ((-2)*X) + (((-2)*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + ((5*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((4*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-7)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 383
  change ((1))*v 189 + (((1)/(X)))*v 378 + ((1))*v 444=0 at h
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p224 - (((-1)*X))*p274 - ((((-1)*X^2*Y^2)/(W^2)))*p358 - (((1)/(X)))*p393 - ((1))*p395

#print axioms residual_50

compact_residual_elimination
theorem residual_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 388
  change ((1))*v 201 + (((1)/(X)))*v 402 + ((1))*v 456=0 at h
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p299 - ((1))*p332 - ((1))*p351

#print axioms residual_51

compact_residual_elimination
theorem residual_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X)) + ((-1)))*v 390 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 391
  change ((1))*v 210 + (((1)/(X)))*v 420 + ((1))*v 465=0 at h
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p4 - ((1))*p121 - ((1))*p189 - (((-1)) + (1*X))*p257

#print axioms residual_52

compact_residual_elimination
theorem residual_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)) + ((1)/(Y^2*W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)))*v 435=0 := by
  have h:=hv 407
  change ((1))*v 241 + (((1)/(X)))*v 482 + ((1))*v 496=0 at h
  have p42:=pivot_42 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p178:=pivot_178 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p42 - (((1)/(X)))*p76 - (((1)/(Y^2)))*p116 - ((1))*p178 - (((1*X)/(Y^2*W^2)))*p189 - (((1)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)))*p257

#print axioms residual_53

compact_residual_elimination
theorem residual_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + ((1)/(W^2)))*v 390 + (((1*X)/(W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=0 := by
  have h:=hv 410
  change ((1))*v 246 + (((1)/(X)))*v 492 + ((1))*v 501=0 at h
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(X)))*p37 - ((1))*p85 - (((1)/(X*W^2)))*p121 - ((1))*p162 - (((1*X)/(W^2)))*p189 - (((1)/(W^2)) + (((-1)*X)/(W^2)))*p257

#print axioms residual_54

compact_residual_elimination
theorem residual_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 390 + (((1*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 415
  change ((1))*v 6 + ((((-1)*a)/(Y)))*v 18 + (((1)/(Y^2)))*v 54 + ((1))*v 176 + ((1))*v 346=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p370:=pivot_370 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*a)/(Y)))*p8 - ((1))*p36 - (((1)/(Y^2)))*p263 - ((((-1)*X)/(W^2)))*p264 - ((1))*p370

#print axioms residual_55

compact_residual_elimination
theorem residual_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 421
  change ((1))*v 14 + ((((-1)*a)/(Y)))*v 42 + (((1)/(Y^2)))*v 126 + ((1))*v 184 + ((1))*v 354=0 at h
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p171 - (((1*X)/(Y^2*W^2)))*p257 - ((((-1)*a)/(Y)))*p261 - ((1))*p293 - (((1)/(Y^2)))*p341 - ((1))*p349 - ((((-1))/(X)))*p353

#print axioms residual_56

compact_residual_elimination
theorem residual_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*a)/(X*Y)) + (((-1))/(Y^2)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 390 + ((((-1)*X)/(Y^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((-1)*X^2) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2)))*v 435=0 := by
  have h:=hv 422
  change ((1))*v 15 + ((((-1)*a)/(Y)))*v 45 + (((1)/(Y^2)))*v 135 + ((1))*v 185 + ((1))*v 355=0 at h
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p5 - (((1)/(Y^2)))*p196 - ((((-1)*a)/(Y)))*p257 - ((1))*p294 - ((1))*p317 - (((-1)))*p330

#print axioms residual_57

compact_residual_elimination
theorem residual_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((1)/(Y^2)) + (1))*v 390 + (((1)/(Y^2)) + ((1*X*a)/(Y)) + (1*X) + (((-1)*X^2)/(Y^2)))*v 435=0 := by
  have h:=hv 434
  change ((1))*v 35 + ((((-1)*a)/(Y)))*v 105 + ((1))*v 205 + (((1)/(Y^2)))*v 315 + ((1))*v 375=0 at h
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p323:=pivot_323 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*a)/(Y)))*p99 - ((1))*p142 - ((1))*p208 - (((1)/(X*Y^2)))*p233 - (((-1)))*p235 - (((1)/(Y^2)))*p236 - ((((-1))/(X)))*p256 - ((1))*p323

#print axioms residual_58

compact_residual_elimination
theorem residual_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)) + (1))*v 390 + ((1*X) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 441
  change ((1))*v 45 + ((((-1)*a)/(Y)))*v 135 + ((1))*v 215 + ((1))*v 385 + (((1)/(Y^2)))*v 405=0 at h
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p215:=pivot_215 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Y^2)))*p102 - ((1))*p154 - ((((-1)*a)/(Y)))*p196 - ((1))*p215 - (((1)/(X*Y^2)))*p235 - ((1))*p257 - (((1*W^2)/(X*Y^2)))*p262 - (((-1)))*p277 - (((1*W^2)/(Y^2)))*p331 - ((((-1)*W^2)/(Y^2)))*p335

#print axioms residual_59

compact_residual_elimination
theorem residual_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)))*v 370 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*a)/(Y)) + (((-1)*X)/(W^2)))*v 390 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)))*v 435=0 := by
  have h:=hv 442
  change ((1))*v 48 + ((((-1)*a)/(Y)))*v 144 + ((1))*v 218 + ((1))*v 388 + (((1)/(Y^2)))*v 432=0 at h
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  have p373:=pivot_373 X Y Z W a b hX hY hZ hW v hv
  have p385:=pivot_385 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Y^2)))*p124 - (((1*X)/(Y^2)))*p253 - ((1))*p262 - ((1))*p328 - ((((-1)*a)/(Y)))*p357 - ((((-1))/(X)))*p373 - (((-1)))*p385

#print axioms residual_60

compact_residual_elimination
theorem residual_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y*a)/(X^2*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*v 370 + ((((-1)*a)/(X^3*Y)) + ((1)/(X^2*Y^2*W^2)) + ((2*a)/(X^2*Y*W^2)) + ((1*a*b)/(X^2*Y*W)) + ((3*a)/(X^2*Y)) + ((2*Y*a)/(X^2*W^2)) + ((1)/(X*Y^2*W^2)) + ((4*a)/(X*Y*W^2)) + (((-2)*a*b)/(X*Y*W)) + (((-2)*a)/(X*Y)) + (((-1)*Z*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + (((-2)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((4)/(Y^2*W^2)) + (((-1))/(Y^2)) + (((-1)*Z)/(Y^2*W^2)) + ((2*a)/(Y*W^2)) + (((-1)*a)/(Y)) + ((2)/(W^2)) + (((-3)*a^2)/(W^2)) + ((4*Y*a)/(W^2)) + ((1*Y^3*a)/(W^2)) + ((1*X)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + ((3*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X^2*a)/(Y*W^2)) + ((1*X^2*Z*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^3*a)/(Y*W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)))*v 390 + (((1*a)/(2*X^2*Y*W^2)) + ((1*a^2)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + (((-1)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-3)*a)/(Y*W^2)) + (((-2)*a*b)/(Y*W)) + (((-1)*a)/(2*Y)) + (((-1)*Z*a)/(2*Y*W^2)) + ((1)/(W^2)) + (((-3)*a^2)/(2*W^2)) + ((1*a^2)/(2)) + (((-1)*Z*a^2)/(2*W^2)) + ((2*Y*a)/(W^2)) + (((-3)*Y*a^3)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-7)*X*a)/(Y*W^2)) + ((2*X*a)/(Y)) + ((2*X*Z*a)/(Y*W^2)) + ((3*X)/(2*W^2)) + (((-5)*X*a^2)/(2*W^2)) + (((-7)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^3*a^3)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-7)*X^2)/(Y^2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + (((-5)*X^2*a)/(Y*W^2)) + ((2*X^2*a)/(Y)) + ((1*X^2*Z*a)/(2*Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*a^2)/(W^2)) + (1*X^2*a^2) + ((1*X^2*Z*a^2)/(2*W^2)) + (((-5)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-5)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^3*a^3)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-11)*X^3)/(2*Y^2*W^2)) + ((3*X^3*Z)/(2*Y^2*W^2)) + (((-4)*X^3*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((3*X^3*Z*a)/(2*Y*W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-7)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-5)*X^4)/(2*Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + ((5*X^4*a)/(2*Y*W^2)) + (((-2)*X^4*a^2)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Z*a^2)/(2*W^2)) + (((-5)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^5)/(Y^2*W^2)) + ((3*X^5*a)/(2*Y*W^2)) + (((-1)*X^5*Z*a)/(2*Y*W^2)) + ((1*X^5*a^2)/(W^2)) + (((-1)*X^5*Z*a^2)/(2*W^2)) + ((1*X^5*Y*a)/(W^2)) + ((1*X^5*Y*a^3)/(2*W^2)) + (((-1)*X^5*Y*Z*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 446
  change (((1)/(Y^2)))*v 57 + ((1))*v 63 + ((((-1)*a)/(Y)))*v 189 + ((1))*v 233 + ((1))*v 403=0 at h
  have p181:=pivot_181 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p395:=pivot_395 X Y Z W a b hX hY hZ hW v hv
  have p398:=pivot_398 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p181 - (((1)/(Y^2*W^2)))*p236 - ((((-1))/(X*W^2)))*p256 - (((1)/(Y^2)))*p275 - ((1))*p276 - (((-1)))*p337 - ((((-1))/(X*Y^2)))*p339 - ((((-1))/(X)))*p341 - ((((-1))/(Y^2)))*p352 - ((((-1)*X)/(W^2)))*p358 - ((((-1)*a)/(Y)))*p395 - ((1))*p398

#print axioms residual_61

compact_residual_elimination
theorem residual_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2)) + ((1*a)/(Y)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 390 + ((((-1)*X)/(Y^2)) + (((-1)*X^2*a)/(Y)) + ((-1)*X^2) + ((1*X^3)/(Y^2)))*v 435=0 := by
  have h:=hv 449
  change ((1))*v 70 + (((1)/(Y^2)))*v 120 + ((((-1)*a)/(Y)))*v 210 + ((1))*v 240 + ((1))*v 410=0 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p27 - ((1))*p78 - ((((-1)*a)/(Y)))*p121 - (((1*X)/(Y^2)))*p196 - (((1)/(Y^2)))*p235 - ((((-1)*X*a)/(Y)))*p257 - ((1))*p264

#print axioms residual_62

compact_residual_elimination
theorem residual_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 370 + (((1)/(X*Y^2)) + ((2)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 390 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 457
  change ((1))*v 79 + (((1)/(Y^2)))*v 201 + ((((-1)*a)/(Y)))*v 237 + ((1))*v 249 + ((1))*v 419=0 at h
  have p20:=pivot_20 X Y Z W a b hX hY hZ hW v hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p387:=pivot_387 X Y Z W a b hX hY hZ hW v hv
  have p388:=pivot_388 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p20 - ((((-1)*a)/(Y)))*p159 - ((1))*p163 - ((((-1)*a)/(X*Y*W^2)))*p195 - (((1*a)/(X*Y*W^2)))*p230 - ((1))*p285 - (((1)/(Y^2)))*p351 - ((((-1))/(X)))*p387 - (((-1)))*p388

#print axioms residual_63

compact_residual_elimination
theorem residual_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X)/(W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^3)/(Y^2*W^2)))*v 435=0 := by
  have h:=hv 459
  change ((1))*v 82 + (((1)/(Y^2)))*v 228 + ((((-1)*a)/(Y)))*v 246 + ((1))*v 252 + ((1))*v 422=0 at h
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p57:=pivot_57 X Y Z W a b hX hY hZ hW v hv
  have p67:=pivot_67 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p45 - ((1))*p57 - ((1))*p67 - (((1)/(W^2)))*p98 - ((((-1)*a)/(Y)))*p162 - (((1*X)/(Y^2)))*p166 - (((1)/(Y^2)))*p180 - ((((-1)*X*a)/(Y*W^2)))*p189 - (((1*X)/(Y^2*W^2)))*p208 - ((((-1)*X)/(Y^2*W^2)))*p235 - (((1*X*a)/(Y*W^2)))*p257 - (((1)/(W^2)))*p330

#print axioms residual_64

compact_residual_elimination
theorem residual_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^3)/(Y^2*W^2)))*v 435=0 := by
  have h:=hv 460
  change ((1))*v 88 + ((1))*v 258 + ((((-1)*a)/(Y)))*v 264 + (((1)/(Y^2)))*v 282 + ((1))*v 428=0 at h
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p56:=pivot_56 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p46 - ((1))*p56 - (((1)/(W^2)))*p78 - ((((-1)*a)/(Y)))*p109 - ((1))*p123 - (((1)/(Y^2)))*p170 - (((1*X)/(Y^2*W^2)))*p196 - (((1)/(Y^2*W^2)))*p235 - ((((-1)*X*a)/(Y*W^2)))*p257 - (((1)/(W^2)))*p264

#print axioms residual_65

compact_residual_elimination
theorem residual_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 370 + (((4)/(X*Y^2*W^2)) + (((-1))/(X*Y^2)) + (((-1)*Z)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((2)/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1)*Z)/(Y^2*W^2)) + ((3)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 390 + ((((-1))/(Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + ((3)/(2*W^2)) + (((-1)*a^2)/(2*W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-7)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + (((-2)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-13)*X^2)/(2*Y^2*W^2)) + ((3*X^2*Z)/(2*Y^2*W^2)) + (((-5)*X^2*a)/(2*Y*W^2)) + ((1*X^2*Z*a)/(2*Y*W^2)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2*Z)/(2*W^2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-5)*X^3)/(2*Y^2*W^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + (((-3)*X^3*a)/(2*Y*W^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*a^2)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=0 := by
  have h:=hv 462
  change ((1))*v 91 + ((1))*v 261 + ((((-1)*a)/(Y)))*v 273 + (((1)/(Y^2)))*v 309 + ((1))*v 431=0 at h
  have p17:=pivot_17 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p314:=pivot_314 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p370:=pivot_370 X Y Z W a b hX hY hZ hW v hv
  have p409:=pivot_409 X Y Z W a b hX hY hZ hW v hv
  have p410:=pivot_410 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p17 - ((1))*p80 - (((1)/(X*W^2)))*p91 - ((((-1)*a)/(Y)))*p146 - (((1)/(W^2)))*p194 - ((((-1)*a)/(X*Y*W^2)))*p230 - ((1))*p314 - (((1)/(Y^2)))*p350 - ((((-1))/(X*W^2)))*p358 - (((-1)))*p370 - ((1))*p409 - ((((-1))/(X)))*p410

#print axioms residual_66

compact_residual_elimination
theorem residual_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 370 + (((1)/(X*Y^2*W^2)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-2))/(W^2)) + ((1*X)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((3*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 465
  change ((1))*v 99 + ((1))*v 269 + ((((-1)*a)/(Y)))*v 297 + (((1)/(Y^2)))*v 381 + ((1))*v 439=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p316:=pivot_316 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v hv
  have p375:=pivot_375 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p30 - ((1))*p97 - ((((-1)*a)/(Y)))*p200 - (((1)/(Y^2)))*p211 - (((1*a)/(Y)))*p261 - ((1))*p316 - ((((-1))/(Y^2)))*p341 - (((-1)))*p349 - ((((-1))/(X)))*p375

#print axioms residual_67

compact_residual_elimination
theorem residual_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Y^2)) + (((-1)*a)/(Y)) + ((1*X)/(Y^2)) + (1*X))*v 390 + (((1*X)/(Y^2)) + ((1*X^2*a)/(Y)) + (1*X^2) + (((-1)*X^3)/(Y^2)))*v 435=0 := by
  have h:=hv 466
  change ((1))*v 100 + ((1))*v 270 + ((((-1)*a)/(Y)))*v 300 + (((1)/(Y^2)))*v 390 + ((1))*v 440=0 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p9 - ((1))*p98 - ((((-1)*a)/(Y)))*p150 - ((((-1)*X*a)/(Y)))*p189 - (((1*X)/(Y^2)))*p208 - ((((-1)*X)/(Y^2)))*p235 - (((1*X*a)/(Y)))*p257 - ((1))*p330

#print axioms residual_68

compact_residual_elimination
theorem residual_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)) + ((1)/(Y^2)))*v 390 + (((1*X)/(Y^2)) + (((-1)*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)))*v 435=0 := by
  have h:=hv 467
  change ((1))*v 101 + ((1))*v 271 + ((((-1)*a)/(Y)))*v 303 + (((1)/(Y^2)))*v 399 + ((1))*v 441=0 at h
  have p7:=pivot_7 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p371:=pivot_371 X Y Z W a b hX hY hZ hW v hv
  have p376:=pivot_376 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p7 - (((1)/(Y^2)))*p259 - (((1)/(Y^2)))*p261 - ((((-1)*a)/(Y)))*p272 - ((1))*p295 - ((1))*p318 - ((1*X))*p354 - (((-1)))*p371 - ((((-1))/(X)))*p376

#print axioms residual_69

compact_residual_elimination
theorem residual_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 370 + (((4)/(W^2)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + ((((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-7)*X^2)/(W^2)) + ((1*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-11)*X^3)/(2*W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-2)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-5)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-1)*X^5)/(W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 468
  change ((1))*v 108 + ((1))*v 278 + ((((-1)*a)/(Y)))*v 324 + ((1))*v 448 + (((1)/(Y^2)))*v 462=0 at h
  have p24:=pivot_24 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p377:=pivot_377 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p24 - ((((-1)*a)/(Y)))*p220 - (((1)/(Y^2)))*p268 - ((1))*p302 - (((1*X*a)/(Y)))*p355 - (((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p358 - ((1))*p377

#print axioms residual_70

compact_residual_elimination
theorem residual_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 469
  change (((1)/(Y^2)))*v 24 + ((1))*v 116 + ((1))*v 286 + ((((-1)*a)/(Y)))*v 348 + ((1))*v 456=0 at h
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p206:=pivot_206 X Y Z W a b hX hY hZ hW v hv
  have p229:=pivot_229 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p361:=pivot_361 X Y Z W a b hX hY hZ hW v hv
  have p378:=pivot_378 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Y^2)))*p126 - ((1))*p206 - (((-1)))*p229 - (((1*X)/(Y^2*W^2)))*p236 - ((((-1))/(W^2)))*p256 - ((1))*p332 - ((1))*p351 - ((((-1)*a)/(Y)))*p354 - ((1))*p361 - ((((-1))/(X)))*p378

#print axioms residual_71

compact_residual_elimination
theorem residual_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*a)/(X*Y)) + ((1*a)/(Y)))*v 390 + (((1*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 435=0 := by
  have h:=hv 470
  change (((1)/(Y^2)))*v 78 + ((1))*v 122 + ((1))*v 292 + ((((-1)*a)/(Y)))*v 366 + ((1))*v 462=0 at h
  have p209:=pivot_209 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p391:=pivot_391 X Y Z W a b hX hY hZ hW v hv
  have p392:=pivot_392 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p209 - (((1)/(Y^2)))*p252 - ((1))*p268 - ((((-1)*a)/(Y)))*p356 - (((1*Y*a)/(W^2)))*p358 - (((-1)))*p391 - ((1))*p392

#print axioms residual_72

compact_residual_elimination
theorem residual_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X)) + ((-1)))*v 390 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 471
  change (((1)/(Y^2)))*v 105 + ((1))*v 125 + ((1))*v 295 + ((((-1)*a)/(Y)))*v 375 + ((1))*v 465=0 at h
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p149:=pivot_149 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Y^2)))*p99 - ((1))*p149 - ((1))*p189 - ((((-1)*a)/(Y)))*p208 - ((1))*p210 - (((1*a)/(Y)))*p235 - (((-1)))*p257 - (((1*W^2)/(X*Y^2)))*p268 - (((-1)))*p319 - (((1*W^2)/(Y^2)))*p335

#print axioms residual_73

compact_residual_elimination
theorem residual_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1))/(W^2)))*v 390 + ((((-1))/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X^2)/(Y^2*W^2)))*v 435=0 := by
  have h:=hv 472
  change (((1)/(Y^2)))*v 114 + ((1))*v 126 + ((1))*v 296 + ((((-1)*a)/(Y)))*v 378 + ((1))*v 466=0 at h
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  have p369:=pivot_369 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  have p397:=pivot_397 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Y^2)))*p339 - ((1))*p341 - ((1))*p369 - ((((-1)*a)/(Y)))*p393 - ((1))*p397

#print axioms residual_74

compact_residual_elimination
theorem residual_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((1)/(Y^2*W^2)) + ((1)/(W^2)))*v 390 + (((1)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 435=0 := by
  have h:=hv 473
  change ((1))*v 129 + (((1)/(Y^2)))*v 141 + ((1))*v 299 + ((((-1)*a)/(Y)))*v 387 + ((1))*v 469=0 at h
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p271:=pivot_271 X Y Z W a b hX hY hZ hW v hv
  have p326:=pivot_326 X Y Z W a b hX hY hZ hW v hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v hv
  have p360:=pivot_360 X Y Z W a b hX hY hZ hW v hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p407:=pivot_407 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p214 - ((1))*p271 - ((1))*p326 - (((-1)))*p342 - (((1)/(Y^2)))*p345 - (((-1)))*p360 - ((((-1)*a)/(Y)))*p364 - (((1*a)/(Y)))*p403 - (((-1)))*p407

#print axioms residual_75

compact_residual_elimination
theorem residual_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2)) + ((-1)))*v 390 + ((((-1))/(Y^2)) + (((-1)*X*a)/(Y)) + ((-1)*X) + ((1*X^2)/(Y^2)))*v 435=0 := by
  have h:=hv 476
  change ((1))*v 135 + (((1)/(Y^2)))*v 195 + ((1))*v 305 + ((((-1)*a)/(Y)))*v 405 + ((1))*v 475=0 at h
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*a)/(Y)))*p102 - ((1))*p111 - (((1)/(Y^2)))*p131 - ((1))*p196 - (((1)/(X*Y^2)))*p232 - ((((-1)*a)/(X*Y)))*p235 - (((1)/(X)))*p256 - ((1))*p273

#print axioms residual_76

compact_residual_elimination
theorem residual_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*v 390 + ((((-1)*X^2)/(Y^2)) + ((1*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)) + ((1*X^4)/(2*Y^2)) + ((1*X^4*a)/(2*Y)) + ((1*X^4)/(2)))*v 435=0 := by
  have h:=hv 477
  change ((1))*v 138 + (((1)/(Y^2)))*v 222 + ((1))*v 308 + ((((-1)*a)/(Y)))*v 414 + ((1))*v 478=0 at h
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  have p400:=pivot_400 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p28 - ((((-1)*a)/(Y)))*p104 - ((((-1)*X*a)/(Y*W^2)))*p198 - (((1*a)/(Y*W^2)))*p230 - (((1)/(Y^2)))*p274 - (((1*X)/(W^2)))*p358 - ((1))*p394 - ((1))*p400

#print axioms residual_77

compact_residual_elimination
theorem residual_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + ((((-1))/(Y^2*W^2)) + (((-4))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-2)*Y^2)/(W^2)) + ((1*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 390 + (((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((7*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((6*X^3)/(W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((2*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + (((-1)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)) + ((1*X^5)/(W^2)) + ((1*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 481
  change ((1))*v 142 + (((1)/(Y^2)))*v 258 + ((1))*v 312 + ((((-1)*a)/(Y)))*v 426 + ((1))*v 482=0 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p379:=pivot_379 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*a)/(Y)))*p16 - (((1)/(Y^2)))*p46 - ((1))*p76 - (((1*X)/(Y^2)))*p116 - (((1*X)/(Y^2*W^2)))*p257 - ((1))*p352 - (((1*X*Y^2)/(W^2)))*p358 - ((1))*p379

#print axioms residual_78

compact_residual_elimination
theorem residual_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(W^2)) + ((1*X)/(W^2)))*v 370 + ((((-4))/(Y^2*W^2)) + ((1)/(Y^2)) + ((1*Z)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-2))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-3)*X)/(W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^3)/(W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-3)*X)/(2*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((7*X^2)/(Y^2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((11*X^3)/(2*Y^2*W^2)) + (((-3)*X^3*Z)/(2*Y^2*W^2)) + ((3*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + ((1*X^3*a^2)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(W^2)) + ((5*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + ((1*X^4*a)/(Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^5)/(Y^2*W^2)) + ((1*X^5*a)/(2*Y*W^2)) + ((1*X^5*a^2)/(2*W^2)) + ((1*X^5*Y*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 483
  change ((1))*v 148 + (((1)/(Y^2)))*v 312 + ((1))*v 318 + ((((-1)*a)/(Y)))*v 444 + ((1))*v 488=0 at h
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p225:=pivot_225 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p381:=pivot_381 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*a)/(Y)))*p224 - ((1))*p225 - ((((-1))/(W^2)))*p246 - (((1*X*a)/(Y)))*p274 - ((1))*p282 - ((1*X))*p306 - (((1)/(Y^2)))*p352 - (((1)/(W^2)) + ((1*X)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*p358 - (((-1)*X))*p381

#print axioms residual_79

compact_residual_elimination
theorem residual_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((3)/(Y^2)) + (((-1)*Z)/(Y^2)) + ((1*X)/(Y^2)) + (1*X))*v 390 + (((3*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((3*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (2*X^2) + ((1*X^2*a^2)/(2)) + (((-1)*X^2*Z)/(2)) + ((1*X^2*Y*a)/(2)) + (((-2)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-3)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + (((-1)*X^3*a^2)/(2)) + ((1*X^3*Z)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 435=0 := by
  have h:=hv 486
  change ((1))*v 155 + ((1))*v 325 + (((1)/(Y^2)))*v 375 + ((((-1)*a)/(Y)))*v 465 + ((1))*v 495=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p2 - ((((-1)*a)/(Y)))*p189 - (((1)/(Y^2)))*p208 - ((((-1))/(Y^2)))*p235 - (((1*a)/(Y)))*p257 - ((1))*p304 - (((1)/(X)))*p358 - ((1))*p359

#print axioms residual_80

compact_residual_elimination
theorem residual_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 492
  change ((1))*v 167 + ((1))*v 337 + (((1)/(Y^2)))*v 483 + ((((-1)*a)/(Y)))*v 501 + ((1))*v 507=0 at h
  have p49:=pivot_49 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p388:=pivot_388 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p49 - (((1)/(Y^2)))*p74 - ((((-1)*a)/(Y)))*p85 - (((1)/(X*Y^2)))*p114 - ((((-1)*a)/(X*Y*W^2)))*p121 - (((1)/(X*Y^2*W^2)))*p235 - ((((-1)*a)/(Y*W^2)))*p257 - ((1))*p286 - ((1))*p308 - ((((-1))/(X)))*p388

#print axioms residual_81

compact_residual_elimination
theorem residual_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)))*v 390 + (((1)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((-1)*X) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(2*W)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)))*v 435=0 := by
  have h:=hv 494
  change ((1))*v 9 + ((((-1)*b)/(W)))*v 45 + ((1))*v 111 + ((1))*v 213 + (((1)/(W^2)))*v 225 + ((1))*v 315 + ((1))*v 417=0 at h
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p26 - ((1))*p69 - (((1)/(W^2)))*p137 - (((1)/(W^2)))*p189 - ((1))*p223 - ((1))*p236 - ((((-1)*Y^2)/(X)))*p256 - ((((-1))/(W^2)) + (((-1)*b)/(W)))*p257 - ((1))*p258

#print axioms residual_82

compact_residual_elimination
theorem residual_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2*W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + ((3)/(X^2*W^2)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-7))/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((3*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-3)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-2)*Y^4)/(W^2)) + ((11*X)/(2*W^2)) + ((1*X*b)/(2*W)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((5*X^2)/(W^2)) + ((1*X^2*b)/(2*W)) + (((-3)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((4*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((4*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 497
  change ((1))*v 15 + ((((-1)*b)/(W)))*v 75 + ((1))*v 117 + ((1))*v 219 + ((1))*v 321 + (((1)/(W^2)))*v 375 + ((1))*v 423=0 at h
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p5 - ((1))*p54 - (((1)/(W^2)) + (((-1)*b)/(W)))*p194 - (((1)/(W^2)))*p208 - ((((-1))/(W^2)))*p235 - ((1))*p278 - ((1))*p300 - ((1*X))*p322 - ((1))*p329 - ((((-1))/(X)))*p331 - (((1)/(X)))*p335 - ((((-1))/(X)))*p403 - (((-1)))*p404

#print axioms residual_83

compact_residual_elimination
theorem residual_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Z)/(2*Y^2*W^2)) + (((-1)*Z)/(W^2)) + ((1*Z*a^2)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)))*v 435=0 := by
  have h:=hv 498
  change ((1))*v 17 + ((((-1)*b)/(W)))*v 85 + ((1))*v 119 + ((1))*v 221 + ((1))*v 323 + (((1)/(W^2)) + (1))*v 425=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p207:=pivot_207 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*b)/(W)))*p11 - (((1)/(W^2)) + (1))*p12 - ((1))*p71 - (((1)/(X*Y^2)))*p113 - ((1))*p207 - (((-1)))*p238 - ((1))*p240 - ((1))*p244

#print axioms residual_84

compact_residual_elimination
theorem residual_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 499
  change ((1))*v 18 + ((((-1)*b)/(W)))*v 90 + ((1))*v 120 + ((1))*v 222 + ((1))*v 324 + ((1))*v 426 + (((1)/(W^2)))*v 450=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*b)/(W)))*p3 - ((1))*p8 - ((1))*p16 - (((1)/(W^2)))*p91 - (((1*X)/(W^2)))*p194 - ((1))*p220 - ((1))*p235 - ((1))*p274 - (((-1)*X))*p355

#print axioms residual_85

compact_residual_elimination
theorem residual_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 370 + ((((-1)*a)/(X*Y)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-2))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*b)/(W)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1)*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((1*Y*a^3)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + ((1*X*a)/(Y)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 507
  change ((1))*v 31 + ((1))*v 133 + ((((-1)*b)/(W)))*v 155 + ((1))*v 235 + (((1)/(W^2)))*v 265 + ((1))*v 337 + ((1))*v 439=0 at h
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p173:=pivot_173 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p216:=pivot_216 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p316:=pivot_316 X Y Z W a b hX hY hZ hW v hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p375:=pivot_375 X Y Z W a b hX hY hZ hW v hv
  have p388:=pivot_388 X Y Z W a b hX hY hZ hW v hv
  have p390:=pivot_390 X Y Z W a b hX hY hZ hW v hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p82 - ((1))*p141 - ((1))*p173 - (((1)/(Y^2*W^2)))*p189 - ((1))*p216 - (((1)/(X*Y^2)))*p235 - ((((-1))/(Y^2*W^2)))*p257 - ((1))*p286 - ((((-1)*b)/(W)))*p304 - ((1))*p316 - (((-1)))*p349 - ((((-1)*b)/(X*W)))*p358 - ((((-1))/(X)))*p375 - ((((-1))/(X)))*p388 - (((-1)))*p390 - (((1)/(X)))*p402

#print axioms residual_86

compact_residual_elimination
theorem residual_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^4)) + ((3)/(X^3*W^2)) + (((-2))/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + (((-7))/(X^2*W^2)) + ((1*b)/(X^2*W)) + ((1)/(X^2)) + ((1*Z)/(X^2*W^2)) + ((2*Y*a)/(X^2*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-3))/(X*W^2)) + ((1)/(X)) + ((3*Y*a)/(X*W^2)) + (((-4)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((1*b)/(X*W)) + (((-1))/(2*X)) + ((3*Z)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-1)*Y*a)/(2*X)) + ((1*Y*Z*a)/(2*X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((3*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^2)/(2*X)) + ((1*Y^2*Z)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + (((-2)*Y^4)/(X*W^2)) + ((11)/(2*W^2)) + ((1*b)/(2*W)) + (((-3))/(2)) + (((-3)*Z)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a*b)/(2*W)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*b)/(2*W)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*Y^4*a^2)/(2*W^2)) + ((1*Y^5*a)/(2*W^2)) + ((9*X)/(2*W^2)) + ((1*X*b)/(2*W)) + (((-3)*X)/(2)) + (((-1)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((5*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((9*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((3*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((2*X^3)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 508
  change ((1))*v 33 + ((1))*v 135 + ((((-1)*b)/(W)))*v 165 + ((1))*v 237 + (((1)/(W^2)))*v 315 + ((1))*v 339 + ((1))*v 441=0 at h
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p38 - ((1))*p159 - (((1)/(X*W^2)))*p195 - ((1))*p196 - ((((-1)*b)/(W)))*p198 - ((1))*p201 - ((((-1))/(X*W^2)) + ((1*b)/(X*W)))*p230 - (((1)/(W^2)))*p236 - ((((-1)*Y^2)/(X*W^2)))*p256 - ((((-1))/(X)))*p310 - ((1))*p318 - ((1*X))*p354 - ((((-1))/(X^3)))*p355 - ((((-1)*Y^2)/(X^3*W^2)))*p358 - ((((-1))/(X)))*p404

#print axioms residual_87

compact_residual_elimination
theorem residual_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(Y^2*W^2)) + ((1*Z*b)/(Y^2*W)) + ((1*Z)/(Y^2)))*v 390 + (((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + (((-1)*X^2*Z*b)/(Y^2*W)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Z*b)/(2*W)) + (((-1)*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 509
  change ((1))*v 34 + ((1))*v 136 + ((((-1)*b)/(W)))*v 170 + ((1))*v 238 + (((1)/(W^2)) + (1))*v 340 + ((1))*v 442=0 at h
  have p40:=pivot_40 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v hv
  have p133:=pivot_133 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p40 - ((((-1)*b)/(W)))*p117 - (((1)/(W^2)) + (1))*p118 - ((1))*p119 - ((1))*p133 - (((1*X*Z*b)/(Y^2*W)))*p189 - ((((-1)*X*Z)/(Y^2*W^2)))*p194 - ((((-1)*Z)/(W^2)))*p239 - ((1))*p241 - ((((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*Z*b)/(Y^2*W)) + (((-1)*X*Z)/(Y^2)))*p257

#print axioms residual_88

compact_residual_elimination
theorem residual_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + (((-2))/(X^2*W^2)) + (((-2))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((5*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((3*Y^4)/(2*X*W^2)) + ((3)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((6*X)/(W^2)) + (((-1)*X*b)/(2*W)) + (((-5)*X)/(2)) + (((-2)*X*Z)/(W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((2*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((4*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-7)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 510
  change ((1))*v 36 + ((1))*v 138 + ((((-1)*b)/(W)))*v 180 + ((1))*v 240 + ((1))*v 342 + (((1)/(W^2)))*v 390 + ((1))*v 444=0 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p27 - ((1))*p127 - ((((-1)*b)/(W)))*p195 - (((1*X)/(W^2)))*p198 - ((1))*p224 - ((((-1))/(W^2)) + ((1*b)/(W)))*p230 - (((-1)*X))*p274 - ((1))*p313 - (((1)/(X^2)))*p354 - ((((-1)*X^2*Y^2)/(W^2)))*p358 - ((1))*p394

#print axioms residual_89

compact_residual_elimination
theorem residual_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*a)/(Y*W^2)) + (((-1)*a)/(Y)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X^2*b)/(Y^2*W)) + (((-1)*X^2*b)/(W)))*v 390 + ((((-1)*X*a)/(2*Y*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2*a)/(Y)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3*b)/(W)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^4*b)/(Y^2*W)) + ((1*X^4*a*b)/(2*Y*W)) + ((1*X^4*a^2*b)/(2*W)) + ((1*X^4*Y*a*b)/(2*W)))*v 435=0 := by
  have h:=hv 513
  change ((1))*v 40 + ((1))*v 142 + ((((-1)*b)/(W)))*v 200 + ((1))*v 244 + ((1))*v 346 + ((1))*v 448 + (((1)/(W^2)))*v 490=0 at h
  have p48:=pivot_48 X Y Z W a b hX hY hZ hW v hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p377:=pivot_377 X Y Z W a b hX hY hZ hW v hv
  have p379:=pivot_379 X Y Z W a b hX hY hZ hW v hv
  have p409:=pivot_409 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf)) h - ((1))*p48 - (((1)/(W^2)))*p60 - ((((-1)*b)/(W)))*p227 - ((1))*p256 - ((1))*p377 - ((1))*p379 - ((1))*p409

#print axioms residual_90

compact_residual_elimination
theorem residual_91 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(W^2)) + ((1*b)/(W)) + (1))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((-1)*X^2) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*b)/(2*W)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*b)/(2*W)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 514
  change (((1)/(W^2)))*v 30 + ((1))*v 42 + ((1))*v 144 + ((((-1)*b)/(W)))*v 210 + ((1))*v 246 + ((1))*v 348 + ((1))*v 450=0 at h
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p15 - ((1))*p91 - ((((-1)*b)/(W)))*p121 - ((1))*p162 - (((1*X)/(W^2)))*p189 - ((1*X))*p194 - ((((-1)*X)/(W^2)) + (((-1)*X*b)/(W)))*p257 - ((1))*p261 - ((1))*p354 - ((1))*p357

#print axioms residual_91

compact_residual_elimination
theorem residual_92 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)) + ((1)/(X*W^2)) + (((-1))/(X)) + (1))*v 390 + (((1)/(W^2)) + (((-1)*X)/(2*W^2)) + (1*X) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 515
  change ((1))*v 45 + (((1)/(W^2)))*v 105 + ((1))*v 147 + ((((-1)*b)/(W)))*v 225 + ((1))*v 249 + ((1))*v 351 + ((1))*v 453=0 at h
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p321:=pivot_321 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  have p365:=pivot_365 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p99 - ((((-1)*b)/(W)))*p137 - ((1))*p163 - ((1))*p257 - ((1))*p291 - ((1))*p321 - ((((-1))/(X)))*p336 - ((((-1))/(X)))*p346 - (((-1)))*p353 - ((1))*p365

#print axioms residual_92

compact_residual_elimination
theorem residual_93 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 516
  change ((1))*v 48 + ((1))*v 150 + (((1)/(W^2)))*v 180 + ((((-1)*b)/(W)))*v 240 + ((1))*v 252 + ((1))*v 354 + ((1))*v 456=0 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((((-1)*b)/(W)))*p27 - ((1))*p45 - (((1)/(W^2)))*p195 - ((((-1))/(W^2)))*p230 - ((1))*p233 - ((1))*p262 - ((1))*p293 - ((1))*p332 - ((((-1))/(X)))*p353

#print axioms residual_93

compact_residual_elimination
theorem residual_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X)) + ((-1)))*v 390 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 517
  change ((1))*v 57 + ((1))*v 159 + ((1))*v 261 + ((((-1)*b)/(W)))*v 285 + ((1))*v 363 + (((1)/(W^2)))*v 405 + ((1))*v 465=0 at h
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p80 - ((((-1)*b)/(W)))*p83 - (((1)/(X*W^2)))*p91 - (((1)/(W^2)))*p102 - ((1))*p189 - (((1)/(W^2)) + (((-1)*b)/(W)))*p194 - (((1)/(X*W^2)))*p235 - (((-1)))*p257 - ((1))*p275 - ((1))*p297 - (((-1)))*p302 - ((1))*p306 - ((((-1))/(X)))*p327 - ((((-1))/(X)))*p337 - ((((-1))/(X)))*p339 - (((-1)))*p352

#print axioms residual_94

compact_residual_elimination
theorem residual_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 390 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)) + (1*X^2) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 518
  change ((1))*v 60 + ((1))*v 162 + ((1))*v 264 + ((((-1)*b)/(W)))*v 300 + ((1))*v 366 + ((1))*v 468 + (((1)/(W^2)))*v 480=0 at h
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p13 - ((1))*p77 - ((1))*p109 - ((((-1)*b)/(W)))*p150 - ((((-1)*X*b)/(W)))*p189 - (((1*X)/(W^2)) + ((1*X*b)/(W)))*p257 - ((1))*p333 - ((1))*p355 - ((1))*p356

#print axioms residual_95

compact_residual_elimination
theorem residual_96 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + ((1)/(W^2)))*v 370 + ((((-1))/(X*Y^2)) + (((-2))/(Y^2*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 390 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((2*X^2)/(Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 519
  change (((1)/(W^2)))*v 20 + ((1))*v 62 + ((1))*v 164 + ((1))*v 266 + ((((-1)*b)/(W)))*v 310 + ((1))*v 368 + ((1))*v 470=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p375:=pivot_375 X Y Z W a b hX hY hZ hW v hv
  have p378:=pivot_378 X Y Z W a b hX hY hZ hW v hv
  have p388:=pivot_388 X Y Z W a b hX hY hZ hW v hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p23 - (((1)/(W^2)))*p64 - ((1))*p93 - (((1*W^2)/(Y^2)))*p126 - (((1*X)/(Y^2*W^2)))*p194 - (((1*X)/(Y^2)))*p236 - ((((-1)*b)/(W)))*p246 - (((-1)))*p256 - (((1*b)/(W)))*p358 - ((1))*p375 - ((1))*p378 - ((1))*p388 - (((-1)))*p402

#print axioms residual_96

compact_residual_elimination
theorem residual_97 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + ((1)/(W^2)))*v 390 + (((1*X)/(W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=0 := by
  have h:=hv 520
  change (((1)/(W^2)))*v 45 + ((1))*v 63 + ((1))*v 165 + ((1))*v 267 + ((((-1)*b)/(W)))*v 315 + ((1))*v 369 + ((1))*v 471=0 at h
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p337:=pivot_337 X Y Z W a b hX hY hZ hW v hv
  have p339:=pivot_339 X Y Z W a b hX hY hZ hW v hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p110 - ((1))*p151 - ((1))*p198 - (((1*Y^2)/(X*W^2)))*p219 - (((1)/(X*W^2)) + (((-1))/(X)) + ((1*Y^2)/(W^2)))*p230 - (((1)/(X*W^2)))*p235 - ((((-1)*b)/(W)))*p236 - (((1*Y^2*b)/(X*W)))*p256 - (((1)/(W^2)))*p257 - ((1))*p276 - ((1))*p298 - ((((-1)*Y^2)/(X*W^2)))*p330 - (((-1)))*p337 - (((-1)))*p339 - ((((-1))/(X)))*p341

#print axioms residual_97

compact_residual_elimination
theorem residual_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2*W^2)) + ((2*b)/(X*Y^2*W)) + (((-1)*Z*b)/(X*Y^2*W)) + (((-1))/(Y^2*W^2)) + (((-2)*b)/(Y^2*W)) + ((1*Z*b)/(Y^2*W)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-2)*X*b)/(Y^2*W)) + ((1*X*Z*b)/(Y^2*W)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + (((-1)*X^2*Z*b)/(2*Y^2*W)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a*b)/(Y*W)) + ((1*X^2*Z*a*b)/(2*Y*W)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*Z*b)/(2*W)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(Y*W)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(W)) + (((-1)*X^3*Z*b)/(2*W)))*v 435=0 := by
  have h:=hv 521
  change ((1))*v 65 + (((1)/(W^2)))*v 95 + ((1))*v 167 + ((1))*v 269 + ((((-1)*b)/(W)))*v 325 + ((1))*v 371 + ((1))*v 473=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p229:=pivot_229 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v hv
  have p385:=pivot_385 X Y Z W a b hX hY hZ hW v hv
  have p390:=pivot_390 X Y Z W a b hX hY hZ hW v hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p30 - ((1))*p89 - (((1)/(W^2)))*p95 - ((1))*p229 - (((1)/(X*Y^2*W^2)))*p230 - ((1))*p308 - (((1*W^2)/(X*Y^2)))*p331 - ((((-1)*W^2)/(X*Y^2)))*p335 - (((-1)))*p351 - ((((-1)*b)/(W)))*p359 - ((1))*p385 - ((1))*p390 - ((((-1))/(X)))*p402

#print axioms residual_98

compact_residual_elimination
theorem residual_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^3)) + (((-3))/(X^2*W^2)) + ((2)/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + ((7)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((3)/(W^2)) + ((-1)) + (((-3)*Y*a)/(W^2)) + ((4*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((4)/(W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-3)*Z)/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((3*Y^2)/(W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-11)*X)/(2*W^2)) + (((-1)*X*b)/(2*W)) + ((3*X)/(2)) + ((3*X*Z)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y*a*b)/(2*W)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-5)*X^2)/(W^2)) + (((-1)*X^2*b)/(2*W)) + ((3*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-4)*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-5)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-4)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-2)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-3)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 522
  change ((1))*v 66 + (((1)/(W^2)))*v 120 + ((1))*v 168 + ((1))*v 270 + ((((-1)*b)/(W)))*v 330 + ((1))*v 372 + ((1))*v 474=0 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p9 - ((1))*p152 - ((1))*p199 - (((1*X)/(W^2)))*p202 - (((1)/(W^2)) + (((-1)*b)/(W)))*p230 - (((1)/(W^2)))*p235 - ((1))*p310 - (((-1)*X))*p322 - (((1)/(X^2)))*p355 - (((1*Y^2)/(X^2*W^2)))*p358 - ((1))*p404

#print axioms residual_99

compact_residual_elimination
theorem residual_100 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Z)/(Y^2*W^2)) + (((-1)*Z*b)/(Y^2*W)) + (((-1)*Z)/(Y^2)))*v 390 + ((((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + ((1*X^2*Z*b)/(Y^2*W)) + ((1*X^2*Z)/(Y^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + ((1*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Z*b)/(2*W)) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 523
  change ((1))*v 68 + (((1)/(W^2)) + (1))*v 170 + ((1))*v 272 + ((((-1)*b)/(W)))*v 340 + ((1))*v 374 + ((1))*v 476=0 at h
  have p14:=pivot_14 X Y Z W a b hX hY hZ hW v hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p128:=pivot_128 X Y Z W a b hX hY hZ hW v hv
  have p169:=pivot_169 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p14 - (((1)/(W^2)) + (1))*p117 - ((((-1)*b)/(W)))*p118 - ((1))*p128 - ((1))*p169 - ((((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2)))*p189 - ((1))*p238 - ((((-1)*Z)/(W^2)))*p242 - (((1*X*Z)/(Y^2*W^2)) + ((1*X*Z*b)/(Y^2*W)) + ((1*X*Z)/(Y^2)))*p257

#print axioms residual_100

compact_residual_elimination
theorem residual_101 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + ((((-1))/(X^4)) + ((2)/(X^3*W^2)) + ((2)/(X^3)) + ((2*Y^2)/(X^3*W^2)) + ((4)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1))/(X)) + (((-3)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((2)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + (((-5)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + (((-3))/(2*X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-3)*Y^4)/(2*X^2*W^2)) + (((-3))/(X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + (((-1)*Z)/(2*X*W^2)) + (((-3)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-3)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-6))/(W^2)) + ((1*b)/(2*W)) + ((5)/(2)) + ((2*Z)/(W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a*b)/(2*W)) + ((1*Y*a)/(2)) + (((-2)*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^2*b)/(2*W)) + ((1*Y^2)/(2)) + (((-2)*Y^3*a)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-7)*X)/(2*W^2)) + (2*X) + ((1*X*Z)/(2*W^2)) + (1*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + (((-2)*X*Y^2)/(W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + (((-5)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-3)*X^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-5)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((7*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 524
  change ((1))*v 69 + ((1))*v 171 + (((1)/(W^2)))*v 195 + ((1))*v 273 + ((((-1)*b)/(W)))*v 345 + ((1))*v 375 + ((1))*v 477=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p39 - (((1)/(W^2)))*p131 - ((1))*p146 - ((((-1)*b)/(W)))*p202 - ((1))*p208 - ((1))*p222 - (((1)/(X*W^2)) + (((-1)*b)/(X*W)))*p230 - (((-1)))*p235 - (((1*Y^2)/(X*W^2)))*p256 - ((1))*p279 - ((((-1))/(X)))*p313 - ((((-1))/(X^3)))*p354 - ((1*X))*p355 - (((1*X*Y^2)/(W^2)))*p358 - ((((-1))/(X)))*p394

#print axioms residual_101

compact_residual_elimination
theorem residual_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*a)/(X*Y*W^2)) + ((1*a)/(X*Y)) + ((1*b)/(Y^2*W)) + ((1*X*b)/(Y^2*W)) + ((1*X*b)/(W)))*v 390 + (((1*a)/(2*Y*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a^3)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a*b)/(2*W)))*v 435=0 := by
  have h:=hv 525
  change ((1))*v 71 + ((1))*v 173 + (((1)/(W^2)))*v 245 + ((1))*v 275 + ((((-1)*b)/(W)))*v 355 + ((1))*v 377 + ((1))*v 479=0 at h
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p168:=pivot_168 X Y Z W a b hX hY hZ hW v hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p280:=pivot_280 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  have p343:=pivot_343 X Y Z W a b hX hY hZ hW v hv
  have p379:=pivot_379 X Y Z W a b hX hY hZ hW v hv
  have p391:=pivot_391 X Y Z W a b hX hY hZ hW v hv
  have p409:=pivot_409 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p145 - ((1))*p147 - ((1))*p168 - (((1)/(X)))*p171 - (((1)/(Y^2*W^2)))*p194 - (((1)/(Y^2*W^2)))*p257 - ((1))*p280 - ((((-1)*b)/(W)))*p294 - ((1))*p312 - (((-1)))*p343 - ((((-1))/(X)))*p379 - ((1))*p391 - ((((-1))/(X)))*p409

#print axioms residual_102

compact_residual_elimination
theorem residual_103 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)))*v 435=0 := by
  have h:=hv 526
  change ((1))*v 72 + ((1))*v 174 + (((1)/(W^2)))*v 270 + ((1))*v 276 + ((((-1)*b)/(W)))*v 360 + ((1))*v 378 + ((1))*v 480=0 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p9 - ((1))*p13 - ((1))*p114 - ((((-1)*b)/(W)))*p232 - (((1)/(W^2)))*p235 - ((1))*p288 - (((-1)*X))*p313 - ((1))*p335 - ((((-1))/(X)))*p354 - ((1))*p393

#print axioms residual_103

compact_residual_elimination
theorem residual_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)) + ((1*a)/(Y)) + ((2*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)))*v 390 + (((2*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((3*X^3)/(2*W^2)) + ((1*X^3*b)/(W)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-3)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*b)/(Y^2*W)) + (((-1)*X^4*a)/(Y*W^2)) + (((-1)*X^4*a*b)/(2*Y*W)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*a^2*b)/(2*W)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*a*b)/(2*W)))*v 435=0 := by
  have h:=hv 527
  change ((1))*v 74 + ((1))*v 176 + ((1))*v 278 + (((1)/(W^2)))*v 320 + ((((-1)*b)/(W)))*v 370 + ((1))*v 380 + ((1))*v 482=0 at h
  have p24:=pivot_24 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p370:=pivot_370 X Y Z W a b hX hY hZ hW v hv
  have p381:=pivot_381 X Y Z W a b hX hY hZ hW v hv
  have p409:=pivot_409 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p24 - ((1))*p76 - (((1*X)/(Y^2)))*p116 - (((1)/(W^2)))*p219 - (((1)/(Y^2*W^2)) + ((1*X)/(W^2)))*p230 - (((1*X)/(Y^2*W^2)))*p257 - ((1))*p319 - ((((-1)*W^2)/(Y^2)))*p335 - ((1))*p370 - ((1))*p381 - (((-1)))*p409

#print axioms residual_104

compact_residual_elimination
theorem residual_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*Y^2*W^2)) + ((1*b)/(X*Y^2*W)) + ((1)/(X*Y^2)) + (((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 390 + (((1)/(2*Y^2*W^2)) + ((1)/(W^2)) + (((-1)*a^2)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(Y^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*b)/(2*Y^2*W)) + (((-1)*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a*b)/(2*Y*W)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 529
  change ((1))*v 76 + ((1))*v 178 + ((1))*v 280 + (((1)/(W^2)))*v 370 + ((((-1)*b)/(W)))*v 380 + ((1))*v 382 + ((1))*v 484=0 at h
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v hv
  have p311:=pivot_311 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p382:=pivot_382 X Y Z W a b hX hY hZ hW v hv
  have p399:=pivot_399 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p62 - ((1))*p311 - (((-1)*X^2))*p313 - ((((-1)*b)/(W)))*p319 - ((1))*p334 - (((1*W*b)/(Y^2)))*p335 - (((-1)))*p354 - ((1))*p382 - ((1))*p399

#print axioms residual_105

compact_residual_elimination
theorem residual_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)))*v 390 + (((1)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((-1)*X) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(2*W)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)))*v 435=0 := by
  have h:=hv 530
  change ((1))*v 81 + ((1))*v 183 + ((1))*v 285 + ((1))*v 387 + ((((-1)*b)/(W)))*v 405 + ((1))*v 489 + (((1)/(W^2)))*v 495=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p315:=pivot_315 X Y Z W a b hX hY hZ hW v hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p2 - ((1))*p66 - ((1))*p83 - ((((-1)*b)/(W)))*p102 - (((1)/(X)))*p126 - ((1))*p194 - ((((-1)*b)/(X*W)))*p235 - (((1)/(W^2)))*p236 - ((1))*p253 - ((((-1)*Y^2)/(X*W^2)))*p256 - ((1))*p315 - (((-1)))*p331 - ((1))*p335 - ((((-1))/(X)))*p356 - (((1*Y^2)/(X*W^2)))*p358 - ((1))*p364 - (((-1)))*p403

#print axioms residual_106

compact_residual_elimination
theorem residual_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + ((1)/(X)) + ((1*b)/(Y^2*W)) + ((2)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + ((1*X*b)/(W)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X*a)/(Y)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-5)*X^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=0 := by
  have h:=hv 531
  change (((1)/(W^2)))*v 10 + ((1))*v 82 + ((1))*v 184 + ((1))*v 286 + ((1))*v 388 + ((((-1)*b)/(W)))*v 410 + ((1))*v 490=0 at h
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p67:=pivot_67 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v hv
  have p361:=pivot_361 X Y Z W a b hX hY hZ hW v hv
  have p378:=pivot_378 X Y Z W a b hX hY hZ hW v hv
  have p390:=pivot_390 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)))*p31 - ((1))*p60 - ((1))*p67 - ((((-1)*b)/(W)))*p78 - (((1*X)/(Y^2)))*p166 - ((((-1)*X*b)/(Y^2*W)))*p196 - ((1))*p349 - ((1))*p361 - ((((-1))/(X)))*p378 - ((1))*p390

#print axioms residual_107

compact_residual_elimination
theorem residual_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 532
  change (((1)/(W^2)))*v 60 + ((1))*v 84 + ((1))*v 186 + ((1))*v 288 + ((1))*v 390 + ((((-1)*b)/(W)))*v 420 + ((1))*v 492=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p0 - ((((-1)*b)/(W)))*p4 - ((1))*p37 - (((1)/(W^2)))*p77 - ((1))*p204 - ((1))*p322 - (((-1)*X))*p354

#print axioms residual_108

compact_residual_elimination
theorem residual_109 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(2*Y^2*W^2)) + ((1*Z)/(W^2)) + (((-1)*Z*a^2)/(2*W^2)) + ((1*Y^2*Z)/(2*W^2)) + (((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)))*v 435=0 := by
  have h:=hv 533
  change (((1)/(W^2)) + (1))*v 85 + ((1))*v 187 + ((1))*v 289 + ((1))*v 391 + ((((-1)*b)/(W)))*v 425 + ((1))*v 493=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p72:=pivot_72 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p217:=pivot_217 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(W^2)) + (1))*p11 - ((((-1)*b)/(W)))*p12 - ((1))*p72 - ((((-1)*Z)/(Y^2*W^2)))*p83 - ((((-1)*Z)/(Y^2*W^2)))*p194 - ((1))*p217 - ((1))*p237 - (((-1)))*p241 - ((1))*p243

#print axioms residual_109

compact_residual_elimination
theorem residual_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X*a)/(Y)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)))*v 435=0 := by
  have h:=hv 535
  change ((1))*v 88 + (((1)/(W^2)))*v 160 + ((1))*v 190 + ((1))*v 292 + ((1))*v 394 + ((((-1)*b)/(W)))*v 440 + ((1))*v 496=0 at h
  have p56:=pivot_56 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p178:=pivot_178 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p392:=pivot_392 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p56 - (((1)/(W^2)))*p78 - ((1))*p178 - (((1*X)/(Y^2*W^2)))*p189 - (((1)/(W^2)))*p193 - (((1*X)/(Y^2*W^2)))*p196 - ((1))*p205 - ((((-1))/(Y^2)) + (((-1))/(W^2)) + ((-1)*X))*p230 - ((1))*p245 - ((((-1)*X)/(Y^2*W^2)))*p257 - ((((-1)*b)/(W)))*p330 - ((1))*p350 - ((((-1)*Y^2)/(X*W^2)))*p358 - ((1))*p392

#print axioms residual_110

compact_residual_elimination
theorem residual_111 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + (((-1))/(W^2)))*v 390 + ((((-1)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=0 := by
  have h:=hv 536
  change ((1))*v 90 + ((1))*v 192 + (((1)/(W^2)))*v 210 + ((1))*v 294 + ((1))*v 396 + ((((-1)*b)/(W)))*v 450 + ((1))*v 498=0 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p3 - ((1))*p58 - ((((-1)*b)/(W)))*p91 - (((1)/(W^2)))*p121 - (((1*X)/(W^2)) + (((-1)*X*b)/(W)))*p194 - (((1*X)/(W^2)))*p257 - ((1))*p267 - ((1))*p336 - ((1))*p346

#print axioms residual_111

compact_residual_elimination
theorem residual_112 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)))*v 435=0 := by
  have h:=hv 537
  change ((1))*v 93 + ((1))*v 195 + (((1)/(W^2)))*v 285 + ((1))*v 297 + ((1))*v 399 + ((((-1)*b)/(W)))*v 465 + ((1))*v 501=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p18 - (((1)/(W^2)))*p83 - ((1))*p85 - (((1)/(X*W^2)))*p121 - ((1))*p131 - ((((-1)*b)/(W)))*p189 - (((1)/(W^2)))*p194 - ((1))*p200 - (((1*Y^2)/(X)))*p256 - (((1)/(W^2)) + ((1*b)/(W)))*p257 - ((1))*p259

#print axioms residual_112

compact_residual_elimination
theorem residual_113 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(W^2)) + ((1*b)/(W)) + (1))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((-1)*X^2) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*b)/(2*W)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*b)/(2*W)) + (((-1)*X^3*Y^2)/(2)))*v 435=0 := by
  have h:=hv 538
  change ((1))*v 94 + ((1))*v 196 + ((1))*v 298 + (((1)/(W^2)))*v 310 + ((1))*v 400 + ((((-1)*b)/(W)))*v 470 + ((1))*v 502=0 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p182:=pivot_182 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p374:=pivot_374 X Y Z W a b hX hY hZ hW v hv
  have p406:=pivot_406 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p86 - ((((-1)*b)/(W)))*p93 - ((((-1)*W*b)/(Y^2)))*p126 - (((1*X)/(W^2)))*p141 - ((1))*p182 - (((1)/(Y^2*W^2)))*p235 - ((((-1)*X*b)/(Y^2*W)))*p236 - ((1))*p239 - (((1)/(W^2)))*p246 - (((1*b)/(W)))*p256 - (((1)/(Y^2)))*p333 - ((((-1))/(W^2)))*p358 - ((1))*p374 - ((1))*p406

#print axioms residual_113

compact_residual_elimination
theorem residual_114 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 390 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 435=0 := by
  have h:=hv 539
  change ((1))*v 5 + ((1))*v 35 + ((1))*v 65 + (((1)/(Z)))*v 85 + ((1))*v 95 + ((1))*v 125 + ((1))*v 155 + ((1))*v 185 + ((1))*v 215 + ((1))*v 245 + ((1))*v 275 + ((1))*v 305 + ((1))*v 335 + ((1))*v 365 + ((1))*v 395 + ((1))*v 425 + ((1))*v 455 + ((1))*v 485=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - (((1)/(Z)))*p11 - ((1))*p12 - ((1))*p35 - ((1))*p89 - ((1))*p95 - ((1))*p100 - ((1))*p138 - ((1))*p142 - ((((-1)*W^2)/(X*Y^2*Z)))*p143 - ((1))*p145 - ((1))*p147 - ((1))*p148 - ((1))*p154 - (((1)/(Y^2)))*p194 - (((1)/(X*Y^2)))*p195 - ((1))*p210 - (((1)/(X*Y^2)))*p233 - ((1))*p251 - ((1))*p254 - ((((-1)*Y^2)/(X)))*p256 - (((1)/(Y^2)))*p257 - (((1*W^2)/(X*Y^2)))*p262 - ((1))*p273 - (((1*W^2)/(X*Y^2)))*p302 - ((1))*p304 - ((1))*p317 - (((-1)))*p319 - (((1*W^2)/(X*Y^2)))*p322 - (((-1)))*p330 - (((1*W^2)/(X*Y^2)))*p331 - ((((-1)*W^2)/(X*Y^2)) + ((1*W^2)/(Y^2)))*p335 - (((1)/(X)) + ((-1)))*p358

#print axioms residual_114

compact_residual_elimination
theorem residual_115 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^2)) + ((4)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((5)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-8)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-10)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-9)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)))*v 435=0 := by
  have h:=hv 540
  change ((1))*v 6 + ((1))*v 36 + ((1))*v 66 + ((1))*v 96 + (((1)/(Z)))*v 102 + ((1))*v 126 + ((1))*v 156 + ((1))*v 186 + ((1))*v 216 + ((1))*v 246 + ((1))*v 276 + ((1))*v 306 + ((1))*v 336 + ((1))*v 366 + ((1))*v 396 + ((1))*v 426 + ((1))*v 456 + ((1))*v 486=0 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  have p36:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p16 - ((1))*p36 - ((1))*p96 - (((1)/(Z)))*p113 - ((1))*p114 - ((1))*p115 - ((1))*p127 - ((1))*p143 - ((1))*p162 - (((1*X)/(W^2)))*p189 - ((((-1)*Z)/(W^2)))*p195 - (((1*X)/(W^2)))*p198 - ((1))*p199 - (((1*X)/(W^2)))*p202 - ((1))*p204 - (((1*Z)/(W^2)))*p230 - (((1)/(W^2)))*p235 - (((1*Y^2)/(W^2)))*p256 - ((((-1)*X)/(W^2)))*p257 - ((1))*p269 - ((1))*p309 - (((-1)*X))*p310 - (((-1)*X))*p322 - ((1))*p327 - ((1))*p332 - ((1))*p341 - ((1))*p346 - (((-1)*X))*p354 - ((((-1))/(X)))*p355 - ((1))*p356 - ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p358

#print axioms residual_115

compact_residual_elimination
theorem residual_116 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^4)) + ((4)/(X^3*W^2)) + ((2)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((4*Y^2)/(X^3*W^2)) + ((2)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-4))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-1))/(X*W^2)) + ((2*b)/(X*W)) + ((1*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + (((-1)*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-5)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-2))/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((4*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + (((-2)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-15))/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((1*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + (((-2)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-13))/(2*W^2)) + ((2*b)/(W)) + (2) + ((2*Z)/(W^2)) + ((1*Y*Z*a)/(W^2)) + (((-5)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^2*Z)/(W^2)) + (((-2)*Y^3*a)/(W^2)) + (((-3)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-5)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(2*W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-7)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((15*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 435=0 := by
  have h:=hv 541
  change ((1))*v 9 + ((1))*v 39 + ((1))*v 69 + ((1))*v 99 + ((1))*v 129 + (((1)/(Z)))*v 153 + ((1))*v 159 + ((1))*v 189 + ((1))*v 219 + ((1))*v 249 + ((1))*v 279 + ((1))*v 309 + ((1))*v 339 + ((1))*v 369 + ((1))*v 399 + ((1))*v 429 + ((1))*v 459 + ((1))*v 489=0 at h
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p69 - ((1))*p87 - ((1))*p97 - ((1))*p116 - ((1))*p135 - ((1))*p153 - ((1))*p163 - (((1)/(W^2)))*p189 - ((1))*p201 - (((1*Y^2)/(X*W^2)))*p205 - ((1))*p214 - ((((-1))/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p230 - ((((-1)*Z)/(X*W^2)))*p233 - (((1)/(Z)))*p234 - ((1))*p253 - (((1*Y^2)/(X*W^2)))*p256 - ((1))*p259 - ((1))*p261 - ((1))*p279 - ((1))*p298 - ((1))*p306 - ((((-1))/(X)))*p310 - ((1))*p329 - ((((-1)*Y^2)/(X*W^2)))*p330 - ((((-1))/(X)))*p331 - (((1)/(X)))*p335 - ((((-1))/(X)))*p337 - (((-1)))*p339 - (((-1)))*p342 - ((1))*p350 - ((((-1))/(X^3)) + (1*X))*p355 - ((((-1)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p358 - ((((-1))/(X)))*p394 - ((1))*p395

#print axioms residual_116

compact_residual_elimination
theorem residual_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + (((1)/(X^3)) + (((-1))/(X^2*W^2)) + ((1)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-3)*X)/(2*W^2)) + ((3*X)/(2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-9)*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + ((15*X^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((19*X^3)/(2*W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 542
  change ((1))*v 12 + ((1))*v 42 + ((1))*v 72 + ((1))*v 102 + ((1))*v 132 + ((1))*v 162 + ((1))*v 192 + (((1)/(Z)))*v 204 + ((1))*v 222 + ((1))*v 252 + ((1))*v 282 + ((1))*v 312 + ((1))*v 342 + ((1))*v 372 + ((1))*v 402 + ((1))*v 432 + ((1))*v 462 + ((1))*v 492=0 at h
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v hv
  have p358:=pivot_358 X Y Z W a b hX hY hZ hW v hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v hv
  have p404:=pivot_404 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p37 - ((1))*p45 - ((1))*p70 - ((1))*p113 - ((1))*p124 - (((1)/(Z)))*p165 - ((1))*p170 - ((((-1))/(W^2)))*p230 - ((1*X))*p253 - ((1))*p261 - (((1*Y^2)/(W^2)))*p264 - ((1))*p268 - ((1))*p274 - ((1))*p299 - ((1))*p313 - ((1))*p335 - ((1))*p336 - ((1))*p352 - (((1)/(X^2)))*p354 - ((1))*p355 - (((1*Y^2)/(W^2)) + ((2*X*Y^2)/(W^2)))*p358 - ((1))*p403 - ((1))*p404

#print axioms residual_117

compact_residual_elimination
theorem residual_118 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 370 + ((((-1))/(X^3)) + (((-4))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 390 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((10*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((11*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-2)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(W^2)))*v 435=0 := by
  have h:=hv 543
  change ((1))*v 18 + ((1))*v 48 + ((1))*v 78 + ((1))*v 108 + ((1))*v 138 + ((1))*v 168 + ((1))*v 198 + ((1))*v 228 + ((1))*v 258 + ((1))*v 288 + (((1)/(Z)))*v 306 + ((1))*v 318 + ((1))*v 348 + ((1))*v 378 + ((1))*v 408 + ((1))*v 438 + ((1))*v 468 + ((1))*v 498=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p8 - ((1))*p46 - ((1))*p58 - ((1))*p120 - (((1)/(Z)))*p143 - ((1))*p180 - (((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)))*p194 - ((((-1))/(W^2)))*p195 - (((1)/(W^2)))*p230 - ((1))*p252 - ((1))*p262 - ((1))*p302 - ((1))*p310 - ((1))*p322 - (((1*Y^2)/(W^2)))*p330 - ((1))*p331 - ((1))*p333 - (((-1)))*p335 - ((1))*p337 - ((1))*p353 - ((1))*p354 - (((1)/(X^2)))*p355 - (((1*Y^2)/(X^2*W^2)) + (((-1)*X*Y^2)/(W^2)))*p358 - ((1))*p393 - ((1))*p394

#print axioms residual_118

compact_residual_elimination
theorem residual_119 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^4)) + ((1)/(X^3*W^2)) + (((-1))/(X^3)) + (((-2)*Y^2)/(X^3*W^2)) + (((-3))/(X^2*W^2)) + ((1*b)/(X^2*W)) + ((1)/(X^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((1*b)/(W)) + (1) + ((1*Z)/(W^2)) + ((2*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + (((-3)*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(2*X*W^2)) + ((1*b)/(X*W)) + (((-1))/(2*X)) + ((1*Z)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + (((-1)*Y*a)/(2*X)) + ((1*Y*Z*a)/(2*X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^2)/(2*X)) + ((1*Y^2*Z)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + (((-3)*Y^4)/(2*X*W^2)) + ((7)/(2*W^2)) + (((-3))/(2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + (((-3)*Y^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((3*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((1*Y^4*a^2)/(2*W^2)) + ((1*Y^5*a)/(2*W^2)) + ((17*X)/(2*W^2)) + ((1*X*b)/(W)) + ((-2)*X) + (((-1)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + ((-1)*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((-1)*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + ((3*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(W^2)) + ((7*X^2)/(2*W^2)) + ((-1)*X^2) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((6*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 435=0 := by
  have h:=hv 544
  change ((1))*v 21 + ((1))*v 51 + ((1))*v 81 + ((1))*v 111 + ((1))*v 141 + ((1))*v 171 + ((1))*v 201 + ((1))*v 231 + ((1))*v 261 + ((1))*v 291 + ((1))*v 321 + ((1))*v 351 + (((1)/(Z)))*v 357 + ((1))*v 381 + ((1))*v 411 + ((1))*v 441 + ((1))*v 471 + ((1))*v 501=0 at h
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v hv
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
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) h - ((1))*p65 - ((1))*p66 - ((1))*p80 - ((1))*p85 - (((1)/(X*W^2)))*p91 - ((1))*p103 - (((1)/(X*W^2)))*p121 - (((1)/(X)))*p126 - ((1))*p130 - ((1))*p151 - ((1))*p157 - (((1)/(W^2)))*p189 - (((1)/(W^2)))*p194 - ((1))*p211 - (((1*Y^2)/(X*W^2)))*p219 - ((1))*p222 - (((1)/(X*W^2)) + ((1*Y^2)/(W^2)))*p230 - (((1)/(Z)))*p231 - ((((-1)*Z)/(X*W^2)))*p232 - (((1)/(W^2)))*p236 - (((1)/(X)))*p252 - ((((-1)*Y^2)/(X*W^2)))*p256 - ((1))*p258 - ((1))*p265 - ((1))*p278 - ((1))*p291 - ((((-1))/(X)))*p313 - ((1))*p318 - ((1*X))*p322 - ((1))*p333 - ((((-1))/(X)))*p335 - ((((-1))/(X)))*p336 - (((-1)))*p341 - ((1))*p345 - ((1))*p351 - ((((-1))/(X^3)) + (1*X))*p354 - (((1*Y^2)/(X*W^2)))*p358 - ((((-1))/(X)))*p403 - ((((-1))/(X)))*p404

#print axioms residual_119

end SmallLevelThirtyFourUnitMMM
