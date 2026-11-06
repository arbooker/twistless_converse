module

public import SmallLevelTwentySixUnitMMMKernelV1

/-! Consolidated chapter: SmallLevelTwentySixUnitMMM.FreeKernel. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMMFreeKernelBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixUnitMMM.FreeKernel
open Complex

theorem free_zero_736 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 736=0 := by
  have h:=pivot_317 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1))/(X^2*Z*W^2)) + (((-1)*Y*a)/(X^2*Z*W^2)) + ((1*Y^3*a)/(X^2*Z*W^2)) + ((1*Y^4)/(X^2*Z*W^2)) + (((-1)*Y^2)/(X*Z*W^2)) + (((-1)*Y^3*a)/(X*Z*W^2)) + (((-1)*Y^4)/(X*Z*W^2)) + (((-1)*X^2*Y^2)/(Z*W^2)))*p520 - (((1)/(X^2*Y^2*W^2)) + ((1)/(X^2*W^2)) + (((-1)*a^2)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + ((1)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*p540

theorem free_zero_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 44=0 := by
  have h:=pivot_316 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1)/(X^2*Z*W^2)) + ((1*Y*a)/(X^2*Z*W^2)) + (((-1)*Y^3*a)/(X^2*Z*W^2)) + (((-1)*Y^4)/(X^2*Z*W^2)) + ((1*Y^2)/(X*Z*W^2)) + ((1*Y^3*a)/(X*Z*W^2)) + ((1*Y^4)/(X*Z*W^2)) + ((1*X^2*Y^2)/(Z*W^2)))*p520 - ((((-1))/(X^2*Y^2*W^2)) + (((-1))/(X^2*W^2)) + ((1*a^2)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1))/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + (((-1))/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*p540

theorem free_zero_595 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 595=0 := by
  have h:=pivot_315 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(X^5*Z)) + (((-1)*Y^4)/(X^5*Z)) + ((1*Y^4)/(X^4*Z)) + ((1*Y^2)/(X^3*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1))/(X*Z)) + ((1)/(Z)))*p520 - ((((-1))/(X^5)) + ((1*Y*a)/(X^5)) + (((-1))/(X^4)) + ((1)/(X^3*Y^2)) + (((-1))/(X^3)) + ((1)/(X^2*Y^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X)))*p540

theorem free_zero_485 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 485=0 := by
  have h:=pivot_314 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^3*a)/(X^5*Z)) + ((1*Y^5*a)/(X^5*Z)) + (((-1)*Y^5*a)/(X^4*Z)) + (((-1)*Y*a)/(X^3*Z)) + (((-1)*Y^2)/(X^3*Z)) + ((1*Y^4)/(X^3*Z)) + (((-1))/(X*Z)))*p520 - (((1*Y*a)/(X^5)) + (((-1)*Y^2*a^2)/(X^5)) + ((1*Y*a)/(X^4)) + ((1)/(X^3*Y^2)) + (((-1)*Y*a)/(X^3)) + ((1)/(X^2)) + (((-1)*Y^2)/(X^2)) + ((1)/(X*Y^2)))*p540

theorem free_zero_575 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 575=0 := by
  have h:=pivot_313 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(X^5*Z)) + (((-1)*Y^4)/(X^5*Z)) + ((1*Y^4)/(X^4*Z)) + ((1)/(X^3*Z)) + ((1*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1))/(X*Z)) + ((1)/(Z)))*p520 - ((((-1))/(X^5)) + ((1*Y*a)/(X^5)) + (((-1))/(X^4)) + ((1*a)/(X^3*Y)) + (((-1))/(X^3)) + ((1*Y*a)/(X^2)) + (((-1))/(X)))*p540

theorem free_zero_550 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 550=0 := by
  have h:=pivot_312 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^2)/(X^3*Z)) + ((1*Y^4)/(X^3*Z)) + (((-1)*Y^4)/(X^2*Z)) + (((-2))/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*X)/(Z)))*p520 - (((1)/(X^3)) + (((-1)*Y*a)/(X^3)) + ((1)/(X^2)) + ((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1)*X^2)/(Y^2)))*p540

theorem free_zero_685 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 685=0 := by
  have h:=pivot_311 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^3*a)/(X^5*Z)) + ((1*Y^5*a)/(X^5*Z)) + (((-1)*Y^5*a)/(X^4*Z)) + (((-1)*Y*a)/(X^3*Z)) + ((1*Y^4)/(X^2*Z)) + ((1*Y*a)/(X*Z)) + (((-1)*Y*a)/(Z)))*p520 - (((1*Y*a)/(X^5)) + (((-1)*Y^2*a^2)/(X^5)) + ((1*Y*a)/(X^4)) + ((1)/(X^3*Y^2)) + (((-1))/(X^3)) + (((-1)*Y^2)/(X^2)))*p540

theorem free_zero_228 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 228=0 := by
  have h:=pivot_310 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^4)/(X^2*Z*W^2)) + (((-1)*Y^6)/(X^2*Z*W^2)) + ((1*Y^6)/(X*Z*W^2)) + ((1*Y^2)/(Z*W^2)) + ((1*X*Y^2)/(Z*W^2)) + (((-2)*X^2*Y^2)/(Z*W^2)) + ((1*X^3*Y^2)/(Z*W^2)))*p520 - ((((-1)*Y^2)/(X^2*W^2)) + ((1*Y^3*a)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + (1))*p540

theorem free_zero_552 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 552=0 := by
  have h:=pivot_309 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^4)/(X^2*Z*W^2)) + ((1*Y^6)/(X^2*Z*W^2)) + (((-1)*Y^6)/(X*Z*W^2)) + (((-1)*Y^2)/(Z*W^2)) + (((-1)*X*Y^2)/(Z*W^2)) + ((2*X^2*Y^2)/(Z*W^2)) + (((-1)*X^3*Y^2)/(Z*W^2)))*p520 - (((1*Y^2)/(X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1)/(W^2)) + ((-1)))*p540

theorem free_zero_580 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 580=0 := by
  have h:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^2)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + (((-1)*Y*a)/(Z)) + ((1*X*Y*a)/(Z)))*p520 - (((1)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X)) + ((1)/(Y^2)))*p540

theorem free_zero_230 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 230=0 := by
  have h:=pivot_307 X Y Z W a b hX hY hZ hW v hv
  have p550:=free_zero_550 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p550

theorem free_zero_470 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 470=0 := by
  have h:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1))/(X^2*Z)) + ((1*Y^2)/(X^2*Z)) + ((1*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + ((1*Y^2)/(Z)) + (((-1)*X*Y^2)/(Z)))*p520 - (((1)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + (((-1)*a)/(Y)))*p540

theorem free_zero_310 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 310=0 := by
  have h:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1)/(X^2*Z)) + (((-1)*Y^2)/(X^2*Z)) + (((-1)*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)) + ((1*X*Y^2)/(Z)))*p520 - ((((-1))/(X^2*Y^2)) + ((1*a)/(X^2*Y)) + ((1*a)/(Y)))*p540

theorem free_zero_572 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 572=0 := by
  have h:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)))*p520 - ((((-1)*Z)/(X*Y^2*W^2)) + ((1*Z*a)/(X*Y*W^2)) + (((-1)*Z)/(W^2)) + ((1*X*Z*a)/(Y*W^2)))*p540

theorem free_zero_620 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 620=0 := by
  have h:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1))/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*X)/(Z)))*p520 - (((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1)*X^2)/(Y^2)))*p540

theorem free_zero_200 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 200=0 := by
  have h:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p580

#print axioms free_zero_200

theorem free_zero_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 110=0 := by
  have h:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y^2)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^4)/(X*Z)))*p520 - (((1)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X)) + (1))*p540

theorem free_zero_670 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 670=0 := by
  have h:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^4)/(X*Z)))*p520 - ((((-1))/(X^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X)) + ((-1)))*p540

theorem free_zero_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 170=0 := by
  have h:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1)*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + (((-1)*Y^3*a)/(Z)))*p520 - (((1)/(X*Y^2)) + (((-1)*a^2)/(X)) + ((1*a)/(Y)))*p540

theorem free_zero_610 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 610=0 := by
  have h:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + ((1*Y^3*a)/(Z)))*p520 - ((((-1))/(X*Y^2)) + ((1*a^2)/(X)) + (((-1)*a)/(Y)))*p540

theorem free_zero_160 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 160=0 := by
  have h:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p620:=free_zero_620 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p620

theorem free_zero_208 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 208=0 := by
  have h:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  have p572:=free_zero_572 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p572

theorem free_zero_195 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 195=0 := by
  have h:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(X^4)) + (((-1)*Y^4)/(X^4)) + ((1*Y^4)/(X^3)))*p520 - ((((-1)*Z)/(X^4)) + ((1*Y*Z*a)/(X^4)) + (((-1)*Z)/(X^3)))*p540

theorem free_zero_676 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 676=0 := by
  have h:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - ((((-1))/(W^2)) + ((1*Y^2)/(W^2)))*p520 - ((((-1)*Z*a)/(Y*W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*Z)/(W^2)))*p540

theorem free_zero_495 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 495=0 := by
  have h:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1*Y^2)/(X*Z)))*p195 - ((((-1)*Y^2)/(X^3*Z)) + ((1*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)))*p520

theorem free_zero_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 285=0 := by
  have h:=pivot_292 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((((-1)*Y^2)/(X*Z)))*p195 - (((1*Y^2)/(X^3*Z)) + (((-1)*Y^2)/(X*Z)) + ((1*Y^2)/(Z)))*p520

theorem free_zero_220 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 220=0 := by
  have h:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)))*p195 - (((1*Y^2)/(Z)))*p520

theorem free_zero_560 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 560=0 := by
  have h:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((((-1)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)))*p195 - ((((-1)*Y^2)/(Z)))*p520

theorem free_zero_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 7=0 := by
  have h:=pivot_289 X Y Z W a b hX hY hZ hW v hv
  have p495:=free_zero_495 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1)/(Y^2*W^2)))*p495 - (((1)/(X*Z*W^2)) + (((-1))/(Z*W^2)))*p520

theorem free_zero_454 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 454=0 := by
  have h:=pivot_288 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1*X*Y^2)/(W^2)))*p110 - ((((-1))/(X*Z*W^2)) + ((1)/(Z*W^2)))*p520

theorem free_zero_326 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 326=0 := by
  have h:=pivot_287 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X*Z*W^2)) + (((-1))/(Z*W^2)))*p520 - (((1*X*Y^2)/(W^2)))*p670

theorem free_zero_442 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 442=0 := by
  have h:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(W^2)))*p520 - ((((-1)*Z)/(X*Y^2*W^2)) + (((-1)*Z)/(W^2)))*p540

#print axioms free_zero_442

theorem free_zero_680 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 680=0 := by
  have h:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*X)/(Z)))*p520 - ((((-1))/(Y^2)) + (((-1)*X^2)/(Y^2)))*p540

theorem free_zero_295 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 295=0 := by
  have h:=pivot_284 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p685:=free_zero_685 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X)))*p200 - ((1))*p685

theorem free_zero_618 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 618=0 := by
  have h:=pivot_283 X Y Z W a b hX hY hZ hW v hv
  have p228:=free_zero_228 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p228 - (((1*Y^2)/(W^2)))*p670

theorem free_zero_338 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 338=0 := by
  have h:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p676:=free_zero_676 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Y^2*W^2)))*p195 - (((1)/(X)))*p676

theorem free_zero_205 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 205=0 := by
  have h:=pivot_281 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p595:=free_zero_595 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X)/(Y^2*Z)))*p195 - ((1))*p595

theorem free_zero_185 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 185=0 := by
  have h:=pivot_280 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p575:=free_zero_575 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2*Z)))*p195 - ((1))*p575

theorem free_zero_162 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 162=0 := by
  have h:=pivot_279 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p552:=free_zero_552 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(W^2)))*p110 - ((1))*p552

theorem free_zero_500 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 500=0 := by
  have h:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p220:=free_zero_220 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p110 - (((1)/(X)))*p220

theorem free_zero_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 290=0 := by
  have h:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X)))*p580 - ((1))*p680

theorem free_zero_490 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 490=0 := by
  have h:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X)))*p200 - (((-1)))*p680

theorem free_zero_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 95=0 := by
  have h:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p485:=free_zero_485 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p485 - ((((-1))/(X)))*p580

theorem free_zero_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 104=0 := by
  have h:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p442:=free_zero_442 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^4)/(Y^2*W^2)))*p195 - ((1*X))*p442

theorem free_zero_280 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 280=0 := by
  have h:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p560:=free_zero_560 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X)))*p560 - ((1))*p670

theorem free_zero_510 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 510=0 := by
  have h:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p540:=h540
  linear_combination h - (((1*X^3)/(Z)))*p195 - ((((-1))/(X)))*p540

theorem free_zero_625 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 625=0 := by
  have h:=pivot_271 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p572:=free_zero_572 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(X*Z)))*p195 - ((((-1)*W^2)/(X^2*Z)))*p572

theorem free_zero_320 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 320=0 := by
  have h:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((((-1)*X^2)/(Z)))*p195 - (((1)/(Z)))*p520

#print axioms free_zero_320

theorem free_zero_155 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 155=0 := by
  have h:=pivot_269 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p208:=free_zero_208 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X*Z)))*p195 - ((((-1)*W^2)/(X^2*Z)))*p208

theorem free_zero_460 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 460=0 := by
  have h:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1*X^2)/(Z)))*p195 - ((((-1))/(Z)))*p520

theorem free_zero_637 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 637=0 := by
  have h:=pivot_267 X Y Z W a b hX hY hZ hW v hv
  have p230:=free_zero_230 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^2*W^2)))*p230 - ((((-1)*Y^2*Z)/(X^3*W^2)))*p580

theorem free_zero_143 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 143=0 := by
  have h:=pivot_266 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p550:=free_zero_550 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2*Z)/(X^3*W^2)))*p200 - (((1*Z)/(X^2*W^2)))*p550

theorem free_zero_640 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 640=0 := by
  have h:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((1*X^3)/(Z)))*p195 - ((((-1))/(Z)))*p520

theorem free_zero_140 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 140=0 := by
  have h:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((((-1)*X^3)/(Z)))*p195 - (((1)/(Z)))*p520

theorem free_zero_128 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 128=0 := by
  have h:=pivot_263 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((((-1)*X^2*Y^2)/(W^2)))*p110 - (((1)/(Z*W^2)))*p520

theorem free_zero_652 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 652=0 := by
  have h:=pivot_262 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Z*W^2)))*p520 - ((((-1)*X^2*Y^2)/(W^2)))*p670

theorem free_zero_630 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 630=0 := by
  have h:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  have p540:=h540
  linear_combination h - (((1*Y^2)/(X*Z)))*p520 - (((-1)))*p540

theorem free_zero_494 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 494=0 := by
  have h:=pivot_260 X Y Z W a b hX hY hZ hW v hv
  have p620:=free_zero_620 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*W^2)))*p620 - ((((-1)*Y^2*Z)/(X*W^2)))*p680

theorem free_zero_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 286=0 := by
  have h:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p160:=free_zero_160 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*W^2)))*p160 - (((1*Y^2*Z)/(X*W^2)))*p680

theorem free_zero_235 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 235=0 := by
  have h:=pivot_258 X Y Z W a b hX hY hZ hW v hv
  have p495:=free_zero_495 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p495 - (((1)/(X^2)))*p630

theorem free_zero_545 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 545=0 := by
  have h:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p285:=free_zero_285 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p285 - ((((-1))/(X^2)))*p630

theorem free_zero_247 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 247=0 := by
  have h:=pivot_256 X Y Z W a b hX hY hZ hW v hv
  have p290:=free_zero_290 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p460:=free_zero_460 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2*Z)/(X^2*W^2)))*p290 - (((1*Z)/(X^3*W^2)))*p460

theorem free_zero_533 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 533=0 := by
  have h:=pivot_255 X Y Z W a b hX hY hZ hW v hv
  have p320:=free_zero_320 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p490:=free_zero_490 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^3*W^2)))*p320 - ((((-1)*Y^2*Z)/(X^2*W^2)))*p490

theorem free_zero_250 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 250=0 := by
  have h:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - ((1))*p510 - (((1)/(X*Z)))*p520

#print axioms free_zero_250

theorem free_zero_530 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 530=0 := by
  have h:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  have p520:=h520
  linear_combination h - (((-1)))*p510 - ((((-1))/(X*Z)))*p520

theorem free_zero_600 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 600=0 := by
  have h:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(Z)) + (((-1)*X*Y^2)/(Z)))*p520

theorem free_zero_132 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 132=0 := by
  have h:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2*Y^2)/(W^2)))*p670

theorem free_zero_648 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 648=0 := by
  have h:=pivot_250 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2*Y^2)/(W^2)))*p110

theorem free_zero_270 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 270=0 := by
  have h:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p510

theorem free_zero_150 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 150=0 := by
  have h:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p630

theorem free_zero_240 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 240=0 := by
  have h:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((1))*p540

theorem free_zero_100 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 100=0 := by
  have h:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p680

theorem free_zero_180 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 180=0 := by
  have h:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p600

theorem free_zero_570 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 570=0 := by
  have h:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p180

theorem free_zero_210 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 210=0 := by
  have h:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p600

theorem free_zero_182 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 182=0 := by
  have h:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p572:=free_zero_572 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p572

theorem free_zero_598 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 598=0 := by
  have h:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p208:=free_zero_208 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p208

theorem free_zero_190 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 190=0 := by
  have h:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p580

theorem free_zero_590 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 590=0 := by
  have h:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((1))*p200

theorem free_zero_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 120=0 := by
  have h:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(Z)))*p195

#print axioms free_zero_120

theorem free_zero_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 260=0 := by
  have h:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - ((1))*p520

theorem free_zero_374 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 374=0 := by
  have h:=pivot_236 X Y Z W a b hX hY hZ hW v hv
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p630

theorem free_zero_406 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 406=0 := by
  have h:=pivot_235 X Y Z W a b hX hY hZ hW v hv
  have p150:=free_zero_150 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p150

theorem free_zero_386 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 386=0 := by
  have h:=pivot_234 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2)/(Y^2*Z*W^2)))*p195

theorem free_zero_377 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 377=0 := by
  have h:=pivot_233 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^2*Y^2*W^2)))*p510

theorem free_zero_615 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 615=0 := by
  have h:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p338:=free_zero_338 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*W^2)/(X^2*Z)))*p338

theorem free_zero_507 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 507=0 := by
  have h:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p290:=free_zero_290 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X^2*W^2)))*p290

theorem free_zero_273 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 273=0 := by
  have h:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p490:=free_zero_490 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X^2*W^2)))*p490

theorem free_zero_165 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 165=0 := by
  have h:=pivot_229 X Y Z W a b hX hY hZ hW v hv
  have p442:=free_zero_442 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*W^2)/(X^2*Z)))*p442

theorem free_zero_403 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 403=0 := by
  have h:=pivot_228 X Y Z W a b hX hY hZ hW v hv
  have p270:=free_zero_270 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^2*Y^2*W^2)))*p270

theorem free_zero_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 61=0 := by
  have h:=pivot_227 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p120

theorem free_zero_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 59=0 := by
  have h:=pivot_226 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p600

theorem free_zero_719 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 719=0 := by
  have h:=pivot_225 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(Y^2*Z*W^2)))*p195

theorem free_zero_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 58=0 := by
  have h:=pivot_224 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X*Z*W^2)))*p260

theorem free_zero_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 57=0 := by
  have h:=pivot_223 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p180

theorem free_zero_718 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 718=0 := by
  have h:=pivot_222 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p540

#print axioms free_zero_718

theorem free_zero_717 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 717=0 := by
  have h:=pivot_221 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p240

theorem free_zero_716 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 716=0 := by
  have h:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1)/(Z*W^2)))*p520

theorem free_zero_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 19=0 := by
  have h:=pivot_219 X Y Z W a b hX hY hZ hW v hv
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p580

theorem free_zero_382 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 382=0 := by
  have h:=pivot_218 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p510

theorem free_zero_381 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 381=0 := by
  have h:=pivot_217 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p600

theorem free_zero_379 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 379=0 := by
  have h:=pivot_216 X Y Z W a b hX hY hZ hW v hv
  have p220:=free_zero_220 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p220

theorem free_zero_376 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 376=0 := by
  have h:=pivot_215 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p180

theorem free_zero_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 22=0 := by
  have h:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p280:=free_zero_280 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p280

theorem free_zero_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 54=0 := by
  have h:=pivot_213 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2)/(Z*W^2)))*p195

theorem free_zero_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 51=0 := by
  have h:=pivot_212 X Y Z W a b hX hY hZ hW v hv
  have p560:=free_zero_560 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p560

theorem free_zero_369 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 369=0 := by
  have h:=pivot_211 X Y Z W a b hX hY hZ hW v hv
  have p640:=free_zero_640 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p640

theorem free_zero_368 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 368=0 := by
  have h:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p615:=free_zero_615 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(Y^2*W^2)))*p615

theorem free_zero_366 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 366=0 := by
  have h:=pivot_209 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(X*W^2)))*p540

theorem free_zero_365 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 365=0 := by
  have h:=pivot_208 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X^3*Z)))*p260

theorem free_zero_363 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 363=0 := by
  have h:=pivot_207 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p240

theorem free_zero_361 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 361=0 := by
  have h:=pivot_206 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p600

#print axioms free_zero_361

theorem free_zero_359 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 359=0 := by
  have h:=pivot_205 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1)/(X^3*Z*W^2)))*p520

theorem free_zero_358 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 358=0 := by
  have h:=pivot_204 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p180

theorem free_zero_357 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 357=0 := by
  have h:=pivot_203 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(Z*W^2)))*p195

theorem free_zero_356 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 356=0 := by
  have h:=pivot_202 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2*W^2)))*p510

theorem free_zero_352 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 352=0 := by
  have h:=pivot_201 X Y Z W a b hX hY hZ hW v hv
  have p285:=free_zero_285 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(Y^2*W^2)))*p285

theorem free_zero_351 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 351=0 := by
  have h:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p260

theorem free_zero_342 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 342=0 := by
  have h:=pivot_199 X Y Z W a b hX hY hZ hW v hv
  have p160:=free_zero_160 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X*W^2)))*p160

theorem free_zero_340 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 340=0 := by
  have h:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p150:=free_zero_150 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2)))*p150

theorem free_zero_335 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 335=0 := by
  have h:=pivot_197 X Y Z W a b hX hY hZ hW v hv
  have p132:=free_zero_132 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*W^2)/(X^3*Y^2)))*p132

theorem free_zero_315 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 315=0 := by
  have h:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p100:=free_zero_100 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3)))*p100

theorem free_zero_96 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 96=0 := by
  have h:=pivot_195 X Y Z W a b hX hY hZ hW v hv
  have p310:=free_zero_310 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X*Y^2)/(W^2)))*p310

theorem free_zero_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 84=0 := by
  have h:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p285:=free_zero_285 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(W^2)))*p285

theorem free_zero_455 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 455=0 := by
  have h:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p210:=free_zero_210 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^2*Y^2)))*p210

theorem free_zero_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 70=0 := by
  have h:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2)))*p180

theorem free_zero_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 69=0 := by
  have h:=pivot_191 X Y Z W a b hX hY hZ hW v hv
  have p160:=free_zero_160 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p160

theorem free_zero_711 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 711=0 := by
  have h:=pivot_190 X Y Z W a b hX hY hZ hW v hv
  have p620:=free_zero_620 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p620

#print axioms free_zero_711

theorem free_zero_708 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 708=0 := by
  have h:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p570:=free_zero_570 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(W^2)))*p570

theorem free_zero_312 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 312=0 := by
  have h:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - (((1*Z)/(W^2)))*p540

theorem free_zero_700 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 700=0 := by
  have h:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2)))*p510

theorem free_zero_696 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 696=0 := by
  have h:=pivot_186 X Y Z W a b hX hY hZ hW v hv
  have p495:=free_zero_495 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(W^2)))*p495

theorem free_zero_480 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 480=0 := by
  have h:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(Z)))*p260

theorem free_zero_684 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 684=0 := by
  have h:=pivot_184 X Y Z W a b hX hY hZ hW v hv
  have p470:=free_zero_470 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X*Y^2)/(W^2)))*p470

theorem free_zero_465 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 465=0 := by
  have h:=pivot_183 X Y Z W a b hX hY hZ hW v hv
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3)))*p680

theorem free_zero_675 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 675=0 := by
  have h:=pivot_182 X Y Z W a b hX hY hZ hW v hv
  have p460:=free_zero_460 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3)))*p460

theorem free_zero_456 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 456=0 := by
  have h:=pivot_181 X Y Z W a b hX hY hZ hW v hv
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X*Y^2)/(W^2)))*p670

theorem free_zero_445 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 445=0 := by
  have h:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  have p648:=free_zero_648 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*W^2)/(X^3*Y^2)))*p648

theorem free_zero_438 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 438=0 := by
  have h:=pivot_179 X Y Z W a b hX hY hZ hW v hv
  have p620:=free_zero_620 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X*W^2)))*p620

theorem free_zero_435 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 435=0 := by
  have h:=pivot_178 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3)))*p600

theorem free_zero_430 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 430=0 := by
  have h:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(X*Y^2)))*p540

theorem free_zero_429 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 429=0 := by
  have h:=pivot_176 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p520

theorem free_zero_428 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 428=0 := by
  have h:=pivot_175 X Y Z W a b hX hY hZ hW v hv
  have p495:=free_zero_495 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(Y^2*W^2)))*p495

theorem free_zero_424 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 424=0 := by
  have h:=pivot_174 X Y Z W a b hX hY hZ hW v hv
  have p270:=free_zero_270 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2*W^2)))*p270

#print axioms free_zero_424

theorem free_zero_423 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 423=0 := by
  have h:=pivot_173 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p120

theorem free_zero_422 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 422=0 := by
  have h:=pivot_172 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p600

theorem free_zero_421 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 421=0 := by
  have h:=pivot_171 X Y Z W a b hX hY hZ hW v hv
  have p480:=free_zero_480 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p480

theorem free_zero_419 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 419=0 := by
  have h:=pivot_170 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p180

theorem free_zero_417 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 417=0 := by
  have h:=pivot_169 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p540

theorem free_zero_415 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 415=0 := by
  have h:=pivot_168 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1)/(X^3*Z)))*p520

theorem free_zero_412 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 412=0 := by
  have h:=pivot_167 X Y Z W a b hX hY hZ hW v hv
  have p165:=free_zero_165 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^3)/(Y^2*W^2)))*p165

theorem free_zero_411 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 411=0 := by
  have h:=pivot_166 X Y Z W a b hX hY hZ hW v hv
  have p140:=free_zero_140 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p140

theorem free_zero_370 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 370=0 := by
  have h:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2)/(Y^2*Z)))*p195

theorem free_zero_348 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 348=0 := by
  have h:=pivot_164 X Y Z W a b hX hY hZ hW v hv
  have p210:=free_zero_210 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(W^2)))*p210

theorem free_zero_345 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 345=0 := by
  have h:=pivot_163 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3)))*p180

theorem free_zero_330 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 330=0 := by
  have h:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X)))*p120

theorem free_zero_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 105=0 := by
  have h:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p320:=free_zero_320 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3)))*p320

theorem free_zero_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 80=0 := by
  have h:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p270:=free_zero_270 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2)))*p270

theorem free_zero_729 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 729=0 := by
  have h:=pivot_159 X Y Z W a b hX hY hZ hW v hv
  have p220:=free_zero_220 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^3*W^2)))*p220

theorem free_zero_726 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 726=0 := by
  have h:=pivot_158 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p120

#print axioms free_zero_726

theorem free_zero_710 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 710=0 := by
  have h:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2)))*p600

theorem free_zero_758 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 758=0 := by
  have h:=pivot_156 X Y Z W a b hX hY hZ hW v hv
  have p500:=free_zero_500 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p500

theorem free_zero_450 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 450=0 := by
  have h:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2)/(Z)))*p195

theorem free_zero_440 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 440=0 := by
  have h:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(Y^2)))*p630

theorem free_zero_410 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 410=0 := by
  have h:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2)))*p120

theorem free_zero_401 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 401=0 := by
  have h:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p560:=free_zero_560 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p560

theorem free_zero_350 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 350=0 := by
  have h:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2)))*p240

theorem free_zero_300 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 300=0 := by
  have h:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(Z)))*p520

theorem free_zero_761 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 761=0 := by
  have h:=pivot_149 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p200

theorem free_zero_468 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 468=0 := by
  have h:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(W^2)))*p240

theorem free_zero_432 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 432=0 := by
  have h:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p570:=free_zero_570 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(W^2)))*p570

theorem free_zero_414 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 414=0 := by
  have h:=pivot_146 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p240

theorem free_zero_408 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 408=0 := by
  have h:=pivot_145 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(Z*W^2)))*p520

theorem free_zero_404 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 404=0 := by
  have h:=pivot_144 X Y Z W a b hX hY hZ hW v hv
  have p710:=free_zero_710 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X)/(W^2)))*p710

theorem free_zero_402 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 402=0 := by
  have h:=pivot_143 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^2)/(Z*W^2)))*p195

theorem free_zero_399 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 399=0 := by
  have h:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p180

#print axioms free_zero_399

theorem free_zero_398 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 398=0 := by
  have h:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p80:=free_zero_80 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p80

theorem free_zero_397 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 397=0 := by
  have h:=pivot_140 X Y Z W a b hX hY hZ hW v hv
  have p696:=free_zero_696 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2)))*p696

theorem free_zero_394 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 394=0 := by
  have h:=pivot_139 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p120

theorem free_zero_378 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 378=0 := by
  have h:=pivot_138 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*W^2)))*p120

theorem free_zero_372 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 372=0 := by
  have h:=pivot_137 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(Z*W^2)))*p260

theorem free_zero_324 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 324=0 := by
  have h:=pivot_136 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X*Y^2)/(W^2)))*p110

theorem free_zero_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 64=0 := by
  have h:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(Z*W^2)))*p260

theorem free_zero_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 63=0 := by
  have h:=pivot_134 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p540

theorem free_zero_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 62=0 := by
  have h:=pivot_133 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p240

theorem free_zero_723 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 723=0 := by
  have h:=pivot_132 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*W^2)))*p600

theorem free_zero_722 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 722=0 := by
  have h:=pivot_131 X Y Z W a b hX hY hZ hW v hv
  have p300:=free_zero_300 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X*Y^2*W^2)))*p300

theorem free_zero_721 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 721=0 := by
  have h:=pivot_130 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^3*Y^2*W^2)))*p180

theorem free_zero_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 29=0 := by
  have h:=pivot_129 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1)/(X^3*Z*W^2)))*p520

theorem free_zero_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 27=0 := by
  have h:=pivot_128 X Y Z W a b hX hY hZ hW v hv
  have p270:=free_zero_270 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p270

theorem free_zero_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 21=0 := by
  have h:=pivot_127 X Y Z W a b hX hY hZ hW v hv
  have p70:=free_zero_70 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^2*W^2)))*p70

theorem free_zero_769 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 769=0 := by
  have h:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  have p110:=free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p110

#print axioms free_zero_769

theorem free_zero_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 14=0 := by
  have h:=pivot_125 X Y Z W a b hX hY hZ hW v hv
  have p210:=free_zero_210 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p210

theorem free_zero_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 11=0 := by
  have h:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p670:=free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p670

theorem free_zero_764 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 764=0 := by
  have h:=pivot_123 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p240

theorem free_zero_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 16=0 := by
  have h:=pivot_122 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p540

theorem free_zero_749 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 749=0 := by
  have h:=pivot_121 X Y Z W a b hX hY hZ hW v hv
  have p150:=free_zero_150 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*Y^2*W^2)))*p150

theorem free_zero_748 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 748=0 := by
  have h:=pivot_120 X Y Z W a b hX hY hZ hW v hv
  have p480:=free_zero_480 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p480

theorem free_zero_747 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 747=0 := by
  have h:=pivot_119 X Y Z W a b hX hY hZ hW v hv
  have p330:=free_zero_330 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p330

theorem free_zero_745 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 745=0 := by
  have h:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  have p210:=free_zero_210 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*Y^2)))*p210

theorem free_zero_738 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 738=0 := by
  have h:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  have p105:=free_zero_105 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^2)/(W^2)))*p105

theorem free_zero_732 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 732=0 := by
  have h:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  have p80:=free_zero_80 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(W^2)))*p80

theorem free_zero_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 48=0 := by
  have h:=pivot_115 X Y Z W a b hX hY hZ hW v hv
  have p700:=free_zero_700 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(W^2)))*p700

theorem free_zero_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 42=0 := by
  have h:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p675:=free_zero_675 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*X^2)/(W^2)))*p675

theorem free_zero_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 35=0 := by
  have h:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p570:=free_zero_570 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*Y^2)))*p570

theorem free_zero_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 33=0 := by
  have h:=pivot_112 X Y Z W a b hX hY hZ hW v hv
  have p450:=free_zero_450 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p450

theorem free_zero_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 32=0 := by
  have h:=pivot_111 X Y Z W a b hX hY hZ hW v hv
  have p300:=free_zero_300 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p300

theorem free_zero_759 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 759=0 := by
  have h:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  have p710:=free_zero_710 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1)*Y^2)/(X^2*W^2)))*p710

#print axioms free_zero_759

theorem free_zero_753 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 753=0 := by
  have h:=pivot_109 X Y Z W a b hX hY hZ hW v hv
  have p510:=free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*W^2)))*p510

theorem free_zero_766 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 766=0 := by
  have h:=pivot_108 X Y Z W a b hX hY hZ hW v hv
  have p570:=free_zero_570 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p570

theorem free_zero_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 31=0 := by
  have h:=pivot_107 X Y Z W a b hX hY hZ hW v hv
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(X^2*Y^2*W^2)))*p630

theorem free_zero_751 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 751=0 := by
  have h:=pivot_106 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1)/(X^3*Z*W^2)))*p260

theorem free_zero_772 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 772=0 := by
  have h:=pivot_105 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2*W^2)))*p120

theorem free_zero_771 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 771=0 := by
  have h:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(X^3*Z*W^2)))*p260

theorem free_zero_744 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 744=0 := by
  have h:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(W^2)))*p180

theorem free_zero_741 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 741=0 := by
  have h:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^3*W^2)))*p600

theorem free_zero_740 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 740=0 := by
  have h:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - ((((-1))/(Y^2)))*p120

theorem free_zero_735 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 735=0 := by
  have h:=pivot_100 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(X^3*Z)))*p520

theorem free_zero_730 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 730=0 := by
  have h:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p468:=free_zero_468 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X*Y^2*Z)))*p468

theorem free_zero_728 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 728=0 := by
  have h:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p450:=free_zero_450 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X*Z)/(Y^2*W^2)))*p450

theorem free_zero_325 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 325=0 := by
  have h:=pivot_97 X Y Z W a b hX hY hZ hW v hv
  have p708:=free_zero_708 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z*W^2)/(X^3*Y^2)))*p708

theorem free_zero_705 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 705=0 := by
  have h:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  have p312:=free_zero_312 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X^3*Z)))*p312

theorem free_zero_702 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 702=0 := by
  have h:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p300:=free_zero_300 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*W^2)))*p300

theorem free_zero_690 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 690=0 := by
  have h:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(X*Z)))*p260

#print axioms free_zero_690

theorem free_zero_234 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 234=0 := by
  have h:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p680:=free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X*W^2)))*p680

theorem free_zero_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 225=0 := by
  have h:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p676:=free_zero_676 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*W^2)/(X^3*Z)))*p676

theorem free_zero_663 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 663=0 := by
  have h:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p200:=free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X^3*W^2)))*p200

theorem free_zero_660 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 660=0 := by
  have h:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Z)))*p195

theorem free_zero_650 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 650=0 := by
  have h:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*Y^2)))*p180

theorem free_zero_156 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 156=0 := by
  have h:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p630:=free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X*Z)/(W^2)))*p630

theorem free_zero_624 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 624=0 := by
  have h:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p150:=free_zero_150 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X*Z)/(W^2)))*p150

theorem free_zero_130 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 130=0 := by
  have h:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p600:=free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*Y^2)))*p600

theorem free_zero_585 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 585=0 := by
  have h:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^3)))*p120

theorem free_zero_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 117=0 := by
  have h:=pivot_84 X Y Z W a b hX hY hZ hW v hv
  have p580:=free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X^3*W^2)))*p580

theorem free_zero_555 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 555=0 := by
  have h:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p104:=free_zero_104 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*W^2)/(X^3*Z)))*p104

theorem free_zero_546 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 546=0 := by
  have h:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p100:=free_zero_100 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2*Z)/(X*W^2)))*p100

theorem free_zero_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 90=0 := by
  have h:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(X*Z)))*p520

theorem free_zero_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 78=0 := by
  have h:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p480:=free_zero_480 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*W^2)))*p480

theorem free_zero_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 75=0 := by
  have h:=pivot_79 X Y Z W a b hX hY hZ hW v hv
  have p468:=free_zero_468 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X^3*Z)))*p468

theorem free_zero_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 72=0 := by
  have h:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p455:=free_zero_455 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3*Y^2)/(Z*W^2)))*p455

#print axioms free_zero_72

theorem free_zero_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 52=0 := by
  have h:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p330:=free_zero_330 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X*Z)/(Y^2*W^2)))*p330

theorem free_zero_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 50=0 := by
  have h:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p312:=free_zero_312 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X*Y^2*Z)))*p312

theorem free_zero_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 45=0 := by
  have h:=pivot_75 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(X^3*Z)))*p260

theorem free_zero_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 40=0 := by
  have h:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Y^2*Z)))*p195

theorem free_zero_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 39=0 := by
  have h:=pivot_73 X Y Z W a b hX hY hZ hW v hv
  have p180:=free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^3*W^2)))*p180

theorem free_zero_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 36=0 := by
  have h:=pivot_72 X Y Z W a b hX hY hZ hW v hv
  have p130:=free_zero_130 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X*Y^2)/(Z*W^2)))*p130

theorem free_zero_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 26=0 := by
  have h:=pivot_71 X Y Z W a b hX hY hZ hW v hv
  have p660:=free_zero_660 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*Y^2*W^2)))*p660

theorem free_zero_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 25=0 := by
  have h:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p624:=free_zero_624 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X^3*Y^2*Z)))*p624

theorem free_zero_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 24=0 := by
  have h:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p585:=free_zero_585 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Z*W^2)))*p585

theorem free_zero_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 18=0 := by
  have h:=pivot_68 X Y Z W a b hX hY hZ hW v hv
  have p260:=free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Y^2)/(X*Z*W^2)))*p260

theorem free_zero_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 13=0 := by
  have h:=pivot_67 X Y Z W a b hX hY hZ hW v hv
  have p540:=h540
  linear_combination h - (((1*Z)/(X^3*Y^2*W^2)))*p540

theorem free_zero_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 9=0 := by
  have h:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(X^3*Z*W^2)))*p520

theorem free_zero_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 8=0 := by
  have h:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Y^2*Z*W^2)))*p195

theorem free_zero_762 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 762=0 := by
  have h:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  have p520:=h520
  linear_combination h - (((1*Y^2)/(X*Z*W^2)))*p520

theorem free_zero_756 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 756=0 := by
  have h:=pivot_63 X Y Z W a b hX hY hZ hW v hv
  have p195:=free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*X^3)/(Z*W^2)))*p195

theorem free_zero_755 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 755=0 := by
  have h:=pivot_62 X Y Z W a b hX hY hZ hW v hv
  have p156:=free_zero_156 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*W^2)/(X^3*Y^2*Z)))*p156

#print axioms free_zero_755

theorem free_zero_754 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 754=0 := by
  have h:=pivot_61 X Y Z W a b hX hY hZ hW v hv
  have p120:=free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X*Y^2*W^2)))*p120

theorem free_zero_767 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 767=0 := by
  have h:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  have p240:=free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  linear_combination h - (((1*Z)/(X^3*Y^2*W^2)))*p240

theorem free_zero_391 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 391=0 := by
  have h:=pivot_59 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_389 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 389=0 := by
  have h:=pivot_58 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 56=0 := by
  have h:=pivot_57 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_385 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 385=0 := by
  have h:=pivot_56 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_364 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 364=0 := by
  have h:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_362 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 362=0 := by
  have h:=pivot_54 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_355 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 355=0 := by
  have h:=pivot_53 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_354 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 354=0 := by
  have h:=pivot_52 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 55=0 := by
  have h:=pivot_51 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_714 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 714=0 := by
  have h:=pivot_50 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_426 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 426=0 := by
  have h:=pivot_49 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_418 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 418=0 := by
  have h:=pivot_48 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_416 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 416=0 := by
  have h:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 66=0 := by
  have h:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

#print axioms free_zero_66

theorem free_zero_725 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 725=0 := by
  have h:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_425 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 425=0 := by
  have h:=pivot_44 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_380 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 380=0 := by
  have h:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_375 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 375=0 := by
  have h:=pivot_42 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 28=0 := by
  have h:=pivot_41 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 65=0 := by
  have h:=pivot_40 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_420 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 420=0 := by
  have h:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_405 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 405=0 := by
  have h:=pivot_38 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_400 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 400=0 := by
  have h:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_396 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 396=0 := by
  have h:=pivot_36 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_395 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 395=0 := by
  have h:=pivot_35 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_393 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 393=0 := by
  have h:=pivot_34 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_392 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 392=0 := by
  have h:=pivot_33 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_387 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 387=0 := by
  have h:=pivot_32 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_776 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 776=0 := by
  have h:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_720 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 720=0 := by
  have h:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

#print axioms free_zero_720

theorem free_zero_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 60=0 := by
  have h:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 20=0 := by
  have h:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 12=0 := by
  have h:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 4=0 := by
  have h:=pivot_26 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_760 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 760=0 := by
  have h:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_768 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 768=0 := by
  have h:=pivot_24 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_390 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 390=0 := by
  have h:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_388 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 388=0 := by
  have h:=pivot_22 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_384 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 384=0 := by
  have h:=pivot_21 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_752 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 752=0 := by
  have h:=pivot_20 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_715 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 715=0 := by
  have h:=pivot_19 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_360 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 360=0 := by
  have h:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_724 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 724=0 := by
  have h:=pivot_17 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_779 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 779=0 := by
  have h:=pivot_16 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_778 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 778=0 := by
  have h:=pivot_15 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_777 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 777=0 := by
  have h:=pivot_14 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

#print axioms free_zero_777

theorem free_zero_775 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 775=0 := by
  have h:=pivot_13 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_774 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 774=0 := by
  have h:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_770 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 770=0 := by
  have h:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 30=0 := by
  have h:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 15=0 := by
  have h:=pivot_9 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 10=0 := by
  have h:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 6=0 := by
  have h:=pivot_7 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 5=0 := by
  have h:=pivot_6 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 3=0 := by
  have h:=pivot_5 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 2=0 := by
  have h:=pivot_4 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 1=0 := by
  have h:=pivot_3 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_750 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 750=0 := by
  have h:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_765 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 765=0 := by
  have h:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

theorem free_zero_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : v 0=0 := by
  have h:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination h

#print axioms free_zero_0

end SmallLevelTwentySixUnitMMM.FreeKernel
end
end

/-! ## SmallLevelTwentySixUnitMMMFreeKernelTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentySixUnitMMM.FreeKernel. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMMFreeKernelV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMM.FreeKernel
open Complex

/-- Vanishing of the two free coordinates forces the entire original
source kernel to vanish, even at zeros of every residual minor. -/
theorem source_zero_of_free (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h520 : v 520=0) (h540 : v 540=0) : ∀ j : Fin 320,v (support j)=0 := by
  intro j
  fin_cases j
  · exact free_zero_0 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_1 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_2 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_3 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_4 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_5 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_6 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_7 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_8 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_9 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_10 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_11 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_12 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_13 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_14 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_15 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_16 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_18 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_19 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_20 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_21 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_22 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_24 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_25 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_26 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_27 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_28 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_29 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_30 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_31 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_32 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_33 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_35 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_36 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_39 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_40 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_42 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_44 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_45 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_48 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_50 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_51 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_52 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_54 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_55 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_56 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_57 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_58 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_59 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_60 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_61 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_62 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_63 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_64 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_65 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_66 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_69 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_70 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_72 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_75 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_78 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_80 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_84 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_90 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_95 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_96 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_100 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_104 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_105 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_110 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_117 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_120 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_128 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_130 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_132 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_140 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_143 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_150 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_155 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_156 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_160 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_162 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_165 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_170 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_180 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_182 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_185 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_190 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_195 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_200 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_205 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_208 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_210 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_220 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_225 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_228 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_230 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_234 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_235 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_240 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_247 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_250 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_260 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_270 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_273 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_280 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_285 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_286 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_290 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_295 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_300 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_310 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_312 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_315 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_320 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_324 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_325 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_326 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_330 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_335 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_338 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_340 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_342 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_345 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_348 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_350 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_351 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_352 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_354 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_355 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_356 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_357 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_358 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_359 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_360 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_361 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_362 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_363 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_364 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_365 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_366 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_368 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_369 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_370 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_372 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_374 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_375 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_376 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_377 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_378 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_379 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_380 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_381 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_382 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_384 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_385 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_386 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_387 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_388 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_389 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_390 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_391 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_392 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_393 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_394 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_395 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_396 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_397 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_398 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_399 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_400 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_401 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_402 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_403 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_404 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_405 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_406 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_408 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_410 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_411 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_412 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_414 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_415 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_416 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_417 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_418 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_419 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_420 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_421 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_422 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_423 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_424 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_425 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_426 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_428 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_429 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_430 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_432 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_435 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_438 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_440 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_442 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_445 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_450 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_454 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_455 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_456 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_460 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_465 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_468 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_470 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_480 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_485 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_490 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_494 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_495 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_500 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_507 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_510 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact h520
  · exact free_zero_530 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_533 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact h540
  · exact free_zero_545 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_546 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_550 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_552 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_555 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_560 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_570 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_572 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_575 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_580 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_585 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_590 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_595 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_598 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_600 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_610 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_615 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_618 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_620 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_624 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_625 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_630 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_637 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_640 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_648 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_650 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_652 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_660 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_663 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_670 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_675 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_676 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_680 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_684 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_685 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_690 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_696 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_700 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_702 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_705 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_708 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_710 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_711 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_714 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_715 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_716 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_717 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_718 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_719 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_720 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_721 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_722 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_723 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_724 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_725 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_726 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_728 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_729 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_730 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_732 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_735 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_736 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_738 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_740 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_741 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_744 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_745 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_747 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_748 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_749 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_750 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_751 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_752 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_753 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_754 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_755 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_756 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_758 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_759 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_760 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_761 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_762 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_764 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_765 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_766 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_767 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_768 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_769 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_770 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_771 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_772 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_774 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_775 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_776 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_777 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_778 X Y Z W a b hX hY hZ hW v hv h520 h540
  · exact free_zero_779 X Y Z W a b hX hY hZ hW v hv h520 h540

#print axioms source_zero_of_free
end SmallLevelTwentySixUnitMMM.FreeKernel
end
end

/-! ## SmallLevelTwentySixReplayFreeKernelV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMM.FreeKernel

/-- The Taylor replay uses coordinate300 in place of520. The triangular
source relation changes between them by the nonzero factor Y²/Z. -/
theorem source_zero_of_replay_free (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h300 : v 300=0) (h540 : v 540=0) : ∀ j : Fin 320,v (support j)=0 := by
  have h := pivot_150 X Y Z W a b hX hY hZ hW v hv
  simp only [h300,mul_zero,zero_add,one_mul] at h
  have h520 := (mul_eq_zero.mp h).resolve_left (div_ne_zero (pow_ne_zero 2 hY) hZ)
  exact source_zero_of_free X Y Z W a b hX hY hZ hW v hv h520 h540

#print axioms source_zero_of_replay_free
end SmallLevelTwentySixUnitMMM.FreeKernel
end
end
end
