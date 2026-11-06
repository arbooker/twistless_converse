module
public import SmallLevelThirtyFourGridSlopeFromLeadingV1
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value263 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((2*Y^2*Z)/(3*X)))*v 10

theorem source_slope_263 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 110=value263 X Y Z W a b v := by
  have hsel : selectedSource 110=.word 107 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 107=(-51:ℚ) from rfl,
    show gridGroupIndex 107=255 from rfl]
  norm_num [value263,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_263

def value266 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-255)*X)/(Y^2*Z*W^2)))*v 255

theorem source_slope_266 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 112=value266 X Y Z W a b v := by
  have hsel : selectedSource 112=.word 109 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 109=(2/15:ℚ) from rfl,
    show gridGroupIndex 109=2 from rfl]
  norm_num [value266,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_266

def value275 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-102)*W^2)/(5*X*Y^2*Z)))*v 204

theorem source_slope_275 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 116=value275 X Y Z W a b v := by
  have hsel : selectedSource 116=.word 113 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 113=(5/3:ℚ) from rfl,
    show gridGroupIndex 113=25 from rfl]
  norm_num [value275,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_275

def value277 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-15)*X*Z)/(Y^2*W^2)))*v 285

theorem source_slope_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 117=value277 X Y Z W a b v := by
  have hsel : selectedSource 117=.word 114 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 114=(34/15:ℚ) from rfl,
    show gridGroupIndex 114=34 from rfl]
  norm_num [value277,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_277

def value279 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X*W^2)/(5*Y^2*Z)))*v 357

theorem source_slope_279 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 118=value279 X Y Z W a b v := by
  have hsel : selectedSource 118=.word 115 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 115=(10/3:ℚ) from rfl,
    show gridGroupIndex 115=50 from rfl]
  norm_num [value279,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_279

def value285 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-17)*X*W^2)/(5*Z)))*v 459

theorem source_slope_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 119=value285 X Y Z W a b v := by
  have hsel : selectedSource 119=.word 116 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 116=(10:ℚ) from rfl,
    show gridGroupIndex 116=150 from rfl]
  norm_num [value285,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_285

def value286 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-10)*Y^2*Z)/(3*X*W^2)))*v 460

theorem source_slope_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 120=value286 X Y Z W a b v := by
  have hsel : selectedSource 120=.word 117 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 117=(51/5:ℚ) from rfl,
    show gridGroupIndex 117=153 from rfl]
  norm_num [value286,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_286

def value288 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-34)*Y^2*W^2)/(15*X*Z)))*v 476

theorem source_slope_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 121=value288 X Y Z W a b v := by
  have hsel : selectedSource 121=.word 118 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 118=(15:ℚ) from rfl,
    show gridGroupIndex 118=225 from rfl]
  norm_num [value288,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_288

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value290 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-5)*X*Y^2*Z)/(3*W^2)))*v 485

theorem source_slope_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 122=value290 X Y Z W a b v := by
  have hsel : selectedSource 122=.word 119 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 119=(102/5:ℚ) from rfl,
    show gridGroupIndex 119=306 from rfl]
  norm_num [value290,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_290

def value296 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-1020))/(Y^2*W^2)))*v 105

theorem source_slope_296 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 124=value296 X Y Z W a b v := by
  have hsel : selectedSource 124=.word 121 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 121=(-68/15:ℚ) from rfl,
    show gridGroupIndex 121=7 from rfl]
  norm_num [value296,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_296

def value297 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((1020)/(Y^2*W^2)))*v 390

theorem source_slope_297 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 125=value297 X Y Z W a b v := by
  have hsel : selectedSource 125=.word 122 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 122=(68/15:ℚ) from rfl,
    show gridGroupIndex 122=8 from rfl]
  norm_num [value297,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_297

def value305 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((68*Y^2*W^2)/(15)))*v 502

theorem source_slope_305 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 126=value305 X Y Z W a b v := by
  have hsel : selectedSource 126=.word 123 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 123=(1020:ℚ) from rfl,
    show gridGroupIndex 123=120 from rfl]
  norm_num [value305,sourceRows,sourceRowsPart7] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_305

def value319 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-816)*W^2)/(5*Y^2*Z)))*v 459

theorem source_slope_319 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 128=value319 X Y Z W a b v := by
  have hsel : selectedSource 128=.word 125 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 125=(80/3:ℚ) from rfl,
    show gridGroupIndex 125=35 from rfl]
  norm_num [value319,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_319

def value326 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-17)*X*Y^2)/(3)))*v 485

theorem source_slope_326 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 130=value326 X Y Z W a b v := by
  have hsel : selectedSource 130=.word 127 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 127=(-102:ℚ) from rfl,
    show gridGroupIndex 127=180 from rfl]
  norm_num [value326,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_326

def value328 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X*W^2)/(5*Y^2)))*v 489

theorem source_slope_328 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 131=value328 X Y Z W a b v := by
  have hsel : selectedSource 131=.word 128 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 128=(-170/3:ℚ) from rfl,
    show gridGroupIndex 128=220 from rfl]
  norm_num [value328,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_328

def value331 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-102)*W^2)/(5*X*Y^2)))*v 498

theorem source_slope_331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 132=value331 X Y Z W a b v := by
  have hsel : selectedSource 132=.word 129 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 129=(-85/3:ℚ) from rfl,
    show gridGroupIndex 129=245 from rfl]
  norm_num [value331,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_331

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value344 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((170)/(X*W^2)))*v 330

theorem source_slope_344 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 134=value344 X Y Z W a b v := by
  have hsel : selectedSource 134=.word 131 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 131=(17/5:ℚ) from rfl,
    show gridGroupIndex 131=273 from rfl]
  norm_num [value344,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_344

def value352 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((17*X))*v 465

theorem source_slope_352 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 138=value352 X Y Z W a b v := by
  have hsel : selectedSource 138=.word 135 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 135=(34:ℚ) from rfl,
    show gridGroupIndex 135=300 from rfl]
  norm_num [value352,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_352

def value355 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34*W^2)/(5*X)))*v 474

theorem source_slope_355 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 140=value355 X Y Z W a b v := by
  have hsel : selectedSource 140=.word 137 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 137=(85:ℚ) from rfl,
    show gridGroupIndex 137=345 from rfl]
  norm_num [value355,sourceRows,sourceRowsPart8] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_355

def value379 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X)/(Y^2)))*v 75

theorem source_slope_379 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 144=value379 X Y Z W a b v := by
  have hsel : selectedSource 144=.word 141 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 141=(-34/3:ℚ) from rfl,
    show gridGroupIndex 141=230 from rfl]
  norm_num [value379,sourceRows,sourceRowsPart9] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_379

def value384 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-255)*X)/(Y^2*W^2)))*v 255

theorem source_slope_384 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 148=value384 X Y Z W a b v := by
  have hsel : selectedSource 148=.word 145 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 145=(-34/15:ℚ) from rfl,
    show gridGroupIndex 145=238 from rfl]
  norm_num [value384,sourceRows,sourceRowsPart9] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_384

def value393 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((51*X)/(Y^2)))*v 495

theorem source_slope_393 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 155=value393 X Y Z W a b v := by
  have hsel : selectedSource 155=.word 152 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 152=(34/3:ℚ) from rfl,
    show gridGroupIndex 152=250 from rfl]
  norm_num [value393,sourceRows,sourceRowsPart9] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_393

def value399 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((51*X*W^2)/(5*Y^2)))*v 21

theorem source_slope_399 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 157=value399 X Y Z W a b v := by
  have hsel : selectedSource 157=.word 154 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 154=(170/3:ℚ) from rfl,
    show gridGroupIndex 154=290 from rfl]
  norm_num [value399,sourceRows,sourceRowsPart9] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_399

def value401 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((17*X*Y^2)/(3)))*v 25

theorem source_slope_401 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 158=value401 X Y Z W a b v := by
  have hsel : selectedSource 158=.word 155 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 155=(102:ℚ) from rfl,
    show gridGroupIndex 155=330 from rfl]
  norm_num [value401,sourceRows,sourceRowsPart9] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_401

end SmallLevelThirtyFourSlopeLiteralMMP
end

section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value404 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((-255)*X))*v 479

theorem source_slope_404 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 161=value404 X Y Z W a b v := by
  have hsel : selectedSource 161=.word 158 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 158=(-510:ℚ) from rfl,
    show gridGroupIndex 158=14 from rfl]
  norm_num [value404,sourceRows,sourceRowsPart10] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_404

def value411 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((30*Z)/(W^2)))*v 110

theorem source_slope_411 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 162=value411 X Y Z W a b v := by
  have hsel : selectedSource 162=.word 159 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 159=(-102/5:ℚ) from rfl,
    show gridGroupIndex 159=68 from rfl]
  norm_num [value411,sourceRows,sourceRowsPart10] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_411

def value485 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-510))/(X*Y^2*W^2)))*v 210

theorem source_slope_485 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 164=value485 X Y Z W a b v := by
  have hsel : selectedSource 164=.word 161 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 161=(-17/15:ℚ) from rfl,
    show gridGroupIndex 161=479 from rfl]
  norm_num [value485,sourceRows,sourceRowsPart10] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_485

def value636 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-510))/(X*W^2)))*v 40

theorem source_slope_636 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 167=value636 X Y Z W a b v := by
  have hsel : selectedSource 167=.word 164 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 164=(-51/5:ℚ) from rfl,
    show gridGroupIndex 164=259 from rfl]
  norm_num [value636,sourceRows,sourceRowsPart10] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_636

def value675 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-68)*Y^2*W^2)/(15)))*v 263

theorem source_slope_675 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 168=value675 X Y Z W a b v := by
  have hsel : selectedSource 168=.word 165 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 165=(-1020:ℚ) from rfl,
    show gridGroupIndex 165=135 from rfl]
  norm_num [value675,sourceRows,sourceRowsPart10] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_675

def value1177 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-510))/(X*Y^2)))*v 12

theorem source_slope_1177 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 183=value1177 X Y Z W a b v := by
  have hsel : selectedSource 183=.word 180 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 180=(-85/3:ℚ) from rfl,
    show gridGroupIndex 180=257 from rfl]
  norm_num [value1177,sourceRows,sourceRowsPart11] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_1177

def value1585 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-510))/(W^2)))*v 20

theorem source_slope_1585 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 187=value1585 X Y Z W a b v := by
  have hsel : selectedSource 187=.word 184 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 184=(-102/5:ℚ) from rfl,
    show gridGroupIndex 184=4 from rfl]
  norm_num [value1585,sourceRows,sourceRowsPart11] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_1585

def value2331 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 189=value2331 X Y Z W a b v := by
  have hsel : selectedSource 189=.entire 0 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2331] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2331

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2334 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-255)*X)/(Z*W^2)))*v 255 + ((((-255)*X)/(Z*W^2)))*v 425

theorem source_slope_2334 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 192=value2334 X Y Z W a b v := by
  have hsel : selectedSource 192=.taylor 2 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 2=3 from rfl,show gridTaylorT 2=(2:ℤ) from rfl,
    show gridTaylorL 2=306 from rfl]
  norm_num [value2334,sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2334

def value2338 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X)/(Z)))*v 85 + ((((-51)*X)/(Z)))*v 255

theorem source_slope_2338 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 196=value2338 X Y Z W a b v := by
  have hsel : selectedSource 196=.taylor 6 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 6=3 from rfl,show gridTaylorT 6=(10:ℤ) from rfl,
    show gridTaylorL 6=306 from rfl]
  norm_num [value2338,sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2338

def value2339 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((51*X)/(Z)))*v 255 + (((51*X)/(Z)))*v 425

theorem source_slope_2339 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 197=value2339 X Y Z W a b v := by
  have hsel : selectedSource 197=.taylor 7 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 7=3 from rfl,show gridTaylorT 7=(-10:ℤ) from rfl,
    show gridTaylorL 7=306 from rfl]
  norm_num [value2339,sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2339

def value2340 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-30)*Z)/(X*W^2)))*v 120 + ((((-30)*Z)/(X*W^2)))*v 290

theorem source_slope_2340 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 198=value2340 X Y Z W a b v := by
  have hsel : selectedSource 198=.taylor 8 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 8=3 from rfl,show gridTaylorT 8=(17:ℤ) from rfl,
    show gridTaylorL 8=306 from rfl]
  norm_num [value2340,sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2340

def value2341 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((30*Z)/(X*W^2)))*v 220 + (((30*Z)/(X*W^2)))*v 390

theorem source_slope_2341 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 199=value2341 X Y Z W a b v := by
  have hsel : selectedSource 199=.taylor 9 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 9=3 from rfl,show gridTaylorT 9=(-17:ℤ) from rfl,
    show gridTaylorL 9=306 from rfl]
  norm_num [value2341,sourceRows,sourceRowsPart12,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2341

def value2356 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2356 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 202=value2356 X Y Z W a b v := by
  have hsel : selectedSource 202=.entire 1 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2356] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2356

def value2386 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2386 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 211=value2386 X Y Z W a b v := by
  have hsel : selectedSource 211=.entire 2 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2386] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2386

def value2395 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2395 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 217=value2395 X Y Z W a b v := by
  have hsel : selectedSource 217=.entire 3 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2395] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2395

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2396 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2396 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 218=value2396 X Y Z W a b v := by
  have hsel : selectedSource 218=.entire 4 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2396] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2396

def value2407 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34)/(X)))*v 0 + (((34)/(X)))*v 30 + (((34)/(X)))*v 60 + (((34)/(X)))*v 90 + (((34)/(X)))*v 120 + (((34)/(X)))*v 150 + (((34)/(X)))*v 180 + (((34)/(X)))*v 210 + (((34)/(X)))*v 240 + (((34)/(X)))*v 270 + (((34)/(X)))*v 300 + (((34)/(X)))*v 330 + (((34)/(X)))*v 360 + (((34)/(X)))*v 390 + (((34)/(X)))*v 420 + (((34)/(X)))*v 450

theorem source_slope_2407 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 228=value2407 X Y Z W a b v := by
  have hsel : selectedSource 228=.taylor 34 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  unfold taylorSlope
  rw [show gridTaylorQ 34=17 from rfl,show gridTaylorT 34=(15:ℤ) from rfl,
    show gridTaylorL 34=578 from rfl]
  norm_num [value2407,sourceRows,sourceRowsPart14,gridSample,gridIndex,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2407

def value2425 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2425 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 238=value2425 X Y Z W a b v := by
  have hsel : selectedSource 238=.entire 5 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2425] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2425

def value2441 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2441 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 247=value2441 X Y Z W a b v := by
  have hsel : selectedSource 247=.entire 6 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2441] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2441

def value2459 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2459 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 259=value2459 X Y Z W a b v := by
  have hsel : selectedSource 259=.hecke 0 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2459] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2459

def value2461 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2461 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 260=value2461 X Y Z W a b v := by
  have hsel : selectedSource 260=.hecke 1 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2461] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2461

def value2464 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2464 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 261=value2464 X Y Z W a b v := by
  have hsel : selectedSource 261=.hecke 2 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2464] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2464

def value2465 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2465 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 262=value2465 X Y Z W a b v := by
  have hsel : selectedSource 262=.hecke 3 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2465] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2465

end SmallLevelThirtyFourSlopeLiteralMMP
end

section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2469 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2469 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 265=value2469 X Y Z W a b v := by
  have hsel : selectedSource 265=.hecke 6 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2469] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2469

def value2475 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2475 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 268=value2475 X Y Z W a b v := by
  have hsel : selectedSource 268=.hecke 9 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2475] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2475

def value2480 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2480 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 272=value2480 X Y Z W a b v := by
  have hsel : selectedSource 272=.hecke 13 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2480] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2480

def value2485 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2485 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 276=value2485 X Y Z W a b v := by
  have hsel : selectedSource 276=.hecke 17 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2485] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2485

def value2486 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2486 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 277=value2486 X Y Z W a b v := by
  have hsel : selectedSource 277=.hecke 18 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2486] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2486

def value2498 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2498 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 289=value2498 X Y Z W a b v := by
  have hsel : selectedSource 289=.hecke 30 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2498] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2498

def value2504 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2504 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 295=value2504 X Y Z W a b v := by
  have hsel : selectedSource 295=.hecke 36 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2504] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2504

def value2512 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2512 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 302=value2512 X Y Z W a b v := by
  have hsel : selectedSource 302=.hecke 43 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2512] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2512

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2523 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2523 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 313=value2523 X Y Z W a b v := by
  have hsel : selectedSource 313=.hecke 54 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2523] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2523

def value2525 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2525 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 315=value2525 X Y Z W a b v := by
  have hsel : selectedSource 315=.hecke 56 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2525] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2525

def value2526 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2526 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 316=value2526 X Y Z W a b v := by
  have hsel : selectedSource 316=.hecke 57 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2526] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2526

def value2530 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2530 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 320=value2530 X Y Z W a b v := by
  have hsel : selectedSource 320=.hecke 61 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2530] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2530

def value2546 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2546 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 333=value2546 X Y Z W a b v := by
  have hsel : selectedSource 333=.hecke 74 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2546] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2546

def value2547 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2547 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 334=value2547 X Y Z W a b v := by
  have hsel : selectedSource 334=.hecke 75 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2547] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2547

def value2559 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2559 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 345=value2559 X Y Z W a b v := by
  have hsel : selectedSource 345=.hecke 86 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2559] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2559

def value2568 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2568 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 354=value2568 X Y Z W a b v := by
  have hsel : selectedSource 354=.hecke 95 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2568] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2568

end SmallLevelThirtyFourSlopeLiteralMMP

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2575 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2575 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 360=value2575 X Y Z W a b v := by
  have hsel : selectedSource 360=.hecke 101 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2575] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2575

def value2586 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2586 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 370=value2586 X Y Z W a b v := by
  have hsel : selectedSource 370=.hecke 111 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2586] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2586

def value2588 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2588 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 372=value2588 X Y Z W a b v := by
  have hsel : selectedSource 372=.hecke 113 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2588] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2588

def value2599 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2599 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 382=value2599 X Y Z W a b v := by
  have hsel : selectedSource 382=.hecke 123 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2599] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2599

def value2601 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2601 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 384=value2601 X Y Z W a b v := by
  have hsel : selectedSource 384=.hecke 125 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2601] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2601

def value2619 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2619 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 399=value2619 X Y Z W a b v := by
  have hsel : selectedSource 399=.hecke 140 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2619] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2619

def value2620 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2620 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 400=value2620 X Y Z W a b v := by
  have hsel : selectedSource 400=.hecke 141 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2620] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2620

def value2656 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2656 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 417=value2656 X Y Z W a b v := by
  have hsel : selectedSource 417=.hecke 158 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2656] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2656

end SmallLevelThirtyFourSlopeLiteralMMP
end

section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace SmallLevelThirtyFourSlopeLiteralMMP
open Complex SmallLevelThirtyFourGrid SmallLevelThirtyFourUnitMMP

def value2664 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2664 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 424=value2664 X Y Z W a b v := by
  have hsel : selectedSource 424=.hecke 165 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2664] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2664

def value2672 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2672 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 430=value2672 X Y Z W a b v := by
  have hsel : selectedSource 430=.hecke 171 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2672] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2672

def value2675 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2675 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 433=value2675 X Y Z W a b v := by
  have hsel : selectedSource 433=.hecke 174 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2675] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2675

def value2686 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2686 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 443=value2686 X Y Z W a b v := by
  have hsel : selectedSource 443=.hecke 184 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2686] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2686

def value2692 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2692 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 447=value2692 X Y Z W a b v := by
  have hsel : selectedSource 447=.hecke 188 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2692] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2692

def value2699 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2699 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 453=value2699 X Y Z W a b v := by
  have hsel : selectedSource 453=.hecke 194 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2699] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2699

def value2746 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_2746 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 479=value2746 X Y Z W a b v := by
  have hsel : selectedSource 479=.hecke 220 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value2746] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2746



def value1 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((-204)))*v 425

theorem source_slope_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 1=value1 X Y Z W a b v := by
  have hsel : selectedSource 1=.word 1 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 1=(-204:ℚ) from rfl,
    show gridGroupIndex 1=85 from rfl]
  norm_num [value1,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_1

def value2 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-1020))/(W^2)))*v 435

theorem source_slope_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 2=value2 X Y Z W a b v := by
  have hsel : selectedSource 2=.word 2 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 2=(-204/5:ℚ) from rfl,
    show gridGroupIndex 2=87 from rfl]
  norm_num [value2,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_2

def value3 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((1020)/(W^2)))*v 410

theorem source_slope_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 3=value3 X Y Z W a b v := by
  have hsel : selectedSource 3=.word 3 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 3=(204/5:ℚ) from rfl,
    show gridGroupIndex 3=88 from rfl]
  norm_num [value3,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_3

def value4 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((204))*v 420

theorem source_slope_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 4=value4 X Y Z W a b v := by
  have hsel : selectedSource 4=.word 4 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 4=(204:ℚ) from rfl,
    show gridGroupIndex 4=90 from rfl]
  norm_num [value4,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_4

def value6 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-238)*W^2)/(5*X)))*v 498

theorem source_slope_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 6=value6 X Y Z W a b v := by
  have hsel : selectedSource 6=.word 6 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 6=(-595:ℚ) from rfl,
    show gridGroupIndex 6=75 from rfl]
  norm_num [value6,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_6

def value7 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-714))/(X*Y^2)))*v 0

theorem source_slope_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 7=value7 X Y Z W a b v := by
  have hsel : selectedSource 7=.word 7 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 7=(-119/3:ℚ) from rfl,
    show gridGroupIndex 7=85 from rfl]
  norm_num [value7,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_7

def value8 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((1785*X)/(Y^2*W^2)))*v 465

theorem source_slope_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 8=value8 X Y Z W a b v := by
  have hsel : selectedSource 8=.word 8 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 8=(238/15:ℚ) from rfl,
    show gridGroupIndex 8=86 from rfl]
  norm_num [value8,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_8

def value9 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((1190*Y^2)/(3*X*W^2)))*v 490

theorem source_slope_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 9=value9 X Y Z W a b v := by
  have hsel : selectedSource 9=.word 9 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 9=(357/5:ℚ) from rfl,
    show gridGroupIndex 9=87 from rfl]
  norm_num [value9,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_9



def value10 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((119*X))*v 495

theorem source_slope_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 10=value10 X Y Z W a b v := by
  have hsel : selectedSource 10=.word 10 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 10=(238:ℚ) from rfl,
    show gridGroupIndex 10=90 from rfl]
  norm_num [value10,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_10

def value12 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((1173*X*W^2)/(5*Y^2)))*v 87

theorem source_slope_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 12=value12 X Y Z W a b v := by
  have hsel : selectedSource 12=.word 12 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 12=(3910/3:ℚ) from rfl,
    show gridGroupIndex 12=280 from rfl]
  norm_num [value12,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_12

def value20 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-170)*Y^2)/(3*X)))*v 20

theorem source_slope_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 14=value20 X Y Z W a b v := by
  have hsel : selectedSource 14=.word 14 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 14=(-255:ℚ) from rfl,
    show gridGroupIndex 14=75 from rfl]
  norm_num [value20,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_20

def value21 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((-85)*X))*v 21

theorem source_slope_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 15=value21 X Y Z W a b v := by
  have hsel : selectedSource 15=.word 15 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 15=(-170:ℚ) from rfl,
    show gridGroupIndex 15=78 from rfl]
  norm_num [value21,sourceRows,sourceRowsPart0] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_21

def value22 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-170))/(X)))*v 24

theorem source_slope_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 16=value22 X Y Z W a b v := by
  have hsel : selectedSource 16=.word 16 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 16=(-85:ℚ) from rfl,
    show gridGroupIndex 16=81 from rfl]
  norm_num [value22,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_22

def value24 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-510))/(X*Y^2)))*v 36

theorem source_slope_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 18=value24 X Y Z W a b v := by
  have hsel : selectedSource 18=.word 18 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 18=(-85/3:ℚ) from rfl,
    show gridGroupIndex 18=83 from rfl]
  norm_num [value24,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_24

def value25 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 19=value25 X Y Z W a b v := by
  have hsel : selectedSource 19=.infinity 0 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value25] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_25

def value28 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((170)/(X)))*v 12

theorem source_slope_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 21=value28 X Y Z W a b v := by
  have hsel : selectedSource 21=.word 20 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 20=(85:ℚ) from rfl,
    show gridGroupIndex 20=87 from rfl]
  norm_num [value28,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_28



def value29 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((85*X))*v 15

theorem source_slope_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 22=value29 X Y Z W a b v := by
  have hsel : selectedSource 22=.word 21 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 21=(170:ℚ) from rfl,
    show gridGroupIndex 21=90 from rfl]
  norm_num [value29,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_29

def value30 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((170*Y^2)/(3*X)))*v 16

theorem source_slope_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 23=value30 X Y Z W a b v := by
  have hsel : selectedSource 23=.word 22 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 22=(255:ℚ) from rfl,
    show gridGroupIndex 22=93 from rfl]
  norm_num [value30,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_30

def value31 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((85*X*Y^2)/(3)))*v 17

theorem source_slope_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 24=value31 X Y Z W a b v := by
  have hsel : selectedSource 24=.word 23 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 23=(510:ℚ) from rfl,
    show gridGroupIndex 23=102 from rfl]
  norm_num [value31,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_31

def value32 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((-18)*Z))*v 480

theorem source_slope_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 25=value32 X Y Z W a b v := by
  have hsel : selectedSource 25=.word 24 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 24=(306:ℚ) from rfl,
    show gridGroupIndex 24=0 from rfl]
  norm_num [value32,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_32

def value34 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((32*Z))*v 495

theorem source_slope_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 26=value34 X Y Z W a b v := by
  have hsel : selectedSource 26=.word 25 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 25=(-544:ℚ) from rfl,
    show gridGroupIndex 25=255 from rfl]
  norm_num [value34,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_34

def value35 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((544)/(Z)))*v 0

theorem source_slope_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 27=value35 X Y Z W a b v := by
  have hsel : selectedSource 27=.word 26 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 26=(-32:ℚ) from rfl,
    show gridGroupIndex 26=270 from rfl]
  norm_num [value35,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_35

def value37 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-480)*Z)/(Y^2*W^2)))*v 480

theorem source_slope_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 29=value37 X Y Z W a b v := by
  have hsel : selectedSource 29=.word 28 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 28=(544/15:ℚ) from rfl,
    show gridGroupIndex 28=272 from rfl]
  norm_num [value37,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_37

def value38 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-544)*Y^2*W^2)/(15*Z)))*v 493

theorem source_slope_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 30=value38 X Y Z W a b v := by
  have hsel : selectedSource 30=.word 29 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 29=(480:ℚ) from rfl,
    show gridGroupIndex 29=285 from rfl]
  norm_num [value38,sourceRows,sourceRowsPart1] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_38



def value42 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-1530))/(W^2)))*v 40

theorem source_slope_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 32=value42 X Y Z W a b v := by
  have hsel : selectedSource 32=.word 31 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 31=(-306/5:ℚ) from rfl,
    show gridGroupIndex 31=268 from rfl]
  norm_num [value42,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_42

def value43 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((306))*v 30

theorem source_slope_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 33=value43 X Y Z W a b v := by
  have hsel : selectedSource 33=.word 32 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 32=(306:ℚ) from rfl,
    show gridGroupIndex 32=270 from rfl]
  norm_num [value43,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_43

def value61 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((17*X*W^2)/(5)))*v 87

theorem source_slope_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 37=value61 X Y Z W a b v := by
  have hsel : selectedSource 37=.word 36 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 36=(170:ℚ) from rfl,
    show gridGroupIndex 36=60 from rfl]
  norm_num [value61,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_61

def value62 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34*Y^2*W^2)/(15*X)))*v 88

theorem source_slope_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 38=value62 X Y Z W a b v := by
  have hsel : selectedSource 38=.word 37 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 37=(255:ℚ) from rfl,
    show gridGroupIndex 37=135 from rfl]
  norm_num [value62,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_62

def value63 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((17*X*Y^2*W^2)/(15)))*v 89

theorem source_slope_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 39=value63 X Y Z W a b v := by
  have hsel : selectedSource 39=.word 38 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 38=(510:ℚ) from rfl,
    show gridGroupIndex 38=360 from rfl]
  norm_num [value63,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_63

def value64 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((986*W^2)/(5)))*v 18

theorem source_slope_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 40=value64 X Y Z W a b v := by
  have hsel : selectedSource 40=.word 39 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 39=(4930:ℚ) from rfl,
    show gridGroupIndex 39=90 from rfl]
  norm_num [value64,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_64

def value66 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-102)*W^2)/(5*X)))*v 262

theorem source_slope_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 42=value66 X Y Z W a b v := by
  have hsel : selectedSource 42=.word 41 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 41=(-255:ℚ) from rfl,
    show gridGroupIndex 41=475 from rfl]
  norm_num [value66,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_66

def value67 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((-51)*X))*v 265

theorem source_slope_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 43=value67 X Y Z W a b v := by
  have hsel : selectedSource 43=.word 42 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 42=(-102:ℚ) from rfl,
    show gridGroupIndex 42=490 from rfl]
  norm_num [value67,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_67



def value68 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-102))/(X)))*v 270

theorem source_slope_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 44=value68 X Y Z W a b v := by
  have hsel : selectedSource 44=.word 43 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 43=(-51:ℚ) from rfl,
    show gridGroupIndex 43=495 from rfl]
  norm_num [value68,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_68

def value69 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-255)*X)/(W^2)))*v 285

theorem source_slope_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 45=value69 X Y Z W a b v := by
  have hsel : selectedSource 45=.word 44 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 44=(-102/5:ℚ) from rfl,
    show gridGroupIndex 44=498 from rfl]
  norm_num [value69,sourceRows,sourceRowsPart2] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_69

def value71 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  0

theorem source_slope_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 47=value71 X Y Z W a b v := by
  have hsel : selectedSource 47=.infinity 1 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  norm_num [value71] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_71

def value73 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((255*X)/(W^2)))*v 235

theorem source_slope_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 49=value73 X Y Z W a b v := by
  have hsel : selectedSource 49=.word 47 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 47=(102/5:ℚ) from rfl,
    show gridGroupIndex 47=502 from rfl]
  norm_num [value73,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_73

def value77 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-34)*W^2)/(5*X)))*v 426

theorem source_slope_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 51=value77 X Y Z W a b v := by
  have hsel : selectedSource 51=.word 49 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 49=(-85:ℚ) from rfl,
    show gridGroupIndex 49=15 from rfl]
  norm_num [value77,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_77

def value78 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X*W^2)/(5*Y^2)))*v 429

theorem source_slope_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 52=value78 X Y Z W a b v := by
  have hsel : selectedSource 52=.word 50 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 50=(-170/3:ℚ) from rfl,
    show gridGroupIndex 50=40 from rfl]
  norm_num [value78,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_78

def value79 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-34)*Y^2)/(3*X)))*v 430

theorem source_slope_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 53=value79 X Y Z W a b v := by
  have hsel : selectedSource 53=.word 51 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 51=(-51:ℚ) from rfl,
    show gridGroupIndex 51=45 from rfl]
  norm_num [value79,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_79

def value81 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-102)*W^2)/(5*X*Y^2)))*v 438

theorem source_slope_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 54=value81 X Y Z W a b v := by
  have hsel : selectedSource 54=.word 52 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 52=(-85/3:ℚ) from rfl,
    show gridGroupIndex 52=65 from rfl]
  norm_num [value81,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_81



def value82 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-85)*X*Y^2)/(3*W^2)))*v 445

theorem source_slope_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 55=value82 X Y Z W a b v := by
  have hsel : selectedSource 55=.word 53 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 53=(-102/5:ℚ) from rfl,
    show gridGroupIndex 53=72 from rfl]
  norm_num [value82,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_82

def value83 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-34))/(X)))*v 450

theorem source_slope_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 56=value83 X Y Z W a b v := by
  have hsel : selectedSource 56=.word 54 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 54=(-17:ℚ) from rfl,
    show gridGroupIndex 54=75 from rfl]
  norm_num [value83,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_83

def value84 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-51)*X)/(Y^2)))*v 465

theorem source_slope_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 57=value84 X Y Z W a b v := by
  have hsel : selectedSource 57=.word 55 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 55=(-34/3:ℚ) from rfl,
    show gridGroupIndex 55=80 from rfl]
  norm_num [value84,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_84

def value85 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-170)*Y^2)/(3*X*W^2)))*v 470

theorem source_slope_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 58=value85 X Y Z W a b v := by
  have hsel : selectedSource 58=.word 56 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 56=(-51/5:ℚ) from rfl,
    show gridGroupIndex 56=81 from rfl]
  norm_num [value85,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_85

def value86 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-85)*X)/(W^2)))*v 495

theorem source_slope_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 59=value86 X Y Z W a b v := by
  have hsel : selectedSource 59=.word 57 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 57=(-34/5:ℚ) from rfl,
    show gridGroupIndex 57=84 from rfl]
  norm_num [value86,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_86

def value94 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((170)/(X*W^2)))*v 270

theorem source_slope_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 62=value94 X Y Z W a b v := by
  have hsel : selectedSource 62=.word 60 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 60=(17/5:ℚ) from rfl,
    show gridGroupIndex 60=93 from rfl]
  norm_num [value94,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_94

def value95 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((102)/(X*Y^2)))*v 330

theorem source_slope_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 63=value95 X Y Z W a b v := by
  have hsel : selectedSource 63=.word 61 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 61=(17/3:ℚ) from rfl,
    show gridGroupIndex 61=95 from rfl]
  norm_num [value95,sourceRows,sourceRowsPart3] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_95

def value98 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((51*X)/(Y^2)))*v 375

theorem source_slope_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 66=value98 X Y Z W a b v := by
  have hsel : selectedSource 66=.word 64 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 64=(34/3:ℚ) from rfl,
    show gridGroupIndex 64=100 from rfl]
  norm_num [value98,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_98



def value99 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34)/(X)))*v 390

theorem source_slope_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 67=value99 X Y Z W a b v := by
  have hsel : selectedSource 67=.word 65 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 65=(17:ℚ) from rfl,
    show gridGroupIndex 65=105 from rfl]
  norm_num [value99,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_99

def value102 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((17*X))*v 405

theorem source_slope_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 70=value102 X Y Z W a b v := by
  have hsel : selectedSource 70=.word 68 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 68=(34:ℚ) from rfl,
    show gridGroupIndex 68=120 from rfl]
  norm_num [value102,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_102

def value105 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34*W^2)/(5*X)))*v 414

theorem source_slope_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 72=value105 X Y Z W a b v := by
  have hsel : selectedSource 72=.word 70 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 70=(85:ℚ) from rfl,
    show gridGroupIndex 70=165 from rfl]
  norm_num [value105,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_105

def value106 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((17*X*Y^2)/(3)))*v 415

theorem source_slope_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 73=value106 X Y Z W a b v := by
  have hsel : selectedSource 73=.word 71 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 71=(102:ℚ) from rfl,
    show gridGroupIndex 71=180 from rfl]
  norm_num [value106,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_106

def value107 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((17*X*W^2)/(5)))*v 417

theorem source_slope_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 74=value107 X Y Z W a b v := by
  have hsel : selectedSource 74=.word 72 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 72=(170:ℚ) from rfl,
    show gridGroupIndex 72=240 from rfl]
  norm_num [value107,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_107

def value108 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34*Y^2*W^2)/(15*X)))*v 418

theorem source_slope_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 75=value108 X Y Z W a b v := by
  have hsel : selectedSource 75=.word 73 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 73=(255:ℚ) from rfl,
    show gridGroupIndex 73=315 from rfl]
  norm_num [value108,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_108

def value142 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-136)*Y^2*W^2)/(15)))*v 424

theorem source_slope_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 78=value142 X Y Z W a b v := by
  have hsel : selectedSource 78=.word 76 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 76=(-2040:ℚ) from rfl,
    show gridGroupIndex 76=210 from rfl]
  norm_num [value142,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_142

def value144 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-408)*W^2)/(5*Y^2)))*v 426

theorem source_slope_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 79=value144 X Y Z W a b v := by
  have hsel : selectedSource 79=.word 77 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 77=(-680/3:ℚ) from rfl,
    show gridGroupIndex 77=260 from rfl]
  norm_num [value144,sourceRows,sourceRowsPart4] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_144



def value148 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((680)/(W^2)))*v 405

theorem source_slope_148 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 82=value148 X Y Z W a b v := by
  have hsel : selectedSource 82=.word 80 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 80=(136/5:ℚ) from rfl,
    show gridGroupIndex 80=267 from rfl]
  norm_num [value148,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_148

def value152 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-408)*W^2)/(5)))*v 89

theorem source_slope_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 83=value152 X Y Z W a b v := by
  have hsel : selectedSource 83=.word 81 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 81=(-2040:ℚ) from rfl,
    show gridGroupIndex 81=475 from rfl]
  norm_num [value152,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_152

def value157 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-115)*X*Y^2*Z)/(3*W^2)))*v 265

theorem source_slope_157 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 85=value157 X Y Z W a b v := by
  have hsel : selectedSource 85=.word 83 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 83=(2346/5:ℚ) from rfl,
    show gridGroupIndex 83=102 from rfl]
  norm_num [value157,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_157

def value170 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((6*Z*W^2)/(5)))*v 86

theorem source_slope_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 90=value170 X Y Z W a b v := by
  have hsel : selectedSource 90=.word 87 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 87=(-510:ℚ) from rfl,
    show gridGroupIndex 87=170 from rfl]
  norm_num [value170,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_170

def value172 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((6*Z))*v 430

theorem source_slope_172 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 91=value172 X Y Z W a b v := by
  have hsel : selectedSource 91=.word 88 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 88=(-102:ℚ) from rfl,
    show gridGroupIndex 88=340 from rfl]
  norm_num [value172,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_172

def value173 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((102*W^2)/(5*Z)))*v 442

theorem source_slope_173 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 92=value173 X Y Z W a b v := by
  have hsel : selectedSource 92=.word 89 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 89=(-30:ℚ) from rfl,
    show gridGroupIndex 89=400 from rfl]
  norm_num [value173,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_173

def value174 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((30*Z)/(W^2)))*v 450

theorem source_slope_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 93=value174 X Y Z W a b v := by
  have hsel : selectedSource 93=.word 90 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 90=(-102/5:ℚ) from rfl,
    show gridGroupIndex 90=408 from rfl]
  norm_num [value174,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_174

def value176 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((510)/(Z*W^2)))*v 340

theorem source_slope_176 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 94=value176 X Y Z W a b v := by
  have hsel : selectedSource 94=.word 91 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 91=(-6/5:ℚ) from rfl,
    show gridGroupIndex 91=424 from rfl]
  norm_num [value176,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_176



def value183 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-170)*Y^2)/(3*X)))*v 494

theorem source_slope_183 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 95=value183 X Y Z W a b v := by
  have hsel : selectedSource 95=.word 92 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 92=(-255:ℚ) from rfl,
    show gridGroupIndex 92=417 from rfl]
  norm_num [value183,sourceRows,sourceRowsPart5] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_183

def value189 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((510)/(X*Y^2)))*v 474

theorem source_slope_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 96=value189 X Y Z W a b v := by
  have hsel : selectedSource 96=.word 93 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 93=(85/3:ℚ) from rfl,
    show gridGroupIndex 93=427 from rfl]
  norm_num [value189,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_189

def value199 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-4335)*X)/(Y^2*W^2)))*v 495

theorem source_slope_199 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 101=value199 X Y Z W a b v := by
  have hsel : selectedSource 101=.word 98 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 98=(-578/15:ℚ) from rfl,
    show gridGroupIndex 98=494 from rfl]
  norm_num [value199,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_199

def value201 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  ((((-850)*Y^2)/(3*X)))*v 418

theorem source_slope_201 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 102=value201 X Y Z W a b v := by
  have hsel : selectedSource 102=.word 99 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 99=(-1275:ℚ) from rfl,
    show gridGroupIndex 99=81 from rfl]
  norm_num [value201,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_201

def value202 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((2550)/(X*Y^2)))*v 414

theorem source_slope_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 103=value202 X Y Z W a b v := by
  have hsel : selectedSource 103=.word 100 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 100=(425/3:ℚ) from rfl,
    show gridGroupIndex 100=83 from rfl]
  norm_num [value202,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_202

def value225 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((90*Z)/(W^2)))*v 490

theorem source_slope_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 106=value225 X Y Z W a b v := by
  have hsel : selectedSource 106=.word 103 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 103=(-306/5:ℚ) from rfl,
    show gridGroupIndex 103=476 from rfl]
  norm_num [value225,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_225

def value246 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((2040)/(Y^2*Z)))*v 51

theorem source_slope_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 108=value246 X Y Z W a b v := by
  have hsel : selectedSource 108=.word 105 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 105=(-40/3:ℚ) from rfl,
    show gridGroupIndex 105=89 from rfl]
  norm_num [value246,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_246

def value260 (X Y Z W a b : ℂ) (v : Fin 510→ℂ) : ℂ :=
  (((34*Y^2*W^2)/(15*X)))*v 268

theorem source_slope_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) : sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 109=value260 X Y Z W a b v := by
  have hsel : selectedSource 109=.word 106 := rfl
  simp only [sourceSlopeRows,slopeFromLeading,hsel]
  rw [show gridGroupDerivative 106=(255:ℚ) from rfl,
    show gridGroupIndex 106=195 from rfl]
  norm_num [value260,sourceRows,sourceRowsPart6] <;> field_simp [hX,hY,hZ,hW] <;> ring

#print axioms source_slope_260

end SmallLevelThirtyFourSlopeLiteralMMP
end
