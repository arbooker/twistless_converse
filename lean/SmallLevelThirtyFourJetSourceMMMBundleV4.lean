module
public import SmallLevelThirtyFourJetOperatorMMMTheoryV4
public import SmallLevelThirtyFourSlopeLiteralMMMBundleV4
public import SmallLevelThirtyFourUnitMMMTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourJetSourceMMM
open Complex SmallLevelThirtyFourUnitMMM SmallLevelThirtyFourJetOperatorMMM SmallLevelThirtyFourSlopeLiteralMMM

theorem source_value_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 1=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 1 := by
  rw [source_slope_1 X Y Z W a b hX hY hZ hW v]
  change value1 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value1
  rw [coordinate_expansion_425 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 2=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 2 := by
  rw [source_slope_2 X Y Z W a b hX hY hZ hW v]
  change value2 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-1020))/(W^2)))*v 435
  unfold value2
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 3=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 3 := by
  rw [source_slope_3 X Y Z W a b hX hY hZ hW v]
  change value3 X Y Z W a b v=(0)*v 370 + ((((-1020)*X)/(Y^2*W^2)))*v 390 + (0)*v 435
  unfold value3
  rw [coordinate_expansion_410 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 4=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 4 := by
  rw [source_slope_4 X Y Z W a b hX hY hZ hW v]
  change value4 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value4
  rw [coordinate_expansion_420 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 6=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 6 := by
  rw [source_slope_6 X Y Z W a b hX hY hZ hW v]
  change value6 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((238)/(5)))*v 435
  unfold value6
  rw [coordinate_expansion_498 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 7=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 7 := by
  rw [source_slope_7 X Y Z W a b hX hY hZ hW v]
  change value7 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value7
  rw [coordinate_expansion_0 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 8=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 8 := by
  rw [source_slope_8 X Y Z W a b hX hY hZ hW v]
  change value8 X Y Z W a b v=(0)*v 370 + (((1785)/(Y^2*W^2)))*v 390 + ((((-1785)*X^2)/(Y^2*W^2)) + (((-1785)*X^3)/(2*Y^2*W^2)) + (((-1785)*X^3*a)/(2*Y*W^2)) + (((-1785)*X^3)/(2*W^2)))*v 435
  unfold value8
  rw [coordinate_expansion_465 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 9=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 9 := by
  rw [source_slope_9 X Y Z W a b hX hY hZ hW v]
  change value9 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((1190)/(3*W^2)))*v 435
  unfold value9
  rw [coordinate_expansion_490 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_9

theorem source_value_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 10=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 10 := by
  rw [source_slope_10 X Y Z W a b hX hY hZ hW v]
  change value10 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value10
  rw [coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 12=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 12 := by
  rw [source_slope_12 X Y Z W a b hX hY hZ hW v]
  change value12 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((1173*X)/(5*Y^2)))*v 435
  unfold value12
  rw [coordinate_expansion_87 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 14=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 14 := by
  rw [source_slope_20 X Y Z W a b hX hY hZ hW v]
  change value20 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((170)/(3)))*v 435
  unfold value20
  rw [coordinate_expansion_20 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 15=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 15 := by
  rw [source_slope_21 X Y Z W a b hX hY hZ hW v]
  change value21 X Y Z W a b v=(0)*v 370 + ((((-85)*Y^2)/(W^2)))*v 390 + (((85*X)/(2*W^2)) + ((85*X*Y*a)/(2*W^2)) + (((-85)*X*Y^2)/(2*W^2)) + ((85*X^2)/(W^2)) + ((85*X^2*Y*a)/(2*W^2)) + ((85*X^2*Y^2*a^2)/(2*W^2)) + ((85*X^2*Y^3*a)/(2*W^2)))*v 435
  unfold value21
  rw [coordinate_expansion_21 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 16=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 16 := by
  rw [source_slope_22 X Y Z W a b hX hY hZ hW v]
  change value22 X Y Z W a b v=(0)*v 370 + ((((-170))/(X*W^2)))*v 390 + (((170*X)/(W^2)))*v 435
  unfold value22
  rw [coordinate_expansion_24 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 18=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 18 := by
  rw [source_slope_24 X Y Z W a b hX hY hZ hW v]
  change value24 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 435
  unfold value24
  rw [coordinate_expansion_36 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 19=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 19 := by
  rw [source_slope_25 X Y Z W a b hX hY hZ hW v]
  change value25 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value25
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 21=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 21 := by
  rw [source_slope_28 X Y Z W a b hX hY hZ hW v]
  change value28 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((170)/(W^2)))*v 435
  unfold value28
  rw [coordinate_expansion_12 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_28

theorem source_value_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 22=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 22 := by
  rw [source_slope_29 X Y Z W a b hX hY hZ hW v]
  change value29 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value29
  rw [coordinate_expansion_15 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 23=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 23 := by
  rw [source_slope_30 X Y Z W a b hX hY hZ hW v]
  change value30 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value30
  rw [coordinate_expansion_16 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 24=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 24 := by
  rw [source_slope_31 X Y Z W a b hX hY hZ hW v]
  change value31 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-85)*X*Z)/(3*W^2)))*v 435
  unfold value31
  rw [coordinate_expansion_17 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 25=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 25 := by
  rw [source_slope_32 X Y Z W a b hX hY hZ hW v]
  change value32 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value32
  rw [coordinate_expansion_480 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 26=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 26 := by
  rw [source_slope_34 X Y Z W a b hX hY hZ hW v]
  change value34 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value34
  rw [coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 27=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 27 := by
  rw [source_slope_35 X Y Z W a b hX hY hZ hW v]
  change value35 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value35
  rw [coordinate_expansion_0 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 29=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 29 := by
  rw [source_slope_37 X Y Z W a b hX hY hZ hW v]
  change value37 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value37
  rw [coordinate_expansion_480 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 30=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 30 := by
  rw [source_slope_38 X Y Z W a b hX hY hZ hW v]
  change value38 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-544))/(15)))*v 435
  unfold value38
  rw [coordinate_expansion_493 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_38

theorem source_value_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 32=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 32 := by
  rw [source_slope_42 X Y Z W a b hX hY hZ hW v]
  change value42 X Y Z W a b v=(0)*v 370 + (((1530)/(Y^2*W^2)))*v 390 + ((((-1530)*X^2)/(Y^2*W^2)))*v 435
  unfold value42
  rw [coordinate_expansion_40 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 33=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 33 := by
  rw [source_slope_43 X Y Z W a b hX hY hZ hW v]
  change value43 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value43
  rw [coordinate_expansion_30 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 37=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 37 := by
  rw [source_slope_61 X Y Z W a b hX hY hZ hW v]
  change value61 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((17*X)/(5)))*v 435
  unfold value61
  rw [coordinate_expansion_87 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 38=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 38 := by
  rw [source_slope_62 X Y Z W a b hX hY hZ hW v]
  change value62 X Y Z W a b v=(0)*v 370 + ((((-34))/(15)))*v 390 + (0)*v 435
  unfold value62
  rw [coordinate_expansion_88 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 39=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 39 := by
  rw [source_slope_63 X Y Z W a b hX hY hZ hW v]
  change value63 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-17)*X)/(15)) + (((-17)*X^2)/(30)) + (((-17)*X^2*Y*a)/(30)) + (((-17)*X^2*Y^2)/(30)))*v 435
  unfold value63
  rw [coordinate_expansion_89 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 40=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 40 := by
  rw [source_slope_64 X Y Z W a b hX hY hZ hW v]
  change value64 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value64
  rw [coordinate_expansion_18 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 42=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 42 := by
  rw [source_slope_66 X Y Z W a b hX hY hZ hW v]
  change value66 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((102)/(5*Y^2)) + ((51*X)/(5*Y^2)) + ((51*X*a)/(5*Y)) + ((51*X)/(5)))*v 435
  unfold value66
  rw [coordinate_expansion_262 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 43=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 43 := by
  rw [source_slope_67 X Y Z W a b hX hY hZ hW v]
  change value67 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-51)*X)/(Y^2)))*v 435
  unfold value67
  rw [coordinate_expansion_265 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_67

theorem source_value_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 44=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 44 := by
  rw [source_slope_68 X Y Z W a b hX hY hZ hW v]
  change value68 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value68
  rw [coordinate_expansion_270 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 45=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 45 := by
  rw [source_slope_69 X Y Z W a b hX hY hZ hW v]
  change value69 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((255*X)/(W^2)))*v 435
  unfold value69
  rw [coordinate_expansion_285 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 47=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 47 := by
  rw [source_slope_71 X Y Z W a b hX hY hZ hW v]
  change value71 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value71
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 49=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 49 := by
  rw [source_slope_73 X Y Z W a b hX hY hZ hW v]
  change value73 X Y Z W a b v=(0)*v 370 + ((((-255))/(Y^2*W^2)))*v 390 + (0)*v 435
  unfold value73
  rw [coordinate_expansion_235 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 51=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 51 := by
  rw [source_slope_77 X Y Z W a b hX hY hZ hW v]
  change value77 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value77
  rw [coordinate_expansion_426 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 52=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 52 := by
  rw [source_slope_78 X Y Z W a b hX hY hZ hW v]
  change value78 X Y Z W a b v=(0)*v 370 + (((51)/(5*Y^2)))*v 390 + ((((-51)*X^2)/(5*Y^2)))*v 435
  unfold value78
  rw [coordinate_expansion_429 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 53=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 53 := by
  rw [source_slope_79 X Y Z W a b hX hY hZ hW v]
  change value79 X Y Z W a b v=(0)*v 370 + (((34)/(3*X)))*v 390 + ((((-34)*X)/(3)) + (((-17)*X^2)/(3)) + (((-17)*X^2*Y*a)/(3)) + (((-17)*X^2*Y^2)/(3)))*v 435
  unfold value79
  rw [coordinate_expansion_430 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 54=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 54 := by
  rw [source_slope_81 X Y Z W a b hX hY hZ hW v]
  change value81 X Y Z W a b v=(0)*v 370 + ((((-102))/(5*X*Y^2)) + ((102*a)/(5*X*Y)) + (((-102))/(5*X)))*v 390 + ((((-102))/(5*Y^2)) + (((-102)*X*a)/(5*Y)))*v 435
  unfold value81
  rw [coordinate_expansion_438 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_81

theorem source_value_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 55=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 55 := by
  rw [source_slope_82 X Y Z W a b hX hY hZ hW v]
  change value82 X Y Z W a b v=(0)*v 370 + (((85)/(3*W^2)) + (((-85)*Y*a)/(3*W^2)) + ((85*Y^2)/(3*W^2)))*v 390 + (((85*X)/(3*W^2)) + ((85*X^2*Y*a)/(3*W^2)))*v 435
  unfold value82
  rw [coordinate_expansion_445 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 56=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 56 := by
  rw [source_slope_83 X Y Z W a b hX hY hZ hW v]
  change value83 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((34))*v 435
  unfold value83
  rw [coordinate_expansion_450 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 57=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 57 := by
  rw [source_slope_84 X Y Z W a b hX hY hZ hW v]
  change value84 X Y Z W a b v=(0)*v 370 + ((((-51))/(Y^2)))*v 390 + (((51*X^2)/(Y^2)) + ((51*X^3)/(2*Y^2)) + ((51*X^3*a)/(2*Y)) + ((51*X^3)/(2)))*v 435
  unfold value84
  rw [coordinate_expansion_465 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 58=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 58 := by
  rw [source_slope_85 X Y Z W a b hX hY hZ hW v]
  change value85 X Y Z W a b v=(0)*v 370 + ((((-170))/(3*X*W^2)))*v 390 + (((170*X)/(3*W^2)))*v 435
  unfold value85
  rw [coordinate_expansion_470 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 59=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 59 := by
  rw [source_slope_86 X Y Z W a b hX hY hZ hW v]
  change value86 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value86
  rw [coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 62=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 62 := by
  rw [source_slope_94 X Y Z W a b hX hY hZ hW v]
  change value94 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value94
  rw [coordinate_expansion_270 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 63=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 63 := by
  rw [source_slope_95 X Y Z W a b hX hY hZ hW v]
  change value95 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-51))/(Y^2)) + (((-51)*a)/(Y)) + ((-51)))*v 435
  unfold value95
  rw [coordinate_expansion_330 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 66=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 66 := by
  rw [source_slope_98 X Y Z W a b hX hY hZ hW v]
  change value98 X Y Z W a b v=(0)*v 370 + (((51*X)/(Y^2)))*v 390 + (0)*v 435
  unfold value98
  rw [coordinate_expansion_375 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_98

theorem source_value_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 67=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 67 := by
  rw [source_slope_99 X Y Z W a b hX hY hZ hW v]
  change value99 X Y Z W a b v=(0)*v 370 + (((34)/(X)))*v 390 + (0)*v 435
  unfold value99
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 70=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 70 := by
  rw [source_slope_102 X Y Z W a b hX hY hZ hW v]
  change value102 X Y Z W a b v=(0)*v 370 + (((-17)))*v 390 + (0)*v 435
  unfold value102
  rw [coordinate_expansion_405 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 72=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 72 := by
  rw [source_slope_105 X Y Z W a b hX hY hZ hW v]
  change value105 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((17)/(5)) + ((17*Y*a)/(5)) + ((17*Y^2)/(5)))*v 435
  unfold value105
  rw [coordinate_expansion_414 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 73=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 73 := by
  rw [source_slope_106 X Y Z W a b hX hY hZ hW v]
  change value106 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((17*X)/(6)) + ((17*X*Y*a)/(6)) + ((17*X*Y^2)/(6)))*v 435
  unfold value106
  rw [coordinate_expansion_415 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 74=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 74 := by
  rw [source_slope_107 X Y Z W a b hX hY hZ hW v]
  change value107 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value107
  rw [coordinate_expansion_417 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 75=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 75 := by
  rw [source_slope_108 X Y Z W a b hX hY hZ hW v]
  change value108 X Y Z W a b v=(0)*v 370 + (((34)/(15*X)))*v 390 + ((((-34)*X)/(15)))*v 435
  unfold value108
  rw [coordinate_expansion_418 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 78=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 78 := by
  rw [source_slope_142 X Y Z W a b hX hY hZ hW v]
  change value142 X Y Z W a b v=(0)*v 370 + (((136)/(15)))*v 390 + ((((-136)*X^2)/(15)) + (((-68)*X^3)/(15)) + (((-68)*X^3*Y*a)/(15)) + (((-68)*X^3*Y^2)/(15)))*v 435
  unfold value142
  rw [coordinate_expansion_424 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 79=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 79 := by
  rw [source_slope_144 X Y Z W a b hX hY hZ hW v]
  change value144 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value144
  rw [coordinate_expansion_426 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_144

theorem source_value_148 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 82=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 82 := by
  rw [source_slope_148 X Y Z W a b hX hY hZ hW v]
  change value148 X Y Z W a b v=(0)*v 370 + ((((-680))/(X*W^2)))*v 390 + (0)*v 435
  unfold value148
  rw [coordinate_expansion_405 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 83=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 83 := by
  rw [source_slope_152 X Y Z W a b hX hY hZ hW v]
  change value152 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((408)/(5*Y^2)) + ((204*X)/(5*Y^2)) + ((204*X*a)/(5*Y)) + ((204*X)/(5)))*v 435
  unfold value152
  rw [coordinate_expansion_89 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_157 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 85=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 85 := by
  rw [source_slope_157 X Y Z W a b hX hY hZ hW v]
  change value157 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-115)*X*Z)/(3*W^2)))*v 435
  unfold value157
  rw [coordinate_expansion_265 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 90=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 90 := by
  rw [source_slope_170 X Y Z W a b hX hY hZ hW v]
  change value170 X Y Z W a b v=(0)*v 370 + (((6*Z)/(5*Y^2)))*v 390 + ((((-6)*X^2*Z)/(5*Y^2)) + (((-3)*X^3*Z)/(5*Y^2)) + (((-3)*X^3*Z*a)/(5*Y)) + (((-3)*X^3*Z)/(5)))*v 435
  unfold value170
  rw [coordinate_expansion_86 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_172 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 91=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 91 := by
  rw [source_slope_172 X Y Z W a b hX hY hZ hW v]
  change value172 X Y Z W a b v=(0)*v 370 + ((((-6)*Z)/(Y^2)))*v 390 + (((6*X^2*Z)/(Y^2)) + ((3*X^3*Z)/(Y^2)) + ((3*X^3*Z*a)/(Y)) + (3*X^3*Z))*v 435
  unfold value172
  rw [coordinate_expansion_430 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_173 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 92=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 92 := by
  rw [source_slope_173 X Y Z W a b hX hY hZ hW v]
  change value173 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-102)*X)/(5*Y^2)) + (((-51)*X*a)/(5*Y)) + ((102*X)/(5)) + (((-51)*X*a^2)/(5)) + (((-51)*X*Y*a)/(5)))*v 435
  unfold value173
  rw [coordinate_expansion_442 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 93=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 93 := by
  rw [source_slope_174 X Y Z W a b hX hY hZ hW v]
  change value174 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-30)*X*Z)/(W^2)))*v 435
  unfold value174
  rw [coordinate_expansion_450 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_176 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 94=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 94 := by
  rw [source_slope_176 X Y Z W a b hX hY hZ hW v]
  change value176 X Y Z W a b v=(0)*v 370 + (((510)/(Y^2*W^2)))*v 390 + ((((-510)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(Y^2*W^2)) + (((-255)*X^3*a)/(Y*W^2)) + (((-255)*X^3)/(W^2)))*v 435
  unfold value176
  rw [coordinate_expansion_340 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_176

theorem source_value_183 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 95=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 95 := by
  rw [source_slope_183 X Y Z W a b hX hY hZ hW v]
  change value183 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value183
  rw [coordinate_expansion_494 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 96=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 96 := by
  rw [source_slope_189 X Y Z W a b hX hY hZ hW v]
  change value189 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-255))/(Y^2*W^2)) + (((-255)*a)/(Y*W^2)) + (((-255))/(W^2)))*v 435
  unfold value189
  rw [coordinate_expansion_474 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_199 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 101=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 101 := by
  rw [source_slope_199 X Y Z W a b hX hY hZ hW v]
  change value199 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value199
  rw [coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_201 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 102=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 102 := by
  rw [source_slope_201 X Y Z W a b hX hY hZ hW v]
  change value201 X Y Z W a b v=(0)*v 370 + ((((-850))/(3*X*W^2)))*v 390 + (((850*X)/(3*W^2)))*v 435
  unfold value201
  rw [coordinate_expansion_418 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 103=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 103 := by
  rw [source_slope_202 X Y Z W a b hX hY hZ hW v]
  change value202 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((1275)/(Y^2*W^2)) + ((1275*a)/(Y*W^2)) + ((1275)/(W^2)))*v 435
  unfold value202
  rw [coordinate_expansion_414 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 106=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 106 := by
  rw [source_slope_225 X Y Z W a b hX hY hZ hW v]
  change value225 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((90*X*Z)/(Y^2*W^2)))*v 435
  unfold value225
  rw [coordinate_expansion_490 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 108=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 108 := by
  rw [source_slope_246 X Y Z W a b hX hY hZ hW v]
  change value246 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((2040)/(Y^2*W^2)) + ((1020*X)/(Y^2*W^2)) + ((1020*X*a)/(Y*W^2)) + ((1020*X)/(W^2)))*v 435
  unfold value246
  rw [coordinate_expansion_51 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 109=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 109 := by
  rw [source_slope_260 X Y Z W a b hX hY hZ hW v]
  change value260 X Y Z W a b v=(0)*v 370 + ((((-34))/(15*X)))*v 390 + (((34*X)/(15)))*v 435
  unfold value260
  rw [coordinate_expansion_268 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_260

theorem source_value_263 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 110=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 110 := by
  rw [source_slope_263 X Y Z W a b hX hY hZ hW v]
  change value263 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value263
  rw [coordinate_expansion_10 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_266 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 112=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 112 := by
  rw [source_slope_266 X Y Z W a b hX hY hZ hW v]
  change value266 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value266
  rw [coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_275 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 116=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 116 := by
  rw [source_slope_275 X Y Z W a b hX hY hZ hW v]
  change value275 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-51))/(5*Y^2)) + (((-51)*a)/(5*Y)) + (((-51))/(5)))*v 435
  unfold value275
  rw [coordinate_expansion_204 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 117=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 117 := by
  rw [source_slope_277 X Y Z W a b hX hY hZ hW v]
  change value277 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((15*X*Z)/(Y^2*W^2)))*v 435
  unfold value277
  rw [coordinate_expansion_285 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_279 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 118=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 118 := by
  rw [source_slope_279 X Y Z W a b hX hY hZ hW v]
  change value279 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((51*X)/(10*Y^2)) + ((51*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)))*v 435
  unfold value279
  rw [coordinate_expansion_357 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 119=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 119 := by
  rw [source_slope_285 X Y Z W a b hX hY hZ hW v]
  change value285 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((17*X)/(5)) + ((17*X^2)/(10)) + ((17*X^2*Y*a)/(10)) + ((17*X^2*Y^2)/(10)))*v 435
  unfold value285
  rw [coordinate_expansion_459 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 120=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 120 := by
  rw [source_slope_286 X Y Z W a b hX hY hZ hW v]
  change value286 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((5*Z)/(3*W^2)) + ((5*Y*Z*a)/(3*W^2)) + ((5*Y^2*Z)/(3*W^2)) + (((-10)*X*Z)/(3*W^2)))*v 435
  unfold value286
  rw [coordinate_expansion_460 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 121=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 121 := by
  rw [source_slope_288 X Y Z W a b hX hY hZ hW v]
  change value288 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((34)/(15)))*v 435
  unfold value288
  rw [coordinate_expansion_476 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_288

theorem source_value_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 122=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 122 := by
  rw [source_slope_290 X Y Z W a b hX hY hZ hW v]
  change value290 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-5)*X*Z)/(6*W^2)) + (((-5)*X*Y*Z*a)/(6*W^2)) + (((-5)*X*Y^2*Z)/(6*W^2)))*v 435
  unfold value290
  rw [coordinate_expansion_485 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_296 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 124=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 124 := by
  rw [source_slope_296 X Y Z W a b hX hY hZ hW v]
  change value296 X Y Z W a b v=(0)*v 370 + ((((-1020))/(X*Y^2*W^2)))*v 390 + (0)*v 435
  unfold value296
  rw [coordinate_expansion_105 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_297 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 125=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 125 := by
  rw [source_slope_297 X Y Z W a b hX hY hZ hW v]
  change value297 X Y Z W a b v=(0)*v 370 + (((1020)/(Y^2*W^2)))*v 390 + (0)*v 435
  unfold value297
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_305 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 126=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 126 := by
  rw [source_slope_305 X Y Z W a b hX hY hZ hW v]
  change value305 X Y Z W a b v=(0)*v 370 + ((((-68))/(15)))*v 390 + (0)*v 435
  unfold value305
  rw [coordinate_expansion_502 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_319 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 128=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 128 := by
  rw [source_slope_319 X Y Z W a b hX hY hZ hW v]
  change value319 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((816)/(5*Y^2)) + ((408*X)/(5*Y^2)) + ((408*X*a)/(5*Y)) + ((408*X)/(5)))*v 435
  unfold value319
  rw [coordinate_expansion_459 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_326 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 130=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 130 := by
  rw [source_slope_326 X Y Z W a b hX hY hZ hW v]
  change value326 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 435
  unfold value326
  rw [coordinate_expansion_485 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_328 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 131=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 131 := by
  rw [source_slope_328 X Y Z W a b hX hY hZ hW v]
  change value328 X Y Z W a b v=(0)*v 370 + (((51)/(5)))*v 390 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 435
  unfold value328
  rw [coordinate_expansion_489 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 132=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 132 := by
  rw [source_slope_331 X Y Z W a b hX hY hZ hW v]
  change value331 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((102)/(5*Y^2)))*v 435
  unfold value331
  rw [coordinate_expansion_498 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_331

theorem source_value_344 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 134=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 134 := by
  rw [source_slope_344 X Y Z W a b hX hY hZ hW v]
  change value344 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-85))/(W^2)) + (((-85)*Y*a)/(W^2)) + (((-85)*Y^2)/(W^2)))*v 435
  unfold value344
  rw [coordinate_expansion_330 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_352 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 138=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 138 := by
  rw [source_slope_352 X Y Z W a b hX hY hZ hW v]
  change value352 X Y Z W a b v=(0)*v 370 + ((17))*v 390 + (((-17)*X^2) + (((-17)*X^3)/(2)) + (((-17)*X^3*Y*a)/(2)) + (((-17)*X^3*Y^2)/(2)))*v 435
  unfold value352
  rw [coordinate_expansion_465 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_355 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 140=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 140 := by
  rw [source_slope_355 X Y Z W a b hX hY hZ hW v]
  change value355 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-17))/(5)) + (((-17)*Y*a)/(5)) + (((-17)*Y^2)/(5)))*v 435
  unfold value355
  rw [coordinate_expansion_474 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_379 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 144=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 144 := by
  rw [source_slope_379 X Y Z W a b hX hY hZ hW v]
  change value379 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((51*X)/(Y^2)))*v 435
  unfold value379
  rw [coordinate_expansion_75 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_384 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 148=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 148 := by
  rw [source_slope_384 X Y Z W a b hX hY hZ hW v]
  change value384 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value384
  rw [coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_393 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 155=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 155 := by
  rw [source_slope_393 X Y Z W a b hX hY hZ hW v]
  change value393 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value393
  rw [coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_399 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 157=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 157 := by
  rw [source_slope_399 X Y Z W a b hX hY hZ hW v]
  change value399 X Y Z W a b v=(0)*v 370 + (((51)/(5)))*v 390 + ((((-51)*X)/(10*Y^2)) + (((-51)*X*a)/(10*Y)) + ((51*X)/(10)) + (((-51)*X^2)/(5*Y^2)) + (((-51)*X^2*a)/(10*Y)) + (((-51)*X^2*a^2)/(10)) + (((-51)*X^2*Y*a)/(10)))*v 435
  unfold value399
  rw [coordinate_expansion_21 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_401 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 158=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 158 := by
  rw [source_slope_401 X Y Z W a b hX hY hZ hW v]
  change value401 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-17)*X)/(6)) + (((-17)*X*Y*a)/(6)) + (((-17)*X*Y^2)/(6)))*v 435
  unfold value401
  rw [coordinate_expansion_25 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_401

theorem source_value_404 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 161=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 161 := by
  rw [source_slope_404 X Y Z W a b hX hY hZ hW v]
  change value404 X Y Z W a b v=(0)*v 370 + (((255)/(Y^2*W^2)))*v 390 + ((((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^3)/(2*Y^2*W^2)) + (((-255)*X^3*a)/(2*Y*W^2)) + (((-255)*X^3)/(2*W^2)))*v 435
  unfold value404
  rw [coordinate_expansion_479 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_411 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 162=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 162 := by
  rw [source_slope_411 X Y Z W a b hX hY hZ hW v]
  change value411 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-30)*X*Z)/(Y^2*W^2)) + (((-15)*X*Z*a)/(Y*W^2)) + ((30*X*Z)/(W^2)) + (((-15)*X*Z*a^2)/(W^2)) + (((-15)*X*Y*Z*a)/(W^2)))*v 435
  unfold value411
  rw [coordinate_expansion_110 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_485 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 164=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 164 := by
  rw [source_slope_485 X Y Z W a b hX hY hZ hW v]
  change value485 X Y Z W a b v=(0)*v 370 + (((510)/(X*Y^2*W^2)))*v 390 + ((((-510)*X)/(Y^2*W^2)) + (((-255)*X^2)/(Y^2*W^2)) + (((-255)*X^2*a)/(Y*W^2)) + (((-255)*X^2)/(W^2)))*v 435
  unfold value485
  rw [coordinate_expansion_210 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_636 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 167=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 167 := by
  rw [source_slope_636 X Y Z W a b hX hY hZ hW v]
  change value636 X Y Z W a b v=(0)*v 370 + (((510)/(X*Y^2*W^2)))*v 390 + ((((-510)*X)/(Y^2*W^2)))*v 435
  unfold value636
  rw [coordinate_expansion_40 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_675 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 168=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 168 := by
  rw [source_slope_675 X Y Z W a b hX hY hZ hW v]
  change value675 X Y Z W a b v=(0)*v 370 + (((68)/(15)))*v 390 + (0)*v 435
  unfold value675
  rw [coordinate_expansion_263 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_1177 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 183=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 183 := by
  rw [source_slope_1177 X Y Z W a b hX hY hZ hW v]
  change value1177 X Y Z W a b v=(0)*v 370 + (0)*v 390 + ((((-510))/(Y^2*W^2)))*v 435
  unfold value1177
  rw [coordinate_expansion_12 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_1585 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 187=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 187 := by
  rw [source_slope_1585 X Y Z W a b hX hY hZ hW v]
  change value1585 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((510*X)/(Y^2*W^2)))*v 435
  unfold value1585
  rw [coordinate_expansion_20 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 189=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 189 := by
  rw [source_slope_2331 X Y Z W a b hX hY hZ hW v]
  change value2331 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2331
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2331

theorem source_value_2334 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 192=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 192 := by
  rw [source_slope_2334 X Y Z W a b hX hY hZ hW v]
  change value2334 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2334
  rw [coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_425 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2338 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 196=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 196 := by
  rw [source_slope_2338 X Y Z W a b hX hY hZ hW v]
  change value2338 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2338
  rw [coordinate_expansion_85 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2339 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 197=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 197 := by
  rw [source_slope_2339 X Y Z W a b hX hY hZ hW v]
  change value2339 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2339
  rw [coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_425 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2340 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 198=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 198 := by
  rw [source_slope_2340 X Y Z W a b hX hY hZ hW v]
  change value2340 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 435
  unfold value2340
  rw [coordinate_expansion_120 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_290 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2341 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 199=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 199 := by
  rw [source_slope_2341 X Y Z W a b hX hY hZ hW v]
  change value2341 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (((15*Z)/(Y^2*W^2)) + ((15*Z*a)/(Y*W^2)) + (((-15)*Z)/(W^2)) + ((30*X*Z)/(Y^2*W^2)) + ((15*X*Z*a)/(Y*W^2)) + ((15*X*Z*a^2)/(W^2)) + ((15*X*Y*Z*a)/(W^2)))*v 435
  unfold value2341
  rw [coordinate_expansion_220 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2356 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 202=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 202 := by
  rw [source_slope_2356 X Y Z W a b hX hY hZ hW v]
  change value2356 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2356
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2386 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 211=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 211 := by
  rw [source_slope_2386 X Y Z W a b hX hY hZ hW v]
  change value2386 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2386
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2395 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 217=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 217 := by
  rw [source_slope_2395 X Y Z W a b hX hY hZ hW v]
  change value2395 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2395
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2395

theorem source_value_2396 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 218=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 218 := by
  rw [source_slope_2396 X Y Z W a b hX hY hZ hW v]
  change value2396 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2396
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2407 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 228=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 228 := by
  rw [source_slope_2407 X Y Z W a b hX hY hZ hW v]
  change value2407 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2407
  rw [coordinate_expansion_0 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_30 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_60 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_90 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_120 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_150 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_180 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_210 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_240 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_270 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_300 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_330 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_360 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_420 X Y Z W a b hX hY hZ hW v hv]
  rw [coordinate_expansion_450 X Y Z W a b hX hY hZ hW v hv]
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2425 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 238=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 238 := by
  rw [source_slope_2425 X Y Z W a b hX hY hZ hW v]
  change value2425 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2425
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2441 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 247=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 247 := by
  rw [source_slope_2441 X Y Z W a b hX hY hZ hW v]
  change value2441 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2441
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2459 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 259=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 259 := by
  rw [source_slope_2459 X Y Z W a b hX hY hZ hW v]
  change value2459 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2459
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2461 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 260=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 260 := by
  rw [source_slope_2461 X Y Z W a b hX hY hZ hW v]
  change value2461 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2461
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2464 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 261=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 261 := by
  rw [source_slope_2464 X Y Z W a b hX hY hZ hW v]
  change value2464 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2464
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2465 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 262=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 262 := by
  rw [source_slope_2465 X Y Z W a b hX hY hZ hW v]
  change value2465 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2465
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2465

theorem source_value_2469 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 265=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 265 := by
  rw [source_slope_2469 X Y Z W a b hX hY hZ hW v]
  change value2469 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2469
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2475 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 268=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 268 := by
  rw [source_slope_2475 X Y Z W a b hX hY hZ hW v]
  change value2475 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2475
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2480 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 272=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 272 := by
  rw [source_slope_2480 X Y Z W a b hX hY hZ hW v]
  change value2480 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2480
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2485 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 276=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 276 := by
  rw [source_slope_2485 X Y Z W a b hX hY hZ hW v]
  change value2485 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2485
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2486 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 277=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 277 := by
  rw [source_slope_2486 X Y Z W a b hX hY hZ hW v]
  change value2486 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2486
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2498 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 289=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 289 := by
  rw [source_slope_2498 X Y Z W a b hX hY hZ hW v]
  change value2498 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2498
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2504 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 295=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 295 := by
  rw [source_slope_2504 X Y Z W a b hX hY hZ hW v]
  change value2504 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2504
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2512 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 302=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 302 := by
  rw [source_slope_2512 X Y Z W a b hX hY hZ hW v]
  change value2512 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2512
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2512

theorem source_value_2523 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 313=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 313 := by
  rw [source_slope_2523 X Y Z W a b hX hY hZ hW v]
  change value2523 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2523
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2525 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 315=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 315 := by
  rw [source_slope_2525 X Y Z W a b hX hY hZ hW v]
  change value2525 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2525
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2526 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 316=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 316 := by
  rw [source_slope_2526 X Y Z W a b hX hY hZ hW v]
  change value2526 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2526
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2530 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 320=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 320 := by
  rw [source_slope_2530 X Y Z W a b hX hY hZ hW v]
  change value2530 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2530
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2546 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 333=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 333 := by
  rw [source_slope_2546 X Y Z W a b hX hY hZ hW v]
  change value2546 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2546
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2547 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 334=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 334 := by
  rw [source_slope_2547 X Y Z W a b hX hY hZ hW v]
  change value2547 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2547
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2559 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 345=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 345 := by
  rw [source_slope_2559 X Y Z W a b hX hY hZ hW v]
  change value2559 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2559
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2568 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 354=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 354 := by
  rw [source_slope_2568 X Y Z W a b hX hY hZ hW v]
  change value2568 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2568
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2568

theorem source_value_2575 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 360=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 360 := by
  rw [source_slope_2575 X Y Z W a b hX hY hZ hW v]
  change value2575 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2575
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2586 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 370=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 370 := by
  rw [source_slope_2586 X Y Z W a b hX hY hZ hW v]
  change value2586 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2586
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2588 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 372=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 372 := by
  rw [source_slope_2588 X Y Z W a b hX hY hZ hW v]
  change value2588 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2588
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2599 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 382=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 382 := by
  rw [source_slope_2599 X Y Z W a b hX hY hZ hW v]
  change value2599 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2599
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2601 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 384=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 384 := by
  rw [source_slope_2601 X Y Z W a b hX hY hZ hW v]
  change value2601 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2601
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2619 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 399=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 399 := by
  rw [source_slope_2619 X Y Z W a b hX hY hZ hW v]
  change value2619 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2619
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2620 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 400=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 400 := by
  rw [source_slope_2620 X Y Z W a b hX hY hZ hW v]
  change value2620 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2620
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2656 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 417=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 417 := by
  rw [source_slope_2656 X Y Z W a b hX hY hZ hW v]
  change value2656 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2656
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2656

theorem source_value_2664 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 424=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 424 := by
  rw [source_slope_2664 X Y Z W a b hX hY hZ hW v]
  change value2664 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2664
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2672 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 430=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 430 := by
  rw [source_slope_2672 X Y Z W a b hX hY hZ hW v]
  change value2672 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2672
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2675 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 433=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 433 := by
  rw [source_slope_2675 X Y Z W a b hX hY hZ hW v]
  change value2675 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2675
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2686 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 443=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 443 := by
  rw [source_slope_2686 X Y Z W a b hX hY hZ hW v]
  change value2686 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2686
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2692 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 447=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 447 := by
  rw [source_slope_2692 X Y Z W a b hX hY hZ hW v]
  change value2692 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2692
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2699 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 453=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 453 := by
  rw [source_slope_2699 X Y Z W a b hX hY hZ hW v]
  change value2699 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2699
  field_simp [hX,hY,hZ,hW]
  <;> ring

theorem source_value_2746 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v 479=
      initialValues X Y Z W a b ![v 370,v 390,v 435] 479 := by
  rw [source_slope_2746 X Y Z W a b hX hY hZ hW v]
  change value2746 X Y Z W a b v=(0)*v 370 + (0)*v 390 + (0)*v 435
  unfold value2746
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms source_value_2746

end SmallLevelThirtyFourJetSourceMMM
