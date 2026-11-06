module

public import SmallLevelTwentyEightLaurentTheoryV4

/-! Consolidated chapter: SmallLevelTwentyEightTriangular. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyEightTriangularIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightTriangular
open Complex SmallLevelTwentyEightLaurent

theorem pivot0_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row0_5 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_0

theorem pivot0_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 82=0 := by
  have h:=normalized_row0_0 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(Y^2*Z))

#print axioms pivot0_1

theorem pivot0_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 81=0 := by
  have h:=normalized_row0_1 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(X^2*Z))

#print axioms pivot0_2

theorem pivot0_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 42=0 := by
  have h:=normalized_row0_2 X Y Z a hX hY hZ w hw
  have p1:=pivot0_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*Y^2*Z)*p1)*(1)

#print axioms pivot0_3

theorem pivot0_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 78=0 := by
  have h:=normalized_row0_3 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(Z))

#print axioms pivot0_4

theorem pivot0_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row0_6 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot0_5

theorem pivot0_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row0_7 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot0_6

theorem pivot0_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row0_8 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot0_7

theorem pivot0_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row0_10 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3)*(1)

#print axioms pivot0_8

theorem pivot0_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 7=0 := by
  have h:=normalized_row0_20 X Y Z a hX hY hZ w hw
  have p8:=pivot0_8 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8)*(((-1)*Z)/(X^2*Y^2))

#print axioms pivot0_9

theorem pivot0_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 48=0 := by
  have h:=normalized_row0_11 X Y Z a hX hY hZ w hw
  have p9:=pivot0_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p9)*((1*X^2*Y^2)/(Z))

#print axioms pivot0_10

theorem pivot0_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row0_27 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3)*(1)

#print axioms pivot0_11

theorem pivot0_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 77=0 := by
  have h:=normalized_row0_18 X Y Z a hX hY hZ w hw
  have p11:=pivot0_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p11)*((1*Z)/(X^2*Y^2))

#print axioms pivot0_12

theorem pivot0_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 35=0 := by
  have h:=normalized_row0_26 X Y Z a hX hY hZ w hw
  have p11:=pivot0_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Z)/(X^2*Y^2))*p11)*(1)

#print axioms pivot0_13

theorem pivot0_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 39=0 := by
  have h:=normalized_row0_29 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot0_14

theorem pivot0_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 40=0 := by
  have h:=normalized_row0_30 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot0_15

theorem pivot0_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 41=0 := by
  have h:=normalized_row0_31 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot0_16

theorem pivot0_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 43=0 := by
  have h:=normalized_row0_32 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot0_17

theorem pivot0_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 44=0 := by
  have h:=normalized_row0_33 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot0_18

theorem pivot0_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 45=0 := by
  have h:=normalized_row0_34 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot0_19

theorem pivot0_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 49=0 := by
  have h:=normalized_row0_36 X Y Z a hX hY hZ w hw
  have p10:=pivot0_10 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Z)/(X^2*Y^2))*p10)*(1)

#print axioms pivot0_20

theorem pivot0_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 83=0 := by
  have h:=normalized_row0_40 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot0_21

theorem pivot0_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 53=0 := by
  have h:=normalized_row0_82 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_22

theorem pivot0_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 11=0 := by
  have h:=normalized_row0_50 X Y Z a hX hY hZ w hw
  have p22:=pivot0_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22)*(1)

#print axioms pivot0_23

theorem pivot0_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 80=0 := by
  have h:=normalized_row0_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X^2)/(Y^2*Z))

#print axioms pivot0_24

theorem pivot0_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 4 + ((1*X^2)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row0_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_25

theorem pivot0_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 9 + ((1*Y^2)/(X^2*Z))*w 56=0 := by
  have h:=normalized_row0_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_26

theorem pivot0_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*Z)/(X^2))*w 12 + (1)*w 63=0 := by
  have h:=normalized_row0_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(X^2))

#print axioms pivot0_27

theorem pivot0_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 14 + ((1*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row0_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_28

theorem pivot0_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*Z)/(Y^2))*w 18 + (1)*w 70=0 := by
  have h:=normalized_row0_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(Y^2))

#print axioms pivot0_29

theorem pivot0_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 72=0 := by
  have h:=normalized_row0_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Z))

#print axioms pivot0_30

theorem pivot0_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*Y^2)/(X^2*Z))*w 28 + (1)*w 75=0 := by
  have h:=normalized_row0_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2*Z))

#print axioms pivot0_31

theorem pivot0_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X^2)/(Z))*w 21=0 := by
  have h:=normalized_row0_19 X Y Z a hX hY hZ w hw
  have p24:=pivot0_24 X Y Z a hX hY hZ w hw
  have p27:=pivot0_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2*Z)/(X^2))*p24 - (1)*p27)*(((-1)*X^2)/(Z))

#print axioms pivot0_32

theorem pivot0_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 56 + (((-1)*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row0_21 X Y Z a hX hY hZ w hw
  have p26:=pivot0_26 X Y Z a hX hY hZ w hw
  have p28:=pivot0_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2*Z)/(Y^2))*p26 - (1)*p28)*(1)

#print axioms pivot0_33

theorem pivot0_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 24 + (1)*w 66=0 := by
  have h:=normalized_row0_22 X Y Z a hX hY hZ w hw
  have p28:=pivot0_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(Z))*p28)*(1)

#print axioms pivot0_34

theorem pivot0_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*Z)/(Y^2))*w 18 + (1)*w 28=0 := by
  have h:=normalized_row0_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_35

theorem pivot0_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 30=0 := by
  have h:=normalized_row0_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_36

theorem pivot0_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1))/(X^2))*w 18 + (1)*w 33=0 := by
  have h:=normalized_row0_25 X Y Z a hX hY hZ w hw
  have p35:=pivot0_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X^2*Z))*p35)*(1)

#print axioms pivot0_37

theorem pivot0_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 38=0 := by
  have h:=normalized_row0_28 X Y Z a hX hY hZ w hw
  have p27:=pivot0_27 X Y Z a hX hY hZ w hw
  have p32:=pivot0_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Y^2*Z))*p27 - ((1)/(Y^2))*p32)*(1)

#print axioms pivot0_38

theorem pivot0_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 46=0 := by
  have h:=normalized_row0_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_39

theorem pivot0_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 51 + (((-1))/(X^2))*w 66=0 := by
  have h:=normalized_row0_37 X Y Z a hX hY hZ w hw
  have p33:=pivot0_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X^2*Z))*p33)*(1)

#print axioms pivot0_40

theorem pivot0_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 54=0 := by
  have h:=normalized_row0_38 X Y Z a hX hY hZ w hw
  have p27:=pivot0_27 X Y Z a hX hY hZ w hw
  have p32:=pivot0_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p27 - (1)*p32)*(1)

#print axioms pivot0_41

theorem pivot0_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 60=0 := by
  have h:=normalized_row0_39 X Y Z a hX hY hZ w hw
  have p29:=pivot0_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(Z))*p29)*(1)

#print axioms pivot0_42

theorem pivot0_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 79=0 := by
  have h:=normalized_row0_41 X Y Z a hX hY hZ w hw
  have p41:=pivot0_41 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p41)*((1)/(X^2*Y^2))

#print axioms pivot0_43

theorem pivot0_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 8 + (((-1))/(Y^2))*w 18=0 := by
  have h:=normalized_row0_42 X Y Z a hX hY hZ w hw
  have p42:=pivot0_42 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p42)*((1)/(Y^2))

#print axioms pivot0_44

theorem pivot0_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 10 + ((1*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row0_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2))

#print axioms pivot0_45

theorem pivot0_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row0_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2))

#print axioms pivot0_46

theorem pivot0_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 66 + (1)*w 76=0 := by
  have h:=normalized_row0_45 X Y Z a hX hY hZ w hw
  have p34:=pivot0_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p34)*(1)

#print axioms pivot0_47

theorem pivot0_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row0_46 X Y Z a hX hY hZ w hw
  have p36:=pivot0_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p36)*(1)

#print axioms pivot0_48

theorem pivot0_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 47=0 := by
  have h:=normalized_row0_47 X Y Z a hX hY hZ w hw
  have p48:=pivot0_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p48)*(1)

#print axioms pivot0_49

theorem pivot0_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1)/(Y^2))*w 18 + (1)*w 50=0 := by
  have h:=normalized_row0_48 X Y Z a hX hY hZ w hw
  have p44:=pivot0_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p44)*(1)

#print axioms pivot0_50

theorem pivot0_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 52 + (((-1)*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row0_49 X Y Z a hX hY hZ w hw
  have p45:=pivot0_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p45)*(1)

#print axioms pivot0_51

theorem pivot0_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 13 + (1)*w 55=0 := by
  have h:=normalized_row0_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_52

theorem pivot0_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 57 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row0_52 X Y Z a hX hY hZ w hw
  have p46:=pivot0_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p46)*(1)

#print axioms pivot0_53

theorem pivot0_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 58=0 := by
  have h:=normalized_row0_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_54

theorem pivot0_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 59=0 := by
  have h:=normalized_row0_54 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_55

theorem pivot0_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 19 + (1)*w 61=0 := by
  have h:=normalized_row0_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_56

theorem pivot0_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 20 + (1)*w 62=0 := by
  have h:=normalized_row0_56 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_57

theorem pivot0_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 22 + (1)*w 64=0 := by
  have h:=normalized_row0_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_58

theorem pivot0_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 23 + (1)*w 65=0 := by
  have h:=normalized_row0_58 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_59

theorem pivot0_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 25 + (1)*w 67=0 := by
  have h:=normalized_row0_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_60

theorem pivot0_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 26 + (1)*w 68=0 := by
  have h:=normalized_row0_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_61

theorem pivot0_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 27 + (1)*w 69=0 := by
  have h:=normalized_row0_61 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_62

theorem pivot0_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 29 + (1)*w 71=0 := by
  have h:=normalized_row0_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_63

theorem pivot0_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 31 + (1)*w 73=0 := by
  have h:=normalized_row0_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_64

theorem pivot0_65 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 32 + (1)*w 74=0 := by
  have h:=normalized_row0_64 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot0_65

theorem pivot0_66 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 34 + ((1)/(Y^2))*w 66=0 := by
  have h:=normalized_row0_65 X Y Z a hX hY hZ w hw
  have p47:=pivot0_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p47)*(1)

#print axioms pivot0_66

theorem pivot0_67 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 37=0 := by
  have h:=normalized_row0_66 X Y Z a hX hY hZ w hw
  have p43:=pivot0_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p43)*(1)

#print axioms pivot0_67

theorem pivot0_68 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 66=0 := by
  have h:=normalized_row0_67 X Y Z a hX hY hZ w hw
  have p33:=pivot0_33 X Y Z a hX hY hZ w hw
  have p35:=pivot0_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p33 - (1)*p35)*((1*Y^2)/(Z))

#print axioms pivot0_68

theorem pivot0_69 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1)/(X^2*Y^2))*w 66 + (1)*w 71 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row0_68 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  have p35:=pivot0_35 X Y Z a hX hY hZ w hw
  have p53:=pivot0_53 X Y Z a hX hY hZ w hw
  have p63:=pivot0_63 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0 - ((1)/(X^2*Z))*p35 - (1)*p53 - (1)*p63 - ((1)/(X^2*Y^2))*p68)*((-1))

#print axioms pivot0_69

theorem pivot0_70 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 55 + ((1)/(X^2*Y^2))*w 66 + ((-1))*w 69=0 := by
  have h:=normalized_row0_69 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  have p33:=pivot0_33 X Y Z a hX hY hZ w hw
  have p62:=pivot0_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0 - ((1)/(X^2*Z))*p33 - (1)*p62)*(1)

#print axioms pivot0_70

theorem pivot0_71 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 58 + (((-1))/(Y^2))*w 66=0 := by
  have h:=normalized_row0_70 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  have p28:=pivot0_28 X Y Z a hX hY hZ w hw
  have p36:=pivot0_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3 - ((1)/(Z))*p28 - (1)*p36)*(1)

#print axioms pivot0_71

theorem pivot0_72 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (((-1))/(Y^2))*w 66 + (1)*w 68=0 := by
  have h:=normalized_row0_71 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  have p29:=pivot0_29 X Y Z a hX hY hZ w hw
  have p41:=pivot0_41 X Y Z a hX hY hZ w hw
  have p61:=pivot0_61 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3 - ((1)/(Z))*p29 - (1)*p41 - (1)*p61 - (((-1))/(Y^2))*p68)*((-1))

#print axioms pivot0_72

theorem pivot0_73 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + ((-1))*w 66 + (1)*w 74=0 := by
  have h:=normalized_row0_72 X Y Z a hX hY hZ w hw
  have p20:=pivot0_20 X Y Z a hX hY hZ w hw
  have p42:=pivot0_42 X Y Z a hX hY hZ w hw
  have p65:=pivot0_65 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p20 - (1)*p42 - (1)*p65 - ((-1))*p68)*((-1))

#print axioms pivot0_73

theorem pivot0_74 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z))*w 21 + (((-1)*Y^2)/(X^2))*w 66 + (1)*w 69=0 := by
  have h:=normalized_row0_73 X Y Z a hX hY hZ w hw
  have p13:=pivot0_13 X Y Z a hX hY hZ w hw
  have p27:=pivot0_27 X Y Z a hX hY hZ w hw
  have p32:=pivot0_32 X Y Z a hX hY hZ w hw
  have p34:=pivot0_34 X Y Z a hX hY hZ w hw
  have p51:=pivot0_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p13 - ((1*X^2)/(Z))*p27 - ((-1))*p32 - (1)*p34 - (1)*p51)*((1*Y^2)/(X^2))

#print axioms pivot0_74

theorem pivot0_75 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 62 + ((-1))*w 64=0 := by
  have h:=normalized_row0_77 X Y Z a hX hY hZ w hw
  have p15:=pivot0_15 X Y Z a hX hY hZ w hw
  have p18:=pivot0_18 X Y Z a hX hY hZ w hw
  have p24:=pivot0_24 X Y Z a hX hY hZ w hw
  have p25:=pivot0_25 X Y Z a hX hY hZ w hw
  have p44:=pivot0_44 X Y Z a hX hY hZ w hw
  have p47:=pivot0_47 X Y Z a hX hY hZ w hw
  have p51:=pivot0_51 X Y Z a hX hY hZ w hw
  have p54:=pivot0_54 X Y Z a hX hY hZ w hw
  have p57:=pivot0_57 X Y Z a hX hY hZ w hw
  have p65:=pivot0_65 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  have p71:=pivot0_71 X Y Z a hX hY hZ w hw
  have p72:=pivot0_72 X Y Z a hX hY hZ w hw
  have p73:=pivot0_73 X Y Z a hX hY hZ w hw
  have p74:=pivot0_74 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p18 - (1)*p24 - (1)*p25 - (1)*p44 - (1)*p47 - (1)*p51 - (1)*p54 - (1)*p57 - (1)*p65 - ((1)/(Y^2))*p68 - ((-1))*p71 - (1)*p72 - ((-1))*p73 - ((1*X^2)/(Y^2))*p74)*((-1))

#print axioms pivot0_75

theorem pivot0_76 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z) + (2*X^2)/(Z))*w 21 + (1)*w 64 + (((-1))/(Y^2) + ((-1)*Z)/(Y^2) + 1)*w 66=0 := by
  have h:=normalized_row0_76 X Y Z a hX hY hZ w hw
  have p3:=pivot0_3 X Y Z a hX hY hZ w hw
  have p4:=pivot0_4 X Y Z a hX hY hZ w hw
  have p8:=pivot0_8 X Y Z a hX hY hZ w hw
  have p28:=pivot0_28 X Y Z a hX hY hZ w hw
  have p36:=pivot0_36 X Y Z a hX hY hZ w hw
  have p38:=pivot0_38 X Y Z a hX hY hZ w hw
  have p41:=pivot0_41 X Y Z a hX hY hZ w hw
  have p50:=pivot0_50 X Y Z a hX hY hZ w hw
  have p61:=pivot0_61 X Y Z a hX hY hZ w hw
  have p72:=pivot0_72 X Y Z a hX hY hZ w hw
  have p73:=pivot0_73 X Y Z a hX hY hZ w hw
  have p75:=pivot0_75 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p3 - ((1)/(Y^2))*p4 - ((1)/(Y^2))*p8 - (1)*p28 - ((1)/(Y^2))*p36 - (1)*p38 - ((1)/(Y^2))*p41 - (1)*p50 - (1)*p61 - ((-1))*p72 - (1)*p73 - (1)*p75)*(1)

#print axioms pivot0_76

theorem pivot0_77 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66=0 := by
  have h:=normalized_row0_80 X Y Z a hX hY hZ w hw
  have p8:=pivot0_8 X Y Z a hX hY hZ w hw
  have p41:=pivot0_41 X Y Z a hX hY hZ w hw
  have p66:=pivot0_66 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  have p75:=pivot0_75 X Y Z a hX hY hZ w hw
  have p76:=pivot0_76 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8 - ((1)/(Y^2))*p41 - (1)*p66 - (((-1)*a)/(Y))*p68 - (1)*p75 - (1)*p76)*(((-1)*Z)/(2*X^2))

#print axioms pivot0_77

theorem pivot0_78 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 61 + (((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row0_79 X Y Z a hX hY hZ w hw
  have p19:=pivot0_19 X Y Z a hX hY hZ w hw
  have p37:=pivot0_37 X Y Z a hX hY hZ w hw
  have p46:=pivot0_46 X Y Z a hX hY hZ w hw
  have p48:=pivot0_48 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  have p73:=pivot0_73 X Y Z a hX hY hZ w hw
  have p77:=pivot0_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p19 - (1)*p37 - (((-1)*a)/(Y))*p46 - (1)*p48 - ((1)/(X^2))*p68 - ((1*Y*a)/(X^2))*p73 - (((-1))/(Y^2*Z) + (1*Y*a)/(Z))*p77)*(1)

#print axioms pivot0_78

theorem pivot0_79 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 65 + (((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row0_81 X Y Z a hX hY hZ w hw
  have p2:=pivot0_2 X Y Z a hX hY hZ w hw
  have p26:=pivot0_26 X Y Z a hX hY hZ w hw
  have p33:=pivot0_33 X Y Z a hX hY hZ w hw
  have p62:=pivot0_62 X Y Z a hX hY hZ w hw
  have p67:=pivot0_67 X Y Z a hX hY hZ w hw
  have p74:=pivot0_74 X Y Z a hX hY hZ w hw
  have p77:=pivot0_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p2 - (1)*p26 - (((-1)*Y^2)/(X^2*Z))*p33 - (((-1)*a)/(Y))*p62 - (1)*p67 - ((1*a)/(Y))*p74 - (((-1))/(Y^2*Z) + (1*Y*a)/(Z))*p77)*(1)

#print axioms pivot0_79

theorem pivot0_80 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (1)*w 59 + (((-1))/(X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66=0 := by
  have h:=normalized_row0_75 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  have p10:=pivot0_10 X Y Z a hX hY hZ w hw
  have p13:=pivot0_13 X Y Z a hX hY hZ w hw
  have p23:=pivot0_23 X Y Z a hX hY hZ w hw
  have p30:=pivot0_30 X Y Z a hX hY hZ w hw
  have p32:=pivot0_32 X Y Z a hX hY hZ w hw
  have p34:=pivot0_34 X Y Z a hX hY hZ w hw
  have p42:=pivot0_42 X Y Z a hX hY hZ w hw
  have p49:=pivot0_49 X Y Z a hX hY hZ w hw
  have p59:=pivot0_59 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  have p69:=pivot0_69 X Y Z a hX hY hZ w hw
  have p73:=pivot0_73 X Y Z a hX hY hZ w hw
  have p77:=pivot0_77 X Y Z a hX hY hZ w hw
  have p79:=pivot0_79 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p0 - ((1)/(X^2*Y^2))*p10 - (1)*p13 - (1)*p23 - ((1)/(X^2*Y^2))*p30 - ((1)/(X^2*Y^2))*p32 - ((1)/(X^2*Y^2))*p34 - ((1)/(X^2*Y^2))*p42 - (1)*p49 - (1)*p59 - (((-1))/(X^2*Y^2))*p68 - (1)*p69 - ((1*Y^2)/(X^2))*p73 - ((1)/(Y^2*Z) + (1*Y^2)/(Z))*p77 - ((-1))*p79)*(1)

#print axioms pivot0_80

theorem pivot0_81 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-1))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(2*X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66 + (1)*w 73=0 := by
  have h:=normalized_row0_78 X Y Z a hX hY hZ w hw
  have p7:=pivot0_7 X Y Z a hX hY hZ w hw
  have p26:=pivot0_26 X Y Z a hX hY hZ w hw
  have p33:=pivot0_33 X Y Z a hX hY hZ w hw
  have p62:=pivot0_62 X Y Z a hX hY hZ w hw
  have p64:=pivot0_64 X Y Z a hX hY hZ w hw
  have p74:=pivot0_74 X Y Z a hX hY hZ w hw
  have p77:=pivot0_77 X Y Z a hX hY hZ w hw
  have p80:=pivot0_80 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p7 - (((-1)*a)/(Y))*p26 - ((1*Y*a)/(X^2*Z))*p33 - ((1)/(Y^2))*p62 - (1)*p64 - (((-1))/(Y^2))*p74 - (((-1))/(Z))*p77 - (1)*p80)*((-1))

#print axioms pivot0_81

theorem pivot0_82 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (((-2))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(X^2) + (1*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66 + (1)*w 67=0 := by
  have h:=normalized_row0_74 X Y Z a hX hY hZ w hw
  have p0:=pivot0_0 X Y Z a hX hY hZ w hw
  have p11:=pivot0_11 X Y Z a hX hY hZ w hw
  have p20:=pivot0_20 X Y Z a hX hY hZ w hw
  have p30:=pivot0_30 X Y Z a hX hY hZ w hw
  have p32:=pivot0_32 X Y Z a hX hY hZ w hw
  have p34:=pivot0_34 X Y Z a hX hY hZ w hw
  have p42:=pivot0_42 X Y Z a hX hY hZ w hw
  have p52:=pivot0_52 X Y Z a hX hY hZ w hw
  have p60:=pivot0_60 X Y Z a hX hY hZ w hw
  have p67:=pivot0_67 X Y Z a hX hY hZ w hw
  have p68:=pivot0_68 X Y Z a hX hY hZ w hw
  have p70:=pivot0_70 X Y Z a hX hY hZ w hw
  have p74:=pivot0_74 X Y Z a hX hY hZ w hw
  have p77:=pivot0_77 X Y Z a hX hY hZ w hw
  have p78:=pivot0_78 X Y Z a hX hY hZ w hw
  have p81:=pivot0_81 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p0 - ((1)/(X^2*Y^2))*p11 - (1)*p20 - ((1)/(X^2*Y^2))*p30 - ((1)/(X^2*Y^2))*p32 - ((1)/(X^2*Y^2))*p34 - ((1)/(X^2*Y^2))*p42 - (1)*p52 - (1)*p60 - (1)*p67 - (((-1))/(X^2*Y^2))*p68 - ((-1))*p70 - ((-1))*p74 - (((-1))/(Y^2*Z) + ((-1)*Y^2)/(Z))*p77 - (1)*p78 - (1)*p81)*((-1))

#print axioms pivot0_82

end SmallLevelTwentyEightTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightTriangular
open Complex SmallLevelTwentyEightLaurent

theorem pivot1_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row1_5 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_0

theorem pivot1_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 82=0 := by
  have h:=normalized_row1_0 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(Y^2*Z))

#print axioms pivot1_1

theorem pivot1_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 81=0 := by
  have h:=normalized_row1_1 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(X^2*Z))

#print axioms pivot1_2

theorem pivot1_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 42=0 := by
  have h:=normalized_row1_2 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*Y^2*Z)*p1)*(1)

#print axioms pivot1_3

theorem pivot1_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 78=0 := by
  have h:=normalized_row1_3 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(Z))

#print axioms pivot1_4

theorem pivot1_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row1_6 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot1_5

theorem pivot1_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row1_7 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot1_6

theorem pivot1_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row1_8 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot1_7

theorem pivot1_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row1_10 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3)*(1)

#print axioms pivot1_8

theorem pivot1_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 7=0 := by
  have h:=normalized_row1_20 X Y Z a hX hY hZ w hw
  have p8:=pivot1_8 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8)*(((-1)*Z)/(X^2*Y^2))

#print axioms pivot1_9

theorem pivot1_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 48=0 := by
  have h:=normalized_row1_11 X Y Z a hX hY hZ w hw
  have p9:=pivot1_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p9)*((1*X^2*Y^2)/(Z))

#print axioms pivot1_10

theorem pivot1_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row1_27 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3)*(1)

#print axioms pivot1_11

theorem pivot1_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 77=0 := by
  have h:=normalized_row1_18 X Y Z a hX hY hZ w hw
  have p11:=pivot1_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p11)*((1*Z)/(X^2*Y^2))

#print axioms pivot1_12

theorem pivot1_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 35=0 := by
  have h:=normalized_row1_26 X Y Z a hX hY hZ w hw
  have p11:=pivot1_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Z)/(X^2*Y^2))*p11)*(1)

#print axioms pivot1_13

theorem pivot1_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 39=0 := by
  have h:=normalized_row1_29 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot1_14

theorem pivot1_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 40=0 := by
  have h:=normalized_row1_30 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot1_15

theorem pivot1_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 41=0 := by
  have h:=normalized_row1_31 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot1_16

theorem pivot1_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 43=0 := by
  have h:=normalized_row1_32 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot1_17

theorem pivot1_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 44=0 := by
  have h:=normalized_row1_33 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot1_18

theorem pivot1_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 45=0 := by
  have h:=normalized_row1_34 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot1_19

theorem pivot1_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 49=0 := by
  have h:=normalized_row1_36 X Y Z a hX hY hZ w hw
  have p10:=pivot1_10 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Z)/(X^2*Y^2))*p10)*(1)

#print axioms pivot1_20

theorem pivot1_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 83=0 := by
  have h:=normalized_row1_40 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot1_21

theorem pivot1_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 53=0 := by
  have h:=normalized_row1_82 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_22

theorem pivot1_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 11=0 := by
  have h:=normalized_row1_50 X Y Z a hX hY hZ w hw
  have p22:=pivot1_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22)*(1)

#print axioms pivot1_23

theorem pivot1_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 80=0 := by
  have h:=normalized_row1_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X^2)/(Y^2*Z))

#print axioms pivot1_24

theorem pivot1_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 4 + ((1*X^2)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row1_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_25

theorem pivot1_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 9 + ((1*Y^2)/(X^2*Z))*w 56=0 := by
  have h:=normalized_row1_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_26

theorem pivot1_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*Z)/(X^2))*w 12 + (1)*w 63=0 := by
  have h:=normalized_row1_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(X^2))

#print axioms pivot1_27

theorem pivot1_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 14 + ((1*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row1_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_28

theorem pivot1_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*Z)/(Y^2))*w 18 + (1)*w 70=0 := by
  have h:=normalized_row1_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(Y^2))

#print axioms pivot1_29

theorem pivot1_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 72=0 := by
  have h:=normalized_row1_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Z))

#print axioms pivot1_30

theorem pivot1_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*Y^2)/(X^2*Z))*w 28 + (1)*w 75=0 := by
  have h:=normalized_row1_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2*Z))

#print axioms pivot1_31

theorem pivot1_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X^2)/(Z))*w 21=0 := by
  have h:=normalized_row1_19 X Y Z a hX hY hZ w hw
  have p24:=pivot1_24 X Y Z a hX hY hZ w hw
  have p27:=pivot1_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2*Z)/(X^2))*p24 - (1)*p27)*(((-1)*X^2)/(Z))

#print axioms pivot1_32

theorem pivot1_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 56 + (((-1)*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row1_21 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2*Z)/(Y^2))*p26 - (1)*p28)*(1)

#print axioms pivot1_33

theorem pivot1_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 24 + (1)*w 66=0 := by
  have h:=normalized_row1_22 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(Z))*p28)*(1)

#print axioms pivot1_34

theorem pivot1_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*Z)/(Y^2))*w 18 + (1)*w 28=0 := by
  have h:=normalized_row1_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_35

theorem pivot1_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 30=0 := by
  have h:=normalized_row1_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_36

theorem pivot1_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1))/(X^2))*w 18 + (1)*w 33=0 := by
  have h:=normalized_row1_25 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X^2*Z))*p35)*(1)

#print axioms pivot1_37

theorem pivot1_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 38=0 := by
  have h:=normalized_row1_28 X Y Z a hX hY hZ w hw
  have p27:=pivot1_27 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Y^2*Z))*p27 - ((1)/(Y^2))*p32)*(1)

#print axioms pivot1_38

theorem pivot1_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 46=0 := by
  have h:=normalized_row1_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_39

theorem pivot1_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 51 + (((-1))/(X^2))*w 66=0 := by
  have h:=normalized_row1_37 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X^2*Z))*p33)*(1)

#print axioms pivot1_40

theorem pivot1_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 54=0 := by
  have h:=normalized_row1_38 X Y Z a hX hY hZ w hw
  have p27:=pivot1_27 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p27 - (1)*p32)*(1)

#print axioms pivot1_41

theorem pivot1_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 60=0 := by
  have h:=normalized_row1_39 X Y Z a hX hY hZ w hw
  have p29:=pivot1_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(Z))*p29)*(1)

#print axioms pivot1_42

theorem pivot1_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 79=0 := by
  have h:=normalized_row1_41 X Y Z a hX hY hZ w hw
  have p41:=pivot1_41 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p41)*((1)/(X^2*Y^2))

#print axioms pivot1_43

theorem pivot1_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 8 + (((-1))/(Y^2))*w 18=0 := by
  have h:=normalized_row1_42 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p42)*((1)/(Y^2))

#print axioms pivot1_44

theorem pivot1_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 10 + ((1*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row1_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2))

#print axioms pivot1_45

theorem pivot1_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row1_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2))

#print axioms pivot1_46

theorem pivot1_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 66 + (1)*w 76=0 := by
  have h:=normalized_row1_45 X Y Z a hX hY hZ w hw
  have p34:=pivot1_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p34)*(1)

#print axioms pivot1_47

theorem pivot1_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row1_46 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p36)*(1)

#print axioms pivot1_48

theorem pivot1_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 47=0 := by
  have h:=normalized_row1_47 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p48)*(1)

#print axioms pivot1_49

theorem pivot1_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1)/(Y^2))*w 18 + (1)*w 50=0 := by
  have h:=normalized_row1_48 X Y Z a hX hY hZ w hw
  have p44:=pivot1_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p44)*(1)

#print axioms pivot1_50

theorem pivot1_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 52 + (((-1)*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row1_49 X Y Z a hX hY hZ w hw
  have p45:=pivot1_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p45)*(1)

#print axioms pivot1_51

theorem pivot1_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 13 + (1)*w 55=0 := by
  have h:=normalized_row1_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_52

theorem pivot1_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 57 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row1_52 X Y Z a hX hY hZ w hw
  have p46:=pivot1_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p46)*(1)

#print axioms pivot1_53

theorem pivot1_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 58=0 := by
  have h:=normalized_row1_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_54

theorem pivot1_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 59=0 := by
  have h:=normalized_row1_54 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_55

theorem pivot1_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 19 + (1)*w 61=0 := by
  have h:=normalized_row1_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_56

theorem pivot1_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 20 + (1)*w 62=0 := by
  have h:=normalized_row1_56 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_57

theorem pivot1_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 22 + (1)*w 64=0 := by
  have h:=normalized_row1_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_58

theorem pivot1_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 23 + (1)*w 65=0 := by
  have h:=normalized_row1_58 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_59

theorem pivot1_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 25 + (1)*w 67=0 := by
  have h:=normalized_row1_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_60

theorem pivot1_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 26 + (1)*w 68=0 := by
  have h:=normalized_row1_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_61

theorem pivot1_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 27 + (1)*w 69=0 := by
  have h:=normalized_row1_61 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_62

theorem pivot1_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 29 + (1)*w 71=0 := by
  have h:=normalized_row1_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_63

theorem pivot1_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 31 + (1)*w 73=0 := by
  have h:=normalized_row1_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_64

theorem pivot1_65 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 32 + (1)*w 74=0 := by
  have h:=normalized_row1_64 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_65

theorem pivot1_66 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 34 + ((1)/(Y^2))*w 66=0 := by
  have h:=normalized_row1_65 X Y Z a hX hY hZ w hw
  have p47:=pivot1_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p47)*(1)

#print axioms pivot1_66

theorem pivot1_67 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 37=0 := by
  have h:=normalized_row1_66 X Y Z a hX hY hZ w hw
  have p43:=pivot1_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p43)*(1)

#print axioms pivot1_67

theorem pivot1_68 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 66=0 := by
  have h:=normalized_row1_67 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p33 - (1)*p35)*((1*Y^2)/(Z))

#print axioms pivot1_68

theorem pivot1_69 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1)/(X^2*Y^2))*w 66 + (1)*w 71 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row1_68 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  have p53:=pivot1_53 X Y Z a hX hY hZ w hw
  have p63:=pivot1_63 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0 - ((1)/(X^2*Z))*p35 - (1)*p53 - (1)*p63 - ((1)/(X^2*Y^2))*p68)*((-1))

#print axioms pivot1_69

theorem pivot1_70 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 55 + ((1)/(X^2*Y^2))*w 66 + ((-1))*w 69=0 := by
  have h:=normalized_row1_69 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  have p62:=pivot1_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0 - ((1)/(X^2*Z))*p33 - (1)*p62)*(1)

#print axioms pivot1_70

theorem pivot1_71 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 58 + (((-1))/(Y^2))*w 66=0 := by
  have h:=normalized_row1_70 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3 - ((1)/(Z))*p28 - (1)*p36)*(1)

#print axioms pivot1_71

theorem pivot1_72 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (((-1))/(Y^2))*w 66 + (1)*w 68=0 := by
  have h:=normalized_row1_71 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  have p29:=pivot1_29 X Y Z a hX hY hZ w hw
  have p41:=pivot1_41 X Y Z a hX hY hZ w hw
  have p61:=pivot1_61 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3 - ((1)/(Z))*p29 - (1)*p41 - (1)*p61 - (((-1))/(Y^2))*p68)*((-1))

#print axioms pivot1_72

theorem pivot1_73 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + ((-1))*w 66 + (1)*w 74=0 := by
  have h:=normalized_row1_72 X Y Z a hX hY hZ w hw
  have p20:=pivot1_20 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p65:=pivot1_65 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p20 - (1)*p42 - (1)*p65 - ((-1))*p68)*((-1))

#print axioms pivot1_73

theorem pivot1_74 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z))*w 21 + (((-1)*Y^2)/(X^2))*w 66 + (1)*w 69=0 := by
  have h:=normalized_row1_73 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p27:=pivot1_27 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  have p34:=pivot1_34 X Y Z a hX hY hZ w hw
  have p51:=pivot1_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p13 - ((1*X^2)/(Z))*p27 - ((-1))*p32 - (1)*p34 - (1)*p51)*((1*Y^2)/(X^2))

#print axioms pivot1_74

theorem pivot1_75 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 62 + ((-1))*w 64=0 := by
  have h:=normalized_row1_77 X Y Z a hX hY hZ w hw
  have p15:=pivot1_15 X Y Z a hX hY hZ w hw
  have p18:=pivot1_18 X Y Z a hX hY hZ w hw
  have p24:=pivot1_24 X Y Z a hX hY hZ w hw
  have p25:=pivot1_25 X Y Z a hX hY hZ w hw
  have p44:=pivot1_44 X Y Z a hX hY hZ w hw
  have p47:=pivot1_47 X Y Z a hX hY hZ w hw
  have p51:=pivot1_51 X Y Z a hX hY hZ w hw
  have p54:=pivot1_54 X Y Z a hX hY hZ w hw
  have p57:=pivot1_57 X Y Z a hX hY hZ w hw
  have p65:=pivot1_65 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p71:=pivot1_71 X Y Z a hX hY hZ w hw
  have p72:=pivot1_72 X Y Z a hX hY hZ w hw
  have p73:=pivot1_73 X Y Z a hX hY hZ w hw
  have p74:=pivot1_74 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p18 - (1)*p24 - (1)*p25 - (1)*p44 - (1)*p47 - (1)*p51 - (1)*p54 - (1)*p57 - (1)*p65 - ((1)/(Y^2))*p68 - ((-1))*p71 - (1)*p72 - ((-1))*p73 - ((1*X^2)/(Y^2))*p74)*((-1))

#print axioms pivot1_75

theorem pivot1_76 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z) + (2*X^2)/(Z))*w 21 + (1)*w 64 + ((1)/(Y^2) + ((-1)*Z)/(Y^2) + 1)*w 66=0 := by
  have h:=normalized_row1_76 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  have p4:=pivot1_4 X Y Z a hX hY hZ w hw
  have p8:=pivot1_8 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p41:=pivot1_41 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  have p61:=pivot1_61 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p72:=pivot1_72 X Y Z a hX hY hZ w hw
  have p73:=pivot1_73 X Y Z a hX hY hZ w hw
  have p75:=pivot1_75 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2))*p3 - (((-1))/(Y^2))*p4 - (((-1))/(Y^2))*p8 - (1)*p28 - (((-1))/(Y^2))*p36 - (1)*p38 - (((-1))/(Y^2))*p41 - (1)*p50 - (1)*p61 - (((-2))/(Y^2))*p68 - ((-1))*p72 - (1)*p73 - (1)*p75)*(1)

#print axioms pivot1_76

theorem pivot1_77 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 21 + ((1*Z)/(X^2*Y^2) + ((-1)*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66=0 := by
  have h:=normalized_row1_80 X Y Z a hX hY hZ w hw
  have p8:=pivot1_8 X Y Z a hX hY hZ w hw
  have p41:=pivot1_41 X Y Z a hX hY hZ w hw
  have p66:=pivot1_66 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p75:=pivot1_75 X Y Z a hX hY hZ w hw
  have p76:=pivot1_76 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8 - ((1)/(Y^2))*p41 - (1)*p66 - (((-1)*a)/(Y))*p68 - (1)*p75 - (1)*p76)*(((-1)*Z)/(2*X^2))

#print axioms pivot1_77

theorem pivot1_78 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 61 + ((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row1_79 X Y Z a hX hY hZ w hw
  have p19:=pivot1_19 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  have p46:=pivot1_46 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p73:=pivot1_73 X Y Z a hX hY hZ w hw
  have p77:=pivot1_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p19 - (1)*p37 - (((-1)*a)/(Y))*p46 - (1)*p48 - ((1)/(X^2))*p68 - ((1*Y*a)/(X^2))*p73 - (((-1))/(Y^2*Z) + (1*Y*a)/(Z))*p77)*(1)

#print axioms pivot1_78

theorem pivot1_79 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 65 + ((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row1_81 X Y Z a hX hY hZ w hw
  have p2:=pivot1_2 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  have p62:=pivot1_62 X Y Z a hX hY hZ w hw
  have p67:=pivot1_67 X Y Z a hX hY hZ w hw
  have p74:=pivot1_74 X Y Z a hX hY hZ w hw
  have p77:=pivot1_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p2 - (1)*p26 - (((-1)*Y^2)/(X^2*Z))*p33 - (((-1)*a)/(Y))*p62 - (1)*p67 - ((1*a)/(Y))*p74 - (((-1))/(Y^2*Z) + (1*Y*a)/(Z))*p77)*(1)

#print axioms pivot1_79

theorem pivot1_80 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (1)*w 59 + (((-1))/(X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-2))/(X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66=0 := by
  have h:=normalized_row1_75 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p10:=pivot1_10 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p23:=pivot1_23 X Y Z a hX hY hZ w hw
  have p30:=pivot1_30 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  have p34:=pivot1_34 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p49:=pivot1_49 X Y Z a hX hY hZ w hw
  have p59:=pivot1_59 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p69:=pivot1_69 X Y Z a hX hY hZ w hw
  have p73:=pivot1_73 X Y Z a hX hY hZ w hw
  have p77:=pivot1_77 X Y Z a hX hY hZ w hw
  have p79:=pivot1_79 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2))*p0 - (((-1))/(X^2*Y^2))*p10 - (1)*p13 - (1)*p23 - (((-1))/(X^2*Y^2))*p30 - (((-1))/(X^2*Y^2))*p32 - (((-1))/(X^2*Y^2))*p34 - (((-1))/(X^2*Y^2))*p42 - (1)*p49 - (1)*p59 - ((1)/(X^2*Y^2))*p68 - (1)*p69 - ((1*Y^2)/(X^2))*p73 - ((1)/(Y^2*Z) + (1*Y^2)/(Z))*p77 - ((-1))*p79)*(1)

#print axioms pivot1_80

theorem pivot1_81 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-2))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-3)*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66 + (1)*w 73=0 := by
  have h:=normalized_row1_78 X Y Z a hX hY hZ w hw
  have p7:=pivot1_7 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  have p62:=pivot1_62 X Y Z a hX hY hZ w hw
  have p64:=pivot1_64 X Y Z a hX hY hZ w hw
  have p74:=pivot1_74 X Y Z a hX hY hZ w hw
  have p77:=pivot1_77 X Y Z a hX hY hZ w hw
  have p80:=pivot1_80 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p7 - (((-1)*a)/(Y))*p26 - ((1*Y*a)/(X^2*Z))*p33 - ((1)/(Y^2))*p62 - (1)*p64 - (((-1))/(Y^2))*p74 - (((-1))/(Z))*p77 - (1)*p80)*((-1))

#print axioms pivot1_81

theorem pivot1_82 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (((-3))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-5)*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + ((-7))/(2*X^2) + (1*a^2)/(X^2) + (1*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66 + (1)*w 67=0 := by
  have h:=normalized_row1_74 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p11:=pivot1_11 X Y Z a hX hY hZ w hw
  have p20:=pivot1_20 X Y Z a hX hY hZ w hw
  have p30:=pivot1_30 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  have p34:=pivot1_34 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p52:=pivot1_52 X Y Z a hX hY hZ w hw
  have p60:=pivot1_60 X Y Z a hX hY hZ w hw
  have p67:=pivot1_67 X Y Z a hX hY hZ w hw
  have p68:=pivot1_68 X Y Z a hX hY hZ w hw
  have p70:=pivot1_70 X Y Z a hX hY hZ w hw
  have p74:=pivot1_74 X Y Z a hX hY hZ w hw
  have p77:=pivot1_77 X Y Z a hX hY hZ w hw
  have p78:=pivot1_78 X Y Z a hX hY hZ w hw
  have p81:=pivot1_81 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2))*p0 - (((-1))/(X^2*Y^2))*p11 - (1)*p20 - (((-1))/(X^2*Y^2))*p30 - (((-1))/(X^2*Y^2))*p32 - (((-1))/(X^2*Y^2))*p34 - (((-1))/(X^2*Y^2))*p42 - (1)*p52 - (1)*p60 - (1)*p67 - ((1)/(X^2*Y^2))*p68 - ((-1))*p70 - ((-1))*p74 - (((-1))/(Y^2*Z) + ((-1)*Y^2)/(Z))*p77 - (1)*p78 - (1)*p81)*((-1))

#print axioms pivot1_82

end SmallLevelTwentyEightTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightTriangular
open Complex SmallLevelTwentyEightLaurent

theorem pivot2_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row2_5 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_0

theorem pivot2_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 82=0 := by
  have h:=normalized_row2_0 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(Y^2*Z))

#print axioms pivot2_1

theorem pivot2_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 81=0 := by
  have h:=normalized_row2_1 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X^2*Z))

#print axioms pivot2_2

theorem pivot2_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 42=0 := by
  have h:=normalized_row2_2 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*Y^2*Z)*p1)*(1)

#print axioms pivot2_3

theorem pivot2_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 78=0 := by
  have h:=normalized_row2_3 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(Z))

#print axioms pivot2_4

theorem pivot2_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row2_6 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot2_5

theorem pivot2_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row2_7 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot2_6

theorem pivot2_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row2_8 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot2_7

theorem pivot2_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row2_10 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3)*(1)

#print axioms pivot2_8

theorem pivot2_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 7=0 := by
  have h:=normalized_row2_20 X Y Z a hX hY hZ w hw
  have p8:=pivot2_8 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8)*((1*Z)/(X^2*Y^2))

#print axioms pivot2_9

theorem pivot2_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 48=0 := by
  have h:=normalized_row2_11 X Y Z a hX hY hZ w hw
  have p9:=pivot2_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p9)*(((-1)*X^2*Y^2)/(Z))

#print axioms pivot2_10

theorem pivot2_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row2_27 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3)*(1)

#print axioms pivot2_11

theorem pivot2_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 77=0 := by
  have h:=normalized_row2_18 X Y Z a hX hY hZ w hw
  have p11:=pivot2_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p11)*(((-1)*Z)/(X^2*Y^2))

#print axioms pivot2_12

theorem pivot2_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 35=0 := by
  have h:=normalized_row2_26 X Y Z a hX hY hZ w hw
  have p11:=pivot2_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Z)/(X^2*Y^2))*p11)*(1)

#print axioms pivot2_13

theorem pivot2_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 39=0 := by
  have h:=normalized_row2_29 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot2_14

theorem pivot2_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 40=0 := by
  have h:=normalized_row2_30 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot2_15

theorem pivot2_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 41=0 := by
  have h:=normalized_row2_31 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot2_16

theorem pivot2_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 43=0 := by
  have h:=normalized_row2_32 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot2_17

theorem pivot2_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 44=0 := by
  have h:=normalized_row2_33 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot2_18

theorem pivot2_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 45=0 := by
  have h:=normalized_row2_34 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot2_19

theorem pivot2_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 49=0 := by
  have h:=normalized_row2_36 X Y Z a hX hY hZ w hw
  have p10:=pivot2_10 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Z)/(X^2*Y^2))*p10)*(1)

#print axioms pivot2_20

theorem pivot2_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 83=0 := by
  have h:=normalized_row2_40 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot2_21

theorem pivot2_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 53=0 := by
  have h:=normalized_row2_82 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_22

theorem pivot2_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 11=0 := by
  have h:=normalized_row2_50 X Y Z a hX hY hZ w hw
  have p22:=pivot2_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22)*(1)

#print axioms pivot2_23

theorem pivot2_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 80=0 := by
  have h:=normalized_row2_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2*Z))

#print axioms pivot2_24

theorem pivot2_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 4 + (((-1)*X^2)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row2_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_25

theorem pivot2_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X^2*Z))*w 56=0 := by
  have h:=normalized_row2_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_26

theorem pivot2_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*Z)/(X^2))*w 12 + (1)*w 63=0 := by
  have h:=normalized_row2_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X^2))

#print axioms pivot2_27

theorem pivot2_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 14 + (((-1)*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row2_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_28

theorem pivot2_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*Z)/(Y^2))*w 18 + (1)*w 70=0 := by
  have h:=normalized_row2_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(Y^2))

#print axioms pivot2_29

theorem pivot2_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 72=0 := by
  have h:=normalized_row2_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X^2)/(Z))

#print axioms pivot2_30

theorem pivot2_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(X^2*Z))*w 28 + (1)*w 75=0 := by
  have h:=normalized_row2_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X^2*Z))

#print axioms pivot2_31

theorem pivot2_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 12 + ((1*X^2)/(Z))*w 21=0 := by
  have h:=normalized_row2_19 X Y Z a hX hY hZ w hw
  have p24:=pivot2_24 X Y Z a hX hY hZ w hw
  have p27:=pivot2_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2*Z)/(X^2))*p24 - (1)*p27)*((1*X^2)/(Z))

#print axioms pivot2_32

theorem pivot2_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 56 + ((1*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row2_21 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2*Z)/(Y^2))*p26 - (1)*p28)*(1)

#print axioms pivot2_33

theorem pivot2_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 24 + (1)*w 66=0 := by
  have h:=normalized_row2_22 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(Z))*p28)*(1)

#print axioms pivot2_34

theorem pivot2_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*Z)/(Y^2))*w 18 + (1)*w 28=0 := by
  have h:=normalized_row2_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_35

theorem pivot2_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 30=0 := by
  have h:=normalized_row2_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_36

theorem pivot2_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1))/(X^2))*w 18 + (1)*w 33=0 := by
  have h:=normalized_row2_25 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X^2*Z))*p35)*(1)

#print axioms pivot2_37

theorem pivot2_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 38=0 := by
  have h:=normalized_row2_28 X Y Z a hX hY hZ w hw
  have p27:=pivot2_27 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Y^2*Z))*p27 - ((1)/(Y^2))*p32)*(1)

#print axioms pivot2_38

theorem pivot2_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 46=0 := by
  have h:=normalized_row2_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_39

theorem pivot2_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 51 + (((-1))/(X^2))*w 66=0 := by
  have h:=normalized_row2_37 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X^2*Z))*p33)*(1)

#print axioms pivot2_40

theorem pivot2_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 54=0 := by
  have h:=normalized_row2_38 X Y Z a hX hY hZ w hw
  have p27:=pivot2_27 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p27 - (1)*p32)*(1)

#print axioms pivot2_41

theorem pivot2_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 60=0 := by
  have h:=normalized_row2_39 X Y Z a hX hY hZ w hw
  have p29:=pivot2_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(Z))*p29)*(1)

#print axioms pivot2_42

theorem pivot2_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 79=0 := by
  have h:=normalized_row2_41 X Y Z a hX hY hZ w hw
  have p41:=pivot2_41 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p41)*((1)/(X^2*Y^2))

#print axioms pivot2_43

theorem pivot2_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 8 + (((-1))/(Y^2))*w 18=0 := by
  have h:=normalized_row2_42 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p42)*((1)/(Y^2))

#print axioms pivot2_44

theorem pivot2_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 10 + ((1*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row2_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2))

#print axioms pivot2_45

theorem pivot2_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row2_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2))

#print axioms pivot2_46

theorem pivot2_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 66 + (1)*w 76=0 := by
  have h:=normalized_row2_45 X Y Z a hX hY hZ w hw
  have p34:=pivot2_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p34)*(1)

#print axioms pivot2_47

theorem pivot2_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 5 + (((-1))/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row2_46 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p36)*(1)

#print axioms pivot2_48

theorem pivot2_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 47=0 := by
  have h:=normalized_row2_47 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p48)*(1)

#print axioms pivot2_49

theorem pivot2_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1)/(Y^2))*w 18 + (1)*w 50=0 := by
  have h:=normalized_row2_48 X Y Z a hX hY hZ w hw
  have p44:=pivot2_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p44)*(1)

#print axioms pivot2_50

theorem pivot2_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 52 + (((-1)*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row2_49 X Y Z a hX hY hZ w hw
  have p45:=pivot2_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p45)*(1)

#print axioms pivot2_51

theorem pivot2_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 13 + (1)*w 55=0 := by
  have h:=normalized_row2_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_52

theorem pivot2_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 57 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row2_52 X Y Z a hX hY hZ w hw
  have p46:=pivot2_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p46)*(1)

#print axioms pivot2_53

theorem pivot2_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 58=0 := by
  have h:=normalized_row2_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_54

theorem pivot2_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 59=0 := by
  have h:=normalized_row2_54 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_55

theorem pivot2_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 19 + (1)*w 61=0 := by
  have h:=normalized_row2_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_56

theorem pivot2_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 20 + (1)*w 62=0 := by
  have h:=normalized_row2_56 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_57

theorem pivot2_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 22 + (1)*w 64=0 := by
  have h:=normalized_row2_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_58

theorem pivot2_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 23 + (1)*w 65=0 := by
  have h:=normalized_row2_58 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_59

theorem pivot2_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 25 + (1)*w 67=0 := by
  have h:=normalized_row2_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_60

theorem pivot2_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 26 + (1)*w 68=0 := by
  have h:=normalized_row2_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_61

theorem pivot2_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 27 + (1)*w 69=0 := by
  have h:=normalized_row2_61 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_62

theorem pivot2_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 29 + (1)*w 71=0 := by
  have h:=normalized_row2_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_63

theorem pivot2_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 31 + (1)*w 73=0 := by
  have h:=normalized_row2_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_64

theorem pivot2_65 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 32 + (1)*w 74=0 := by
  have h:=normalized_row2_64 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_65

theorem pivot2_66 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 34 + ((1)/(Y^2))*w 66=0 := by
  have h:=normalized_row2_65 X Y Z a hX hY hZ w hw
  have p47:=pivot2_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p47)*(1)

#print axioms pivot2_66

theorem pivot2_67 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 37=0 := by
  have h:=normalized_row2_66 X Y Z a hX hY hZ w hw
  have p43:=pivot2_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p43)*(1)

#print axioms pivot2_67

theorem pivot2_68 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 66=0 := by
  have h:=normalized_row2_67 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p33 - (1)*p35)*(((-1)*Y^2)/(Z))

#print axioms pivot2_68

theorem pivot2_69 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1)/(X^2*Y^2))*w 66 + (1)*w 71 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row2_68 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  have p53:=pivot2_53 X Y Z a hX hY hZ w hw
  have p63:=pivot2_63 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0 - (((-1))/(X^2*Z))*p35 - (1)*p53 - (1)*p63 - ((1)/(X^2*Y^2))*p68)*((-1))

#print axioms pivot2_69

theorem pivot2_70 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 55 + ((1)/(X^2*Y^2))*w 66 + ((-1))*w 69=0 := by
  have h:=normalized_row2_69 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  have p62:=pivot2_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0 - (((-1))/(X^2*Z))*p33 - (1)*p62)*(1)

#print axioms pivot2_70

theorem pivot2_71 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 58 + (((-1))/(Y^2))*w 66=0 := by
  have h:=normalized_row2_70 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3 - (((-1))/(Z))*p28 - (1)*p36)*(1)

#print axioms pivot2_71

theorem pivot2_72 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (((-1))/(Y^2))*w 66 + (1)*w 68=0 := by
  have h:=normalized_row2_71 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  have p29:=pivot2_29 X Y Z a hX hY hZ w hw
  have p41:=pivot2_41 X Y Z a hX hY hZ w hw
  have p61:=pivot2_61 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3 - (((-1))/(Z))*p29 - (1)*p41 - (1)*p61 - (((-1))/(Y^2))*p68)*((-1))

#print axioms pivot2_72

theorem pivot2_73 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + ((-1))*w 66 + (1)*w 74=0 := by
  have h:=normalized_row2_72 X Y Z a hX hY hZ w hw
  have p20:=pivot2_20 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p65:=pivot2_65 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p20 - (1)*p42 - (1)*p65 - ((-1))*p68)*((-1))

#print axioms pivot2_73

theorem pivot2_74 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*Y^2)/(Z))*w 21 + (((-1)*Y^2)/(X^2))*w 66 + (1)*w 69=0 := by
  have h:=normalized_row2_73 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p27:=pivot2_27 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  have p34:=pivot2_34 X Y Z a hX hY hZ w hw
  have p51:=pivot2_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p13 - (((-1)*X^2)/(Z))*p27 - ((-1))*p32 - (1)*p34 - (1)*p51)*((1*Y^2)/(X^2))

#print axioms pivot2_74

theorem pivot2_75 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 62 + ((-1))*w 64=0 := by
  have h:=normalized_row2_77 X Y Z a hX hY hZ w hw
  have p15:=pivot2_15 X Y Z a hX hY hZ w hw
  have p18:=pivot2_18 X Y Z a hX hY hZ w hw
  have p24:=pivot2_24 X Y Z a hX hY hZ w hw
  have p25:=pivot2_25 X Y Z a hX hY hZ w hw
  have p44:=pivot2_44 X Y Z a hX hY hZ w hw
  have p47:=pivot2_47 X Y Z a hX hY hZ w hw
  have p51:=pivot2_51 X Y Z a hX hY hZ w hw
  have p54:=pivot2_54 X Y Z a hX hY hZ w hw
  have p57:=pivot2_57 X Y Z a hX hY hZ w hw
  have p65:=pivot2_65 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p71:=pivot2_71 X Y Z a hX hY hZ w hw
  have p72:=pivot2_72 X Y Z a hX hY hZ w hw
  have p73:=pivot2_73 X Y Z a hX hY hZ w hw
  have p74:=pivot2_74 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p18 - (1)*p24 - (1)*p25 - (1)*p44 - (1)*p47 - (1)*p51 - (1)*p54 - (1)*p57 - (1)*p65 - ((1)/(Y^2))*p68 - ((-1))*p71 - (1)*p72 - ((-1))*p73 - ((1*X^2)/(Y^2))*p74)*((-1))

#print axioms pivot2_75

theorem pivot2_76 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z) + ((-2)*X^2)/(Z))*w 21 + (1)*w 64 + ((1)/(Y^2) + (1*Z)/(Y^2) + 1)*w 66=0 := by
  have h:=normalized_row2_76 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  have p4:=pivot2_4 X Y Z a hX hY hZ w hw
  have p8:=pivot2_8 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p41:=pivot2_41 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  have p61:=pivot2_61 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p72:=pivot2_72 X Y Z a hX hY hZ w hw
  have p73:=pivot2_73 X Y Z a hX hY hZ w hw
  have p75:=pivot2_75 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2))*p3 - (((-1))/(Y^2))*p4 - (((-1))/(Y^2))*p8 - (1)*p28 - (((-1))/(Y^2))*p36 - (1)*p38 - (((-1))/(Y^2))*p41 - (1)*p50 - (1)*p61 - (((-2))/(Y^2))*p68 - ((-1))*p72 - (1)*p73 - (1)*p75)*(1)

#print axioms pivot2_76

theorem pivot2_77 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Z)/(X^2*Y^2) + ((-1)*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66=0 := by
  have h:=normalized_row2_80 X Y Z a hX hY hZ w hw
  have p8:=pivot2_8 X Y Z a hX hY hZ w hw
  have p41:=pivot2_41 X Y Z a hX hY hZ w hw
  have p66:=pivot2_66 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p75:=pivot2_75 X Y Z a hX hY hZ w hw
  have p76:=pivot2_76 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8 - ((1)/(Y^2))*p41 - (1)*p66 - (((-1)*a)/(Y))*p68 - (1)*p75 - (1)*p76)*((1*Z)/(2*X^2))

#print axioms pivot2_77

theorem pivot2_78 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 61 + ((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row2_79 X Y Z a hX hY hZ w hw
  have p19:=pivot2_19 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  have p46:=pivot2_46 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p73:=pivot2_73 X Y Z a hX hY hZ w hw
  have p77:=pivot2_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p19 - (1)*p37 - (((-1)*a)/(Y))*p46 - (1)*p48 - ((1)/(X^2))*p68 - ((1*Y*a)/(X^2))*p73 - ((1)/(Y^2*Z) + ((-1)*Y*a)/(Z))*p77)*(1)

#print axioms pivot2_78

theorem pivot2_79 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 65 + ((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row2_81 X Y Z a hX hY hZ w hw
  have p2:=pivot2_2 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  have p62:=pivot2_62 X Y Z a hX hY hZ w hw
  have p67:=pivot2_67 X Y Z a hX hY hZ w hw
  have p74:=pivot2_74 X Y Z a hX hY hZ w hw
  have p77:=pivot2_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p2 - (1)*p26 - ((1*Y^2)/(X^2*Z))*p33 - (((-1)*a)/(Y))*p62 - (1)*p67 - ((1*a)/(Y))*p74 - ((1)/(Y^2*Z) + ((-1)*Y*a)/(Z))*p77)*(1)

#print axioms pivot2_79

theorem pivot2_80 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (1)*w 59 + (((-1))/(X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-2))/(X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66=0 := by
  have h:=normalized_row2_75 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p10:=pivot2_10 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p23:=pivot2_23 X Y Z a hX hY hZ w hw
  have p30:=pivot2_30 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  have p34:=pivot2_34 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p49:=pivot2_49 X Y Z a hX hY hZ w hw
  have p59:=pivot2_59 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p69:=pivot2_69 X Y Z a hX hY hZ w hw
  have p73:=pivot2_73 X Y Z a hX hY hZ w hw
  have p77:=pivot2_77 X Y Z a hX hY hZ w hw
  have p79:=pivot2_79 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2))*p0 - (((-1))/(X^2*Y^2))*p10 - (1)*p13 - (1)*p23 - (((-1))/(X^2*Y^2))*p30 - (((-1))/(X^2*Y^2))*p32 - (((-1))/(X^2*Y^2))*p34 - (((-1))/(X^2*Y^2))*p42 - (1)*p49 - (1)*p59 - ((1)/(X^2*Y^2))*p68 - (1)*p69 - ((1*Y^2)/(X^2))*p73 - (((-1))/(Y^2*Z) + ((-1)*Y^2)/(Z))*p77 - ((-1))*p79)*(1)

#print axioms pivot2_80

theorem pivot2_81 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-2))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-3)*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66 + (1)*w 73=0 := by
  have h:=normalized_row2_78 X Y Z a hX hY hZ w hw
  have p7:=pivot2_7 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  have p62:=pivot2_62 X Y Z a hX hY hZ w hw
  have p64:=pivot2_64 X Y Z a hX hY hZ w hw
  have p74:=pivot2_74 X Y Z a hX hY hZ w hw
  have p77:=pivot2_77 X Y Z a hX hY hZ w hw
  have p80:=pivot2_80 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p7 - (((-1)*a)/(Y))*p26 - (((-1)*Y*a)/(X^2*Z))*p33 - ((1)/(Y^2))*p62 - (1)*p64 - (((-1))/(Y^2))*p74 - ((1)/(Z))*p77 - (1)*p80)*((-1))

#print axioms pivot2_81

theorem pivot2_82 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (((-3))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-5)*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + ((-7))/(2*X^2) + (1*a^2)/(X^2) + ((-1)*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66 + (1)*w 67=0 := by
  have h:=normalized_row2_74 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p11:=pivot2_11 X Y Z a hX hY hZ w hw
  have p20:=pivot2_20 X Y Z a hX hY hZ w hw
  have p30:=pivot2_30 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  have p34:=pivot2_34 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p52:=pivot2_52 X Y Z a hX hY hZ w hw
  have p60:=pivot2_60 X Y Z a hX hY hZ w hw
  have p67:=pivot2_67 X Y Z a hX hY hZ w hw
  have p68:=pivot2_68 X Y Z a hX hY hZ w hw
  have p70:=pivot2_70 X Y Z a hX hY hZ w hw
  have p74:=pivot2_74 X Y Z a hX hY hZ w hw
  have p77:=pivot2_77 X Y Z a hX hY hZ w hw
  have p78:=pivot2_78 X Y Z a hX hY hZ w hw
  have p81:=pivot2_81 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2))*p0 - (((-1))/(X^2*Y^2))*p11 - (1)*p20 - (((-1))/(X^2*Y^2))*p30 - (((-1))/(X^2*Y^2))*p32 - (((-1))/(X^2*Y^2))*p34 - (((-1))/(X^2*Y^2))*p42 - (1)*p52 - (1)*p60 - (1)*p67 - ((1)/(X^2*Y^2))*p68 - ((-1))*p70 - ((-1))*p74 - ((1)/(Y^2*Z) + (1*Y^2)/(Z))*p77 - (1)*p78 - (1)*p81)*((-1))

#print axioms pivot2_82

end SmallLevelTwentyEightTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightTriangular
open Complex SmallLevelTwentyEightLaurent

theorem pivot3_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row3_5 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_0

theorem pivot3_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 82=0 := by
  have h:=normalized_row3_0 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(Y^2*Z))

#print axioms pivot3_1

theorem pivot3_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 81=0 := by
  have h:=normalized_row3_1 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X^2*Z))

#print axioms pivot3_2

theorem pivot3_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 42=0 := by
  have h:=normalized_row3_2 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*Y^2*Z)*p1)*(1)

#print axioms pivot3_3

theorem pivot3_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 78=0 := by
  have h:=normalized_row3_3 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(Z))

#print axioms pivot3_4

theorem pivot3_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row3_6 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot3_5

theorem pivot3_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row3_7 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Y^2*Z))*p3)*(1)

#print axioms pivot3_6

theorem pivot3_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row3_8 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0)*(1)

#print axioms pivot3_7

theorem pivot3_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row3_10 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3)*(1)

#print axioms pivot3_8

theorem pivot3_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 7=0 := by
  have h:=normalized_row3_20 X Y Z a hX hY hZ w hw
  have p8:=pivot3_8 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8)*((1*Z)/(X^2*Y^2))

#print axioms pivot3_9

theorem pivot3_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 48=0 := by
  have h:=normalized_row3_11 X Y Z a hX hY hZ w hw
  have p9:=pivot3_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p9)*(((-1)*X^2*Y^2)/(Z))

#print axioms pivot3_10

theorem pivot3_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row3_27 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p3)*(1)

#print axioms pivot3_11

theorem pivot3_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 77=0 := by
  have h:=normalized_row3_18 X Y Z a hX hY hZ w hw
  have p11:=pivot3_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p11)*(((-1)*Z)/(X^2*Y^2))

#print axioms pivot3_12

theorem pivot3_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 35=0 := by
  have h:=normalized_row3_26 X Y Z a hX hY hZ w hw
  have p11:=pivot3_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Z)/(X^2*Y^2))*p11)*(1)

#print axioms pivot3_13

theorem pivot3_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 39=0 := by
  have h:=normalized_row3_29 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot3_14

theorem pivot3_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 40=0 := by
  have h:=normalized_row3_30 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot3_15

theorem pivot3_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 41=0 := by
  have h:=normalized_row3_31 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot3_16

theorem pivot3_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 43=0 := by
  have h:=normalized_row3_32 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot3_17

theorem pivot3_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 44=0 := by
  have h:=normalized_row3_33 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2*Z))*p3)*(1)

#print axioms pivot3_18

theorem pivot3_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 45=0 := by
  have h:=normalized_row3_34 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Z))*p0)*(1)

#print axioms pivot3_19

theorem pivot3_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 49=0 := by
  have h:=normalized_row3_36 X Y Z a hX hY hZ w hw
  have p10:=pivot3_10 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Z)/(X^2*Y^2))*p10)*(1)

#print axioms pivot3_20

theorem pivot3_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 83=0 := by
  have h:=normalized_row3_40 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Y^2*Z))*p0)*(1)

#print axioms pivot3_21

theorem pivot3_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 53=0 := by
  have h:=normalized_row3_82 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_22

theorem pivot3_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 11=0 := by
  have h:=normalized_row3_50 X Y Z a hX hY hZ w hw
  have p22:=pivot3_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22)*(1)

#print axioms pivot3_23

theorem pivot3_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 80=0 := by
  have h:=normalized_row3_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2*Z))

#print axioms pivot3_24

theorem pivot3_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 4 + (((-1)*X^2)/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row3_9 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_25

theorem pivot3_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X^2*Z))*w 56=0 := by
  have h:=normalized_row3_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_26

theorem pivot3_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*Z)/(X^2))*w 12 + (1)*w 63=0 := by
  have h:=normalized_row3_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X^2))

#print axioms pivot3_27

theorem pivot3_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 14 + (((-1)*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row3_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_28

theorem pivot3_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*Z)/(Y^2))*w 18 + (1)*w 70=0 := by
  have h:=normalized_row3_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(Y^2))

#print axioms pivot3_29

theorem pivot3_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 72=0 := by
  have h:=normalized_row3_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X^2)/(Z))

#print axioms pivot3_30

theorem pivot3_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(X^2*Z))*w 28 + (1)*w 75=0 := by
  have h:=normalized_row3_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X^2*Z))

#print axioms pivot3_31

theorem pivot3_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 12 + ((1*X^2)/(Z))*w 21=0 := by
  have h:=normalized_row3_19 X Y Z a hX hY hZ w hw
  have p24:=pivot3_24 X Y Z a hX hY hZ w hw
  have p27:=pivot3_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2*Z)/(X^2))*p24 - (1)*p27)*((1*X^2)/(Z))

#print axioms pivot3_32

theorem pivot3_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 56 + ((1*Z)/(Y^2))*w 66=0 := by
  have h:=normalized_row3_21 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2*Z)/(Y^2))*p26 - (1)*p28)*(1)

#print axioms pivot3_33

theorem pivot3_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 24 + (1)*w 66=0 := by
  have h:=normalized_row3_22 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(Z))*p28)*(1)

#print axioms pivot3_34

theorem pivot3_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*Z)/(Y^2))*w 18 + (1)*w 28=0 := by
  have h:=normalized_row3_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_35

theorem pivot3_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + (1)*w 30=0 := by
  have h:=normalized_row3_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_36

theorem pivot3_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1))/(X^2))*w 18 + (1)*w 33=0 := by
  have h:=normalized_row3_25 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X^2*Z))*p35)*(1)

#print axioms pivot3_37

theorem pivot3_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Y^2*Z))*w 21 + (1)*w 38=0 := by
  have h:=normalized_row3_28 X Y Z a hX hY hZ w hw
  have p27:=pivot3_27 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Y^2*Z))*p27 - ((1)/(Y^2))*p32)*(1)

#print axioms pivot3_38

theorem pivot3_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z))*w 21 + (1)*w 46=0 := by
  have h:=normalized_row3_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_39

theorem pivot3_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 51 + (((-1))/(X^2))*w 66=0 := by
  have h:=normalized_row3_37 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X^2*Z))*p33)*(1)

#print axioms pivot3_40

theorem pivot3_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 54=0 := by
  have h:=normalized_row3_38 X Y Z a hX hY hZ w hw
  have p27:=pivot3_27 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X^2)/(Z))*p27 - (1)*p32)*(1)

#print axioms pivot3_41

theorem pivot3_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 60=0 := by
  have h:=normalized_row3_39 X Y Z a hX hY hZ w hw
  have p29:=pivot3_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(Z))*p29)*(1)

#print axioms pivot3_42

theorem pivot3_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 79=0 := by
  have h:=normalized_row3_41 X Y Z a hX hY hZ w hw
  have p41:=pivot3_41 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p41)*((1)/(X^2*Y^2))

#print axioms pivot3_43

theorem pivot3_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 8 + (((-1))/(Y^2))*w 18=0 := by
  have h:=normalized_row3_42 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p42)*((1)/(Y^2))

#print axioms pivot3_44

theorem pivot3_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 10 + ((1*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row3_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X^2)/(Y^2))

#print axioms pivot3_45

theorem pivot3_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row3_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X^2))

#print axioms pivot3_46

theorem pivot3_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 66 + (1)*w 76=0 := by
  have h:=normalized_row3_45 X Y Z a hX hY hZ w hw
  have p34:=pivot3_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p34)*(1)

#print axioms pivot3_47

theorem pivot3_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 5 + (((-1))/(Y^2*Z))*w 21=0 := by
  have h:=normalized_row3_46 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p36)*(1)

#print axioms pivot3_48

theorem pivot3_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1)/(Y^2*Z))*w 21 + (1)*w 47=0 := by
  have h:=normalized_row3_47 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p48)*(1)

#print axioms pivot3_49

theorem pivot3_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1)/(Y^2))*w 18 + (1)*w 50=0 := by
  have h:=normalized_row3_48 X Y Z a hX hY hZ w hw
  have p44:=pivot3_44 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p44)*(1)

#print axioms pivot3_50

theorem pivot3_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 52 + (((-1)*X^2)/(Y^2))*w 69=0 := by
  have h:=normalized_row3_49 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p45)*(1)

#print axioms pivot3_51

theorem pivot3_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 13 + (1)*w 55=0 := by
  have h:=normalized_row3_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_52

theorem pivot3_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 57 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row3_52 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p46)*(1)

#print axioms pivot3_53

theorem pivot3_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 58=0 := by
  have h:=normalized_row3_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_54

theorem pivot3_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 59=0 := by
  have h:=normalized_row3_54 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_55

theorem pivot3_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 19 + (1)*w 61=0 := by
  have h:=normalized_row3_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_56

theorem pivot3_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 20 + (1)*w 62=0 := by
  have h:=normalized_row3_56 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_57

theorem pivot3_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 22 + (1)*w 64=0 := by
  have h:=normalized_row3_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_58

theorem pivot3_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 23 + (1)*w 65=0 := by
  have h:=normalized_row3_58 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_59

theorem pivot3_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 25 + (1)*w 67=0 := by
  have h:=normalized_row3_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_60

theorem pivot3_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 26 + (1)*w 68=0 := by
  have h:=normalized_row3_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_61

theorem pivot3_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 27 + (1)*w 69=0 := by
  have h:=normalized_row3_61 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_62

theorem pivot3_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 29 + (1)*w 71=0 := by
  have h:=normalized_row3_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_63

theorem pivot3_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 31 + (1)*w 73=0 := by
  have h:=normalized_row3_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_64

theorem pivot3_65 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 32 + (1)*w 74=0 := by
  have h:=normalized_row3_64 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_65

theorem pivot3_66 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 34 + ((1)/(Y^2))*w 66=0 := by
  have h:=normalized_row3_65 X Y Z a hX hY hZ w hw
  have p47:=pivot3_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p47)*(1)

#print axioms pivot3_66

theorem pivot3_67 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1))/(Y^2*Z))*w 21 + (1)*w 37=0 := by
  have h:=normalized_row3_66 X Y Z a hX hY hZ w hw
  have p43:=pivot3_43 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p43)*(1)

#print axioms pivot3_67

theorem pivot3_68 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 66=0 := by
  have h:=normalized_row3_67 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p33 - (1)*p35)*(((-1)*Y^2)/(Z))

#print axioms pivot3_68

theorem pivot3_69 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1)/(X^2*Y^2))*w 66 + (1)*w 71 + (((-1)*Y^2)/(X^2))*w 74=0 := by
  have h:=normalized_row3_68 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  have p53:=pivot3_53 X Y Z a hX hY hZ w hw
  have p63:=pivot3_63 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0 - (((-1))/(X^2*Z))*p35 - (1)*p53 - (1)*p63 - ((1)/(X^2*Y^2))*p68)*((-1))

#print axioms pivot3_69

theorem pivot3_70 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 55 + ((1)/(X^2*Y^2))*w 66 + ((-1))*w 69=0 := by
  have h:=normalized_row3_69 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  have p62:=pivot3_62 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X^2*Z))*p0 - (((-1))/(X^2*Z))*p33 - (1)*p62)*(1)

#print axioms pivot3_70

theorem pivot3_71 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (1)*w 58 + (((-1))/(Y^2))*w 66=0 := by
  have h:=normalized_row3_70 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3 - (((-1))/(Z))*p28 - (1)*p36)*(1)

#print axioms pivot3_71

theorem pivot3_72 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1)*X^2)/(Z))*w 21 + (((-1))/(Y^2))*w 66 + (1)*w 68=0 := by
  have h:=normalized_row3_71 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  have p29:=pivot3_29 X Y Z a hX hY hZ w hw
  have p41:=pivot3_41 X Y Z a hX hY hZ w hw
  have p61:=pivot3_61 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p3 - (((-1))/(Z))*p29 - (1)*p41 - (1)*p61 - (((-1))/(Y^2))*p68)*((-1))

#print axioms pivot3_72

theorem pivot3_73 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*X^2)/(Z))*w 21 + ((-1))*w 66 + (1)*w 74=0 := by
  have h:=normalized_row3_72 X Y Z a hX hY hZ w hw
  have p20:=pivot3_20 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p65:=pivot3_65 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p20 - (1)*p42 - (1)*p65 - ((-1))*p68)*((-1))

#print axioms pivot3_73

theorem pivot3_74 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*Y^2)/(Z))*w 21 + (((-1)*Y^2)/(X^2))*w 66 + (1)*w 69=0 := by
  have h:=normalized_row3_73 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p27:=pivot3_27 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  have p34:=pivot3_34 X Y Z a hX hY hZ w hw
  have p51:=pivot3_51 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X^2)/(Z))*p13 - (((-1)*X^2)/(Z))*p27 - ((-1))*p32 - (1)*p34 - (1)*p51)*((1*Y^2)/(X^2))

#print axioms pivot3_74

theorem pivot3_75 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 62 + ((-1))*w 64=0 := by
  have h:=normalized_row3_77 X Y Z a hX hY hZ w hw
  have p15:=pivot3_15 X Y Z a hX hY hZ w hw
  have p18:=pivot3_18 X Y Z a hX hY hZ w hw
  have p24:=pivot3_24 X Y Z a hX hY hZ w hw
  have p25:=pivot3_25 X Y Z a hX hY hZ w hw
  have p44:=pivot3_44 X Y Z a hX hY hZ w hw
  have p47:=pivot3_47 X Y Z a hX hY hZ w hw
  have p51:=pivot3_51 X Y Z a hX hY hZ w hw
  have p54:=pivot3_54 X Y Z a hX hY hZ w hw
  have p57:=pivot3_57 X Y Z a hX hY hZ w hw
  have p65:=pivot3_65 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  have p71:=pivot3_71 X Y Z a hX hY hZ w hw
  have p72:=pivot3_72 X Y Z a hX hY hZ w hw
  have p73:=pivot3_73 X Y Z a hX hY hZ w hw
  have p74:=pivot3_74 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p18 - (1)*p24 - (1)*p25 - (1)*p44 - (1)*p47 - (1)*p51 - (1)*p54 - (1)*p57 - (1)*p65 - ((1)/(Y^2))*p68 - ((-1))*p71 - (1)*p72 - ((-1))*p73 - ((1*X^2)/(Y^2))*p74)*((-1))

#print axioms pivot3_75

theorem pivot3_76 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ((1*X^2)/(Y^2*Z) + ((-2)*X^2)/(Z))*w 21 + (1)*w 64 + (((-1))/(Y^2) + (1*Z)/(Y^2) + 1)*w 66=0 := by
  have h:=normalized_row3_76 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  have p4:=pivot3_4 X Y Z a hX hY hZ w hw
  have p8:=pivot3_8 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p41:=pivot3_41 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  have p61:=pivot3_61 X Y Z a hX hY hZ w hw
  have p72:=pivot3_72 X Y Z a hX hY hZ w hw
  have p73:=pivot3_73 X Y Z a hX hY hZ w hw
  have p75:=pivot3_75 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p3 - ((1)/(Y^2))*p4 - ((1)/(Y^2))*p8 - (1)*p28 - ((1)/(Y^2))*p36 - (1)*p38 - ((1)/(Y^2))*p41 - (1)*p50 - (1)*p61 - ((-1))*p72 - (1)*p73 - (1)*p75)*(1)

#print axioms pivot3_76

theorem pivot3_77 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66=0 := by
  have h:=normalized_row3_80 X Y Z a hX hY hZ w hw
  have p8:=pivot3_8 X Y Z a hX hY hZ w hw
  have p41:=pivot3_41 X Y Z a hX hY hZ w hw
  have p66:=pivot3_66 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  have p75:=pivot3_75 X Y Z a hX hY hZ w hw
  have p76:=pivot3_76 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p8 - ((1)/(Y^2))*p41 - (1)*p66 - (((-1)*a)/(Y))*p68 - (1)*p75 - (1)*p76)*((1*Z)/(2*X^2))

#print axioms pivot3_77

theorem pivot3_78 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 61 + ((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row3_79 X Y Z a hX hY hZ w hw
  have p19:=pivot3_19 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  have p73:=pivot3_73 X Y Z a hX hY hZ w hw
  have p77:=pivot3_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p19 - (1)*p37 - (((-1)*a)/(Y))*p46 - (1)*p48 - ((1)/(X^2))*p68 - ((1*Y*a)/(X^2))*p73 - ((1)/(Y^2*Z) + ((-1)*Y*a)/(Z))*p77)*(1)

#print axioms pivot3_78

theorem pivot3_79 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 65 + ((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66=0 := by
  have h:=normalized_row3_81 X Y Z a hX hY hZ w hw
  have p2:=pivot3_2 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  have p62:=pivot3_62 X Y Z a hX hY hZ w hw
  have p67:=pivot3_67 X Y Z a hX hY hZ w hw
  have p74:=pivot3_74 X Y Z a hX hY hZ w hw
  have p77:=pivot3_77 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p2 - (1)*p26 - ((1*Y^2)/(X^2*Z))*p33 - (((-1)*a)/(Y))*p62 - (1)*p67 - ((1*a)/(Y))*p74 - ((1)/(Y^2*Z) + ((-1)*Y*a)/(Z))*p77)*(1)

#print axioms pivot3_79

theorem pivot3_80 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (1)*w 59 + (((-1))/(X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66=0 := by
  have h:=normalized_row3_75 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p10:=pivot3_10 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p23:=pivot3_23 X Y Z a hX hY hZ w hw
  have p30:=pivot3_30 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  have p34:=pivot3_34 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p49:=pivot3_49 X Y Z a hX hY hZ w hw
  have p59:=pivot3_59 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  have p69:=pivot3_69 X Y Z a hX hY hZ w hw
  have p73:=pivot3_73 X Y Z a hX hY hZ w hw
  have p77:=pivot3_77 X Y Z a hX hY hZ w hw
  have p79:=pivot3_79 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p0 - ((1)/(X^2*Y^2))*p10 - (1)*p13 - (1)*p23 - ((1)/(X^2*Y^2))*p30 - ((1)/(X^2*Y^2))*p32 - ((1)/(X^2*Y^2))*p34 - ((1)/(X^2*Y^2))*p42 - (1)*p49 - (1)*p59 - (((-1))/(X^2*Y^2))*p68 - (1)*p69 - ((1*Y^2)/(X^2))*p73 - (((-1))/(Y^2*Z) + ((-1)*Y^2)/(Z))*p77 - ((-1))*p79)*(1)

#print axioms pivot3_80

theorem pivot3_81 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(2*X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66 + (1)*w 73=0 := by
  have h:=normalized_row3_78 X Y Z a hX hY hZ w hw
  have p7:=pivot3_7 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  have p62:=pivot3_62 X Y Z a hX hY hZ w hw
  have p64:=pivot3_64 X Y Z a hX hY hZ w hw
  have p74:=pivot3_74 X Y Z a hX hY hZ w hw
  have p77:=pivot3_77 X Y Z a hX hY hZ w hw
  have p80:=pivot3_80 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p7 - (((-1)*a)/(Y))*p26 - (((-1)*Y*a)/(X^2*Z))*p33 - ((1)/(Y^2))*p62 - (1)*p64 - (((-1))/(Y^2))*p74 - ((1)/(Z))*p77 - (1)*p80)*((-1))

#print axioms pivot3_81

theorem pivot3_82 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (((-2))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(X^2) + ((-1)*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66 + (1)*w 67=0 := by
  have h:=normalized_row3_74 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p11:=pivot3_11 X Y Z a hX hY hZ w hw
  have p20:=pivot3_20 X Y Z a hX hY hZ w hw
  have p30:=pivot3_30 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  have p34:=pivot3_34 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p52:=pivot3_52 X Y Z a hX hY hZ w hw
  have p60:=pivot3_60 X Y Z a hX hY hZ w hw
  have p67:=pivot3_67 X Y Z a hX hY hZ w hw
  have p68:=pivot3_68 X Y Z a hX hY hZ w hw
  have p70:=pivot3_70 X Y Z a hX hY hZ w hw
  have p74:=pivot3_74 X Y Z a hX hY hZ w hw
  have p77:=pivot3_77 X Y Z a hX hY hZ w hw
  have p78:=pivot3_78 X Y Z a hX hY hZ w hw
  have p81:=pivot3_81 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X^2*Y^2))*p0 - ((1)/(X^2*Y^2))*p11 - (1)*p20 - ((1)/(X^2*Y^2))*p30 - ((1)/(X^2*Y^2))*p32 - ((1)/(X^2*Y^2))*p34 - ((1)/(X^2*Y^2))*p42 - (1)*p52 - (1)*p60 - (1)*p67 - (((-1))/(X^2*Y^2))*p68 - ((-1))*p70 - ((-1))*p74 - ((1)/(Y^2*Z) + (1*Y^2)/(Z))*p77 - (1)*p78 - (1)*p81)*((-1))

#print axioms pivot3_82

end SmallLevelTwentyEightTriangular
end
end
end

/-! ## SmallLevelTwentyEightTriangularKernelCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightTriangular
open Complex SmallLevelTwentyEightLaurent

theorem kernel_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole0 X Y Z a j*w 66 := by
  have z67 : w 67=pole0 X Y Z a 67*w 66 := by
    have h:=pivot0_82 X Y Z a hX hY hZ w hw
    change w 67=((2)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(X^2) + ((-1)*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z73 : w 73=pole0 X Y Z a 73*w 66 := by
    have h:=pivot0_81 X Y Z a hX hY hZ w hw
    change w 73=((1)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(2*X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z59 : w 59=pole0 X Y Z a 59*w 66 := by
    have h:=pivot0_80 X Y Z a hX hY hZ w hw
    change w 59=((1)/(X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole0 X Y Z a 65*w 66 := by
    have h:=pivot0_79 X Y Z a hX hY hZ w hw
    change w 65=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z61 : w 61=pole0 X Y Z a 61*w 66 := by
    have h:=pivot0_78 X Y Z a hX hY hZ w hw
    change w 61=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole0 X Y Z a 21*w 66 := by
    have h:=pivot0_77 X Y Z a hX hY hZ w hw
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole0 X Y Z a 64*w 66 := by
    have h:=pivot0_76 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 64=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z) + (2*X^2)/(Z))*v21
  have z62 : w 62=pole0 X Y Z a 62*w 66 := by
    have h:=pivot0_75 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 62=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v64
  have z69 : w 69=pole0 X Y Z a 69*w 66 := by
    have h:=pivot0_74 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 69=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(Z))*v21
  have z74 : w 74=pole0 X Y Z a 74*w 66 := by
    have h:=pivot0_73 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 74=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z68 : w 68=pole0 X Y Z a 68*w 66 := by
    have h:=pivot0_72 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 68=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z58 : w 58=pole0 X Y Z a 58*w 66 := by
    have h:=pivot0_71 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 58=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z55 : w 55=pole0 X Y Z a 55*w 66 := by
    have h:=pivot0_70 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 55=(((-1))/(X^2*Y^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v69
  have z71 : w 71=pole0 X Y Z a 71*w 66 := by
    have h:=pivot0_69 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 71=(((-1))/(X^2*Y^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z18 : w 18=pole0 X Y Z a 18*w 66 := by
    have h:=pivot0_68 X Y Z a hX hY hZ w hw
    change w 18=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z37 : w 37=pole0 X Y Z a 37*w 66 := by
    have h:=pivot0_67 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 37=(((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z34 : w 34=pole0 X Y Z a 34*w 66 := by
    have h:=pivot0_66 X Y Z a hX hY hZ w hw
    change w 34=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole0 X Y Z a 32*w 66 := by
    have h:=pivot0_65 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 32=(((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v74
  have z31 : w 31=pole0 X Y Z a 31*w 66 := by
    have h:=pivot0_64 X Y Z a hX hY hZ w hw
    have v73:=z73
    change w 73=((1)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(2*X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v73
    change w 31=(((-1))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(2*X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v73
  have z29 : w 29=pole0 X Y Z a 29*w 66 := by
    have h:=pivot0_63 X Y Z a hX hY hZ w hw
    have v71:=z71
    change w 71=(((-1))/(X^2*Y^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v71
    change w 29=((1)/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v71
  have z27 : w 27=pole0 X Y Z a 27*w 66 := by
    have h:=pivot0_62 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 27=(((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v69
  have z26 : w 26=pole0 X Y Z a 26*w 66 := by
    have h:=pivot0_61 X Y Z a hX hY hZ w hw
    have v68:=z68
    change w 68=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v68
    change w 26=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v68
  have z25 : w 25=pole0 X Y Z a 25*w 66 := by
    have h:=pivot0_60 X Y Z a hX hY hZ w hw
    have v67:=z67
    change w 67=((2)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(X^2) + ((-1)*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66 at v67
    change w 25=(((-2))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(X^2) + (1*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v67
  have z23 : w 23=pole0 X Y Z a 23*w 66 := by
    have h:=pivot0_59 X Y Z a hX hY hZ w hw
    have v65:=z65
    change w 65=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v65
    change w 23=(((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v65
  have z22 : w 22=pole0 X Y Z a 22*w 66 := by
    have h:=pivot0_58 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 22=(((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v64
  have z20 : w 20=pole0 X Y Z a 20*w 66 := by
    have h:=pivot0_57 X Y Z a hX hY hZ w hw
    have v62:=z62
    change w 62=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v62
    change w 20=(((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v62
  have z19 : w 19=pole0 X Y Z a 19*w 66 := by
    have h:=pivot0_56 X Y Z a hX hY hZ w hw
    have v61:=z61
    change w 61=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v61
    change w 19=(((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v61
  have z17 : w 17=pole0 X Y Z a 17*w 66 := by
    have h:=pivot0_55 X Y Z a hX hY hZ w hw
    have v59:=z59
    change w 59=((1)/(X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v59
    change w 17=(((-1))/(X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v59
  have z16 : w 16=pole0 X Y Z a 16*w 66 := by
    have h:=pivot0_54 X Y Z a hX hY hZ w hw
    have v58:=z58
    change w 58=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v58
    change w 16=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v58
  have z57 : w 57=pole0 X Y Z a 57*w 66 := by
    have h:=pivot0_53 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 57=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z13 : w 13=pole0 X Y Z a 13*w 66 := by
    have h:=pivot0_52 X Y Z a hX hY hZ w hw
    have v55:=z55
    change w 55=(((-1))/(X^2*Y^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v55
    change w 13=((1)/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v55
  have z52 : w 52=pole0 X Y Z a 52*w 66 := by
    have h:=pivot0_51 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 52=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2))*v69
  have z50 : w 50=pole0 X Y Z a 50*w 66 := by
    have h:=pivot0_50 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 50=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2))*v18
  have z47 : w 47=pole0 X Y Z a 47*w 66 := by
    have h:=pivot0_49 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 47=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z5 : w 5=pole0 X Y Z a 5*w 66 := by
    have h:=pivot0_48 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 5=(((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z76 : w 76=pole0 X Y Z a 76*w 66 := by
    have h:=pivot0_47 X Y Z a hX hY hZ w hw
    change w 76=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z15 : w 15=pole0 X Y Z a 15*w 66 := by
    have h:=pivot0_46 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 15=(((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2))*v74
  have z10 : w 10=pole0 X Y Z a 10*w 66 := by
    have h:=pivot0_45 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=((1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 10=(((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2))*v69
  have z8 : w 8=pole0 X Y Z a 8*w 66 := by
    have h:=pivot0_44 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 8=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v18
  have z79 : w 79=pole0 X Y Z a 79*w 66 := by
    have h:=pivot0_43 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 79=((1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z60 : w 60=pole0 X Y Z a 60*w 66 := by
    have h:=pivot0_42 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 60=(1)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v18
  have z54 : w 54=pole0 X Y Z a 54*w 66 := by
    have h:=pivot0_41 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 54=(((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z51 : w 51=pole0 X Y Z a 51*w 66 := by
    have h:=pivot0_40 X Y Z a hX hY hZ w hw
    change w 51=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole0 X Y Z a 46*w 66 := by
    have h:=pivot0_39 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 46=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z38 : w 38=pole0 X Y Z a 38*w 66 := by
    have h:=pivot0_38 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 38=(((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z33 : w 33=pole0 X Y Z a 33*w 66 := by
    have h:=pivot0_37 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 33=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X^2))*v18
  have z30 : w 30=pole0 X Y Z a 30*w 66 := by
    have h:=pivot0_36 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 30=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z28 : w 28=pole0 X Y Z a 28*w 66 := by
    have h:=pivot0_35 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 28=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v18
  have z24 : w 24=pole0 X Y Z a 24*w 66 := by
    have h:=pivot0_34 X Y Z a hX hY hZ w hw
    change w 24=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole0 X Y Z a 56*w 66 := by
    have h:=pivot0_33 X Y Z a hX hY hZ w hw
    change w 56=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole0 X Y Z a 12*w 66 := by
    have h:=pivot0_32 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 12=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z75 : w 75=pole0 X Y Z a 75*w 66 := by
    have h:=pivot0_31 X Y Z a hX hY hZ w hw
    have v28:=z28
    change w 28=(((-1)*Z)/(Y^2))*w 66 at v28
    change w 75=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2*Z))*v28
  have z72 : w 72=pole0 X Y Z a 72*w 66 := by
    have h:=pivot0_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 72=(((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z70 : w 70=pole0 X Y Z a 70*w 66 := by
    have h:=pivot0_29 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 70=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v18
  have z14 : w 14=pole0 X Y Z a 14*w 66 := by
    have h:=pivot0_28 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole0 X Y Z a 63*w 66 := by
    have h:=pivot0_27 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66 at v12
    change w 63=(((-1)*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X^2))*v12
  have z9 : w 9=pole0 X Y Z a 9*w 66 := by
    have h:=pivot0_26 X Y Z a hX hY hZ w hw
    have v56:=z56
    change w 56=((1*Z)/(Y^2))*w 66 at v56
    change w 9=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2*Z))*v56
  have z4 : w 4=pole0 X Y Z a 4*w 66 := by
    have h:=pivot0_25 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 4=(((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z80 : w 80=pole0 X Y Z a 80*w 66 := by
    have h:=pivot0_24 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 80=((1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z11 : w 11=pole0 X Y Z a 11*w 66 := by
    have h:=pivot0_23 X Y Z a hX hY hZ w hw
    change w 11=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z53 : w 53=pole0 X Y Z a 53*w 66 := by
    have h:=pivot0_22 X Y Z a hX hY hZ w hw
    change w 53=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z83 : w 83=pole0 X Y Z a 83*w 66 := by
    have h:=pivot0_21 X Y Z a hX hY hZ w hw
    change w 83=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole0 X Y Z a 49*w 66 := by
    have h:=pivot0_20 X Y Z a hX hY hZ w hw
    change w 49=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole0 X Y Z a 45*w 66 := by
    have h:=pivot0_19 X Y Z a hX hY hZ w hw
    change w 45=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z44 : w 44=pole0 X Y Z a 44*w 66 := by
    have h:=pivot0_18 X Y Z a hX hY hZ w hw
    change w 44=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole0 X Y Z a 43*w 66 := by
    have h:=pivot0_17 X Y Z a hX hY hZ w hw
    change w 43=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole0 X Y Z a 41*w 66 := by
    have h:=pivot0_16 X Y Z a hX hY hZ w hw
    change w 41=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole0 X Y Z a 40*w 66 := by
    have h:=pivot0_15 X Y Z a hX hY hZ w hw
    change w 40=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z39 : w 39=pole0 X Y Z a 39*w 66 := by
    have h:=pivot0_14 X Y Z a hX hY hZ w hw
    change w 39=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z35 : w 35=pole0 X Y Z a 35*w 66 := by
    have h:=pivot0_13 X Y Z a hX hY hZ w hw
    change w 35=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z77 : w 77=pole0 X Y Z a 77*w 66 := by
    have h:=pivot0_12 X Y Z a hX hY hZ w hw
    change w 77=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole0 X Y Z a 36*w 66 := by
    have h:=pivot0_11 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole0 X Y Z a 48*w 66 := by
    have h:=pivot0_10 X Y Z a hX hY hZ w hw
    change w 48=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z7 : w 7=pole0 X Y Z a 7*w 66 := by
    have h:=pivot0_9 X Y Z a hX hY hZ w hw
    change w 7=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole0 X Y Z a 6*w 66 := by
    have h:=pivot0_8 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole0 X Y Z a 3*w 66 := by
    have h:=pivot0_7 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole0 X Y Z a 2*w 66 := by
    have h:=pivot0_6 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole0 X Y Z a 1*w 66 := by
    have h:=pivot0_5 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z78 : w 78=pole0 X Y Z a 78*w 66 := by
    have h:=pivot0_4 X Y Z a hX hY hZ w hw
    change w 78=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z42 : w 42=pole0 X Y Z a 42*w 66 := by
    have h:=pivot0_3 X Y Z a hX hY hZ w hw
    change w 42=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z81 : w 81=pole0 X Y Z a 81*w 66 := by
    have h:=pivot0_2 X Y Z a hX hY hZ w hw
    change w 81=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z82 : w 82=pole0 X Y Z a 82*w 66 := by
    have h:=pivot0_1 X Y Z a hX hY hZ w hw
    change w 82=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole0 X Y Z a 0*w 66 := by
    have h:=pivot0_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  intro j
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
  · change w 66=1*w 66
    exact (one_mul _).symm
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

#print axioms kernel_case0

theorem kernel_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole1 X Y Z a j*w 66 := by
  have z67 : w 67=pole1 X Y Z a 67*w 66 := by
    have h:=pivot1_82 X Y Z a hX hY hZ w hw
    change w 67=((3)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (5*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + (7)/(2*X^2) + ((-1)*a^2)/(X^2) + ((-1)*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z73 : w 73=pole1 X Y Z a 73*w 66 := by
    have h:=pivot1_81 X Y Z a hX hY hZ w hw
    change w 73=((2)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (3*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z59 : w 59=pole1 X Y Z a 59*w 66 := by
    have h:=pivot1_80 X Y Z a hX hY hZ w hw
    change w 59=((1)/(X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (2)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole1 X Y Z a 65*w 66 := by
    have h:=pivot1_79 X Y Z a hX hY hZ w hw
    change w 65=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z61 : w 61=pole1 X Y Z a 61*w 66 := by
    have h:=pivot1_78 X Y Z a hX hY hZ w hw
    change w 61=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole1 X Y Z a 21*w 66 := by
    have h:=pivot1_77 X Y Z a hX hY hZ w hw
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole1 X Y Z a 64*w 66 := by
    have h:=pivot1_76 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 64=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z) + (2*X^2)/(Z))*v21
  have z62 : w 62=pole1 X Y Z a 62*w 66 := by
    have h:=pivot1_75 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 62=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v64
  have z69 : w 69=pole1 X Y Z a 69*w 66 := by
    have h:=pivot1_74 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 69=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(Z))*v21
  have z74 : w 74=pole1 X Y Z a 74*w 66 := by
    have h:=pivot1_73 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 74=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z68 : w 68=pole1 X Y Z a 68*w 66 := by
    have h:=pivot1_72 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 68=((2)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z58 : w 58=pole1 X Y Z a 58*w 66 := by
    have h:=pivot1_71 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 58=((2)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z55 : w 55=pole1 X Y Z a 55*w 66 := by
    have h:=pivot1_70 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 55=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v69
  have z71 : w 71=pole1 X Y Z a 71*w 66 := by
    have h:=pivot1_69 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 71=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z18 : w 18=pole1 X Y Z a 18*w 66 := by
    have h:=pivot1_68 X Y Z a hX hY hZ w hw
    change w 18=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z37 : w 37=pole1 X Y Z a 37*w 66 := by
    have h:=pivot1_67 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 37=((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z34 : w 34=pole1 X Y Z a 34*w 66 := by
    have h:=pivot1_66 X Y Z a hX hY hZ w hw
    change w 34=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole1 X Y Z a 32*w 66 := by
    have h:=pivot1_65 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 32=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v74
  have z31 : w 31=pole1 X Y Z a 31*w 66 := by
    have h:=pivot1_64 X Y Z a hX hY hZ w hw
    have v73:=z73
    change w 73=((2)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (3*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v73
    change w 31=(((-2))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-3)*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v73
  have z29 : w 29=pole1 X Y Z a 29*w 66 := by
    have h:=pivot1_63 X Y Z a hX hY hZ w hw
    have v71:=z71
    change w 71=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v71
    change w 29=((1)/(X^2*Y^2) + (1)/(X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v71
  have z27 : w 27=pole1 X Y Z a 27*w 66 := by
    have h:=pivot1_62 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 27=((1)/(X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v69
  have z26 : w 26=pole1 X Y Z a 26*w 66 := by
    have h:=pivot1_61 X Y Z a hX hY hZ w hw
    have v68:=z68
    change w 68=((2)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v68
    change w 26=(((-2))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v68
  have z25 : w 25=pole1 X Y Z a 25*w 66 := by
    have h:=pivot1_60 X Y Z a hX hY hZ w hw
    have v67:=z67
    change w 67=((3)/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + (5*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + (7)/(2*X^2) + ((-1)*a^2)/(X^2) + ((-1)*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66 at v67
    change w 25=(((-3))/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + ((-5)*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + ((-7))/(2*X^2) + (1*a^2)/(X^2) + (1*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v67
  have z23 : w 23=pole1 X Y Z a 23*w 66 := by
    have h:=pivot1_59 X Y Z a hX hY hZ w hw
    have v65:=z65
    change w 65=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v65
    change w 23=((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v65
  have z22 : w 22=pole1 X Y Z a 22*w 66 := by
    have h:=pivot1_58 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 22=((1)/(Y^4) + ((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v64
  have z20 : w 20=pole1 X Y Z a 20*w 66 := by
    have h:=pivot1_57 X Y Z a hX hY hZ w hw
    have v62:=z62
    change w 62=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v62
    change w 20=((1)/(Y^4) + ((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v62
  have z19 : w 19=pole1 X Y Z a 19*w 66 := by
    have h:=pivot1_56 X Y Z a hX hY hZ w hw
    have v61:=z61
    change w 61=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v61
    change w 19=((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v61
  have z17 : w 17=pole1 X Y Z a 17*w 66 := by
    have h:=pivot1_55 X Y Z a hX hY hZ w hw
    have v59:=z59
    change w 59=((1)/(X^2*Y^2) + (1*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + (2)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v59
    change w 17=(((-1))/(X^2*Y^2) + ((-1)*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + ((-2))/(X^2) + (1*a^2)/(2*X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v59
  have z16 : w 16=pole1 X Y Z a 16*w 66 := by
    have h:=pivot1_54 X Y Z a hX hY hZ w hw
    have v58:=z58
    change w 58=((2)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v58
    change w 16=(((-2))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v58
  have z57 : w 57=pole1 X Y Z a 57*w 66 := by
    have h:=pivot1_53 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 57=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z13 : w 13=pole1 X Y Z a 13*w 66 := by
    have h:=pivot1_52 X Y Z a hX hY hZ w hw
    have v55:=z55
    change w 55=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v55
    change w 13=((1)/(X^2*Y^2) + (1)/(X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v55
  have z52 : w 52=pole1 X Y Z a 52*w 66 := by
    have h:=pivot1_51 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 52=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2))*v69
  have z50 : w 50=pole1 X Y Z a 50*w 66 := by
    have h:=pivot1_50 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 50=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2))*v18
  have z47 : w 47=pole1 X Y Z a 47*w 66 := by
    have h:=pivot1_49 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 47=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z5 : w 5=pole1 X Y Z a 5*w 66 := by
    have h:=pivot1_48 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 5=((1)/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z76 : w 76=pole1 X Y Z a 76*w 66 := by
    have h:=pivot1_47 X Y Z a hX hY hZ w hw
    change w 76=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z15 : w 15=pole1 X Y Z a 15*w 66 := by
    have h:=pivot1_46 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 15=((1)/(X^2) + ((-1)*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2))*v74
  have z10 : w 10=pole1 X Y Z a 10*w 66 := by
    have h:=pivot1_45 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + (1*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 10=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2))*v69
  have z8 : w 8=pole1 X Y Z a 8*w 66 := by
    have h:=pivot1_44 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 8=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v18
  have z79 : w 79=pole1 X Y Z a 79*w 66 := by
    have h:=pivot1_43 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 79=(((-1))/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z60 : w 60=pole1 X Y Z a 60*w 66 := by
    have h:=pivot1_42 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 60=(1)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v18
  have z54 : w 54=pole1 X Y Z a 54*w 66 := by
    have h:=pivot1_41 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 54=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z51 : w 51=pole1 X Y Z a 51*w 66 := by
    have h:=pivot1_40 X Y Z a hX hY hZ w hw
    change w 51=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole1 X Y Z a 46*w 66 := by
    have h:=pivot1_39 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 46=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z38 : w 38=pole1 X Y Z a 38*w 66 := by
    have h:=pivot1_38 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 38=((1)/(Y^4) + ((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z33 : w 33=pole1 X Y Z a 33*w 66 := by
    have h:=pivot1_37 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 33=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X^2))*v18
  have z30 : w 30=pole1 X Y Z a 30*w 66 := by
    have h:=pivot1_36 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 30=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z28 : w 28=pole1 X Y Z a 28*w 66 := by
    have h:=pivot1_35 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 28=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v18
  have z24 : w 24=pole1 X Y Z a 24*w 66 := by
    have h:=pivot1_34 X Y Z a hX hY hZ w hw
    change w 24=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole1 X Y Z a 56*w 66 := by
    have h:=pivot1_33 X Y Z a hX hY hZ w hw
    change w 56=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole1 X Y Z a 12*w 66 := by
    have h:=pivot1_32 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 12=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z75 : w 75=pole1 X Y Z a 75*w 66 := by
    have h:=pivot1_31 X Y Z a hX hY hZ w hw
    have v28:=z28
    change w 28=(((-1)*Z)/(Y^2))*w 66 at v28
    change w 75=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2*Z))*v28
  have z72 : w 72=pole1 X Y Z a 72*w 66 := by
    have h:=pivot1_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 72=((1)/(Y^2) + ((-1)*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z70 : w 70=pole1 X Y Z a 70*w 66 := by
    have h:=pivot1_29 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 70=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v18
  have z14 : w 14=pole1 X Y Z a 14*w 66 := by
    have h:=pivot1_28 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole1 X Y Z a 63*w 66 := by
    have h:=pivot1_27 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1))/(Y^2) + (1*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66 at v12
    change w 63=((1*Z)/(X^2*Y^2) + ((-1)*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X^2))*v12
  have z9 : w 9=pole1 X Y Z a 9*w 66 := by
    have h:=pivot1_26 X Y Z a hX hY hZ w hw
    have v56:=z56
    change w 56=((1*Z)/(Y^2))*w 66 at v56
    change w 9=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2*Z))*v56
  have z4 : w 4=pole1 X Y Z a 4*w 66 := by
    have h:=pivot1_25 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 4=((1)/(Y^4) + ((-1)*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z80 : w 80=pole1 X Y Z a 80*w 66 := by
    have h:=pivot1_24 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66 at v21
    change w 80=(((-1))/(Y^4) + (1*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z11 : w 11=pole1 X Y Z a 11*w 66 := by
    have h:=pivot1_23 X Y Z a hX hY hZ w hw
    change w 11=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z53 : w 53=pole1 X Y Z a 53*w 66 := by
    have h:=pivot1_22 X Y Z a hX hY hZ w hw
    change w 53=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z83 : w 83=pole1 X Y Z a 83*w 66 := by
    have h:=pivot1_21 X Y Z a hX hY hZ w hw
    change w 83=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole1 X Y Z a 49*w 66 := by
    have h:=pivot1_20 X Y Z a hX hY hZ w hw
    change w 49=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole1 X Y Z a 45*w 66 := by
    have h:=pivot1_19 X Y Z a hX hY hZ w hw
    change w 45=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z44 : w 44=pole1 X Y Z a 44*w 66 := by
    have h:=pivot1_18 X Y Z a hX hY hZ w hw
    change w 44=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole1 X Y Z a 43*w 66 := by
    have h:=pivot1_17 X Y Z a hX hY hZ w hw
    change w 43=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole1 X Y Z a 41*w 66 := by
    have h:=pivot1_16 X Y Z a hX hY hZ w hw
    change w 41=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole1 X Y Z a 40*w 66 := by
    have h:=pivot1_15 X Y Z a hX hY hZ w hw
    change w 40=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z39 : w 39=pole1 X Y Z a 39*w 66 := by
    have h:=pivot1_14 X Y Z a hX hY hZ w hw
    change w 39=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z35 : w 35=pole1 X Y Z a 35*w 66 := by
    have h:=pivot1_13 X Y Z a hX hY hZ w hw
    change w 35=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z77 : w 77=pole1 X Y Z a 77*w 66 := by
    have h:=pivot1_12 X Y Z a hX hY hZ w hw
    change w 77=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole1 X Y Z a 36*w 66 := by
    have h:=pivot1_11 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole1 X Y Z a 48*w 66 := by
    have h:=pivot1_10 X Y Z a hX hY hZ w hw
    change w 48=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z7 : w 7=pole1 X Y Z a 7*w 66 := by
    have h:=pivot1_9 X Y Z a hX hY hZ w hw
    change w 7=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole1 X Y Z a 6*w 66 := by
    have h:=pivot1_8 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole1 X Y Z a 3*w 66 := by
    have h:=pivot1_7 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole1 X Y Z a 2*w 66 := by
    have h:=pivot1_6 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole1 X Y Z a 1*w 66 := by
    have h:=pivot1_5 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z78 : w 78=pole1 X Y Z a 78*w 66 := by
    have h:=pivot1_4 X Y Z a hX hY hZ w hw
    change w 78=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z42 : w 42=pole1 X Y Z a 42*w 66 := by
    have h:=pivot1_3 X Y Z a hX hY hZ w hw
    change w 42=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z81 : w 81=pole1 X Y Z a 81*w 66 := by
    have h:=pivot1_2 X Y Z a hX hY hZ w hw
    change w 81=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z82 : w 82=pole1 X Y Z a 82*w 66 := by
    have h:=pivot1_1 X Y Z a hX hY hZ w hw
    change w 82=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole1 X Y Z a 0*w 66 := by
    have h:=pivot1_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  intro j
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
  · change w 66=1*w 66
    exact (one_mul _).symm
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

#print axioms kernel_case1

theorem kernel_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole2 X Y Z a j*w 66 := by
  have z67 : w 67=pole2 X Y Z a 67*w 66 := by
    have h:=pivot2_82 X Y Z a hX hY hZ w hw
    change w 67=((3)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (5*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + (7)/(2*X^2) + ((-1)*a^2)/(X^2) + (1*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z73 : w 73=pole2 X Y Z a 73*w 66 := by
    have h:=pivot2_81 X Y Z a hX hY hZ w hw
    change w 73=((2)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (3*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z59 : w 59=pole2 X Y Z a 59*w 66 := by
    have h:=pivot2_80 X Y Z a hX hY hZ w hw
    change w 59=((1)/(X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (2)/(X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole2 X Y Z a 65*w 66 := by
    have h:=pivot2_79 X Y Z a hX hY hZ w hw
    change w 65=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z61 : w 61=pole2 X Y Z a 61*w 66 := by
    have h:=pivot2_78 X Y Z a hX hY hZ w hw
    change w 61=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole2 X Y Z a 21*w 66 := by
    have h:=pivot2_77 X Y Z a hX hY hZ w hw
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole2 X Y Z a 64*w 66 := by
    have h:=pivot2_76 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 64=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z) + ((-2)*X^2)/(Z))*v21
  have z62 : w 62=pole2 X Y Z a 62*w 66 := by
    have h:=pivot2_75 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 62=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v64
  have z69 : w 69=pole2 X Y Z a 69*w 66 := by
    have h:=pivot2_74 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 69=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(Z))*v21
  have z74 : w 74=pole2 X Y Z a 74*w 66 := by
    have h:=pivot2_73 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 74=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z68 : w 68=pole2 X Y Z a 68*w 66 := by
    have h:=pivot2_72 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 68=((2)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z58 : w 58=pole2 X Y Z a 58*w 66 := by
    have h:=pivot2_71 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 58=((2)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z55 : w 55=pole2 X Y Z a 55*w 66 := by
    have h:=pivot2_70 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 55=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v69
  have z71 : w 71=pole2 X Y Z a 71*w 66 := by
    have h:=pivot2_69 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 71=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z18 : w 18=pole2 X Y Z a 18*w 66 := by
    have h:=pivot2_68 X Y Z a hX hY hZ w hw
    change w 18=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z37 : w 37=pole2 X Y Z a 37*w 66 := by
    have h:=pivot2_67 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 37=((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z34 : w 34=pole2 X Y Z a 34*w 66 := by
    have h:=pivot2_66 X Y Z a hX hY hZ w hw
    change w 34=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole2 X Y Z a 32*w 66 := by
    have h:=pivot2_65 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 32=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v74
  have z31 : w 31=pole2 X Y Z a 31*w 66 := by
    have h:=pivot2_64 X Y Z a hX hY hZ w hw
    have v73:=z73
    change w 73=((2)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (3*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v73
    change w 31=(((-2))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-3)*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v73
  have z29 : w 29=pole2 X Y Z a 29*w 66 := by
    have h:=pivot2_63 X Y Z a hX hY hZ w hw
    have v71:=z71
    change w 71=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v71
    change w 29=((1)/(X^2*Y^2) + (1)/(X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v71
  have z27 : w 27=pole2 X Y Z a 27*w 66 := by
    have h:=pivot2_62 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 27=((1)/(X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v69
  have z26 : w 26=pole2 X Y Z a 26*w 66 := by
    have h:=pivot2_61 X Y Z a hX hY hZ w hw
    have v68:=z68
    change w 68=((2)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v68
    change w 26=(((-2))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v68
  have z25 : w 25=pole2 X Y Z a 25*w 66 := by
    have h:=pivot2_60 X Y Z a hX hY hZ w hw
    have v67:=z67
    change w 67=((3)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (5*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + (7)/(2*X^2) + ((-1)*a^2)/(X^2) + (1*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66 at v67
    change w 25=(((-3))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-5)*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + ((-7))/(2*X^2) + (1*a^2)/(X^2) + ((-1)*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v67
  have z23 : w 23=pole2 X Y Z a 23*w 66 := by
    have h:=pivot2_59 X Y Z a hX hY hZ w hw
    have v65:=z65
    change w 65=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v65
    change w 23=((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v65
  have z22 : w 22=pole2 X Y Z a 22*w 66 := by
    have h:=pivot2_58 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 22=((1)/(Y^4) + (1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v64
  have z20 : w 20=pole2 X Y Z a 20*w 66 := by
    have h:=pivot2_57 X Y Z a hX hY hZ w hw
    have v62:=z62
    change w 62=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v62
    change w 20=((1)/(Y^4) + (1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v62
  have z19 : w 19=pole2 X Y Z a 19*w 66 := by
    have h:=pivot2_56 X Y Z a hX hY hZ w hw
    have v61:=z61
    change w 61=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v61
    change w 19=((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v61
  have z17 : w 17=pole2 X Y Z a 17*w 66 := by
    have h:=pivot2_55 X Y Z a hX hY hZ w hw
    have v59:=z59
    change w 59=((1)/(X^2*Y^2) + (1*a)/(X^2*Y) + (1*Z*a)/(2*X^2*Y) + (2)/(X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v59
    change w 17=(((-1))/(X^2*Y^2) + ((-1)*a)/(X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-2))/(X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v59
  have z16 : w 16=pole2 X Y Z a 16*w 66 := by
    have h:=pivot2_54 X Y Z a hX hY hZ w hw
    have v58:=z58
    change w 58=((2)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v58
    change w 16=(((-2))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v58
  have z57 : w 57=pole2 X Y Z a 57*w 66 := by
    have h:=pivot2_53 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 57=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z13 : w 13=pole2 X Y Z a 13*w 66 := by
    have h:=pivot2_52 X Y Z a hX hY hZ w hw
    have v55:=z55
    change w 55=(((-1))/(X^2*Y^2) + ((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v55
    change w 13=((1)/(X^2*Y^2) + (1)/(X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v55
  have z52 : w 52=pole2 X Y Z a 52*w 66 := by
    have h:=pivot2_51 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 52=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2))*v69
  have z50 : w 50=pole2 X Y Z a 50*w 66 := by
    have h:=pivot2_50 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 50=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2))*v18
  have z47 : w 47=pole2 X Y Z a 47*w 66 := by
    have h:=pivot2_49 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 47=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z5 : w 5=pole2 X Y Z a 5*w 66 := by
    have h:=pivot2_48 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 5=((1)/(X^2*Y^4) + (1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z76 : w 76=pole2 X Y Z a 76*w 66 := by
    have h:=pivot2_47 X Y Z a hX hY hZ w hw
    change w 76=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z15 : w 15=pole2 X Y Z a 15*w 66 := by
    have h:=pivot2_46 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 15=((1)/(X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2))*v74
  have z10 : w 10=pole2 X Y Z a 10*w 66 := by
    have h:=pivot2_45 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1))/(X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 10=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2))*v69
  have z8 : w 8=pole2 X Y Z a 8*w 66 := by
    have h:=pivot2_44 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 8=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v18
  have z79 : w 79=pole2 X Y Z a 79*w 66 := by
    have h:=pivot2_43 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 79=(((-1))/(X^2*Y^4) + ((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z60 : w 60=pole2 X Y Z a 60*w 66 := by
    have h:=pivot2_42 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 60=(1)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v18
  have z54 : w 54=pole2 X Y Z a 54*w 66 := by
    have h:=pivot2_41 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 54=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z51 : w 51=pole2 X Y Z a 51*w 66 := by
    have h:=pivot2_40 X Y Z a hX hY hZ w hw
    change w 51=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole2 X Y Z a 46*w 66 := by
    have h:=pivot2_39 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 46=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z38 : w 38=pole2 X Y Z a 38*w 66 := by
    have h:=pivot2_38 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 38=((1)/(Y^4) + (1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z33 : w 33=pole2 X Y Z a 33*w 66 := by
    have h:=pivot2_37 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 33=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X^2))*v18
  have z30 : w 30=pole2 X Y Z a 30*w 66 := by
    have h:=pivot2_36 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 30=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z28 : w 28=pole2 X Y Z a 28*w 66 := by
    have h:=pivot2_35 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 28=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v18
  have z24 : w 24=pole2 X Y Z a 24*w 66 := by
    have h:=pivot2_34 X Y Z a hX hY hZ w hw
    change w 24=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole2 X Y Z a 56*w 66 := by
    have h:=pivot2_33 X Y Z a hX hY hZ w hw
    change w 56=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole2 X Y Z a 12*w 66 := by
    have h:=pivot2_32 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 12=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z75 : w 75=pole2 X Y Z a 75*w 66 := by
    have h:=pivot2_31 X Y Z a hX hY hZ w hw
    have v28:=z28
    change w 28=((1*Z)/(Y^2))*w 66 at v28
    change w 75=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2*Z))*v28
  have z72 : w 72=pole2 X Y Z a 72*w 66 := by
    have h:=pivot2_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 72=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z70 : w 70=pole2 X Y Z a 70*w 66 := by
    have h:=pivot2_29 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 70=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v18
  have z14 : w 14=pole2 X Y Z a 14*w 66 := by
    have h:=pivot2_28 X Y Z a hX hY hZ w hw
    change w 14=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole2 X Y Z a 63*w 66 := by
    have h:=pivot2_27 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66 at v12
    change w 63=(((-1)*Z)/(X^2*Y^2) + ((-1)*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X^2))*v12
  have z9 : w 9=pole2 X Y Z a 9*w 66 := by
    have h:=pivot2_26 X Y Z a hX hY hZ w hw
    have v56:=z56
    change w 56=(((-1)*Z)/(Y^2))*w 66 at v56
    change w 9=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2*Z))*v56
  have z4 : w 4=pole2 X Y Z a 4*w 66 := by
    have h:=pivot2_25 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 4=((1)/(Y^4) + (1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z80 : w 80=pole2 X Y Z a 80*w 66 := by
    have h:=pivot2_24 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z)/(X^2*Y^2) + (1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 80=(((-1))/(Y^4) + ((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z11 : w 11=pole2 X Y Z a 11*w 66 := by
    have h:=pivot2_23 X Y Z a hX hY hZ w hw
    change w 11=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z53 : w 53=pole2 X Y Z a 53*w 66 := by
    have h:=pivot2_22 X Y Z a hX hY hZ w hw
    change w 53=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z83 : w 83=pole2 X Y Z a 83*w 66 := by
    have h:=pivot2_21 X Y Z a hX hY hZ w hw
    change w 83=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole2 X Y Z a 49*w 66 := by
    have h:=pivot2_20 X Y Z a hX hY hZ w hw
    change w 49=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole2 X Y Z a 45*w 66 := by
    have h:=pivot2_19 X Y Z a hX hY hZ w hw
    change w 45=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z44 : w 44=pole2 X Y Z a 44*w 66 := by
    have h:=pivot2_18 X Y Z a hX hY hZ w hw
    change w 44=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole2 X Y Z a 43*w 66 := by
    have h:=pivot2_17 X Y Z a hX hY hZ w hw
    change w 43=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole2 X Y Z a 41*w 66 := by
    have h:=pivot2_16 X Y Z a hX hY hZ w hw
    change w 41=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole2 X Y Z a 40*w 66 := by
    have h:=pivot2_15 X Y Z a hX hY hZ w hw
    change w 40=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z39 : w 39=pole2 X Y Z a 39*w 66 := by
    have h:=pivot2_14 X Y Z a hX hY hZ w hw
    change w 39=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z35 : w 35=pole2 X Y Z a 35*w 66 := by
    have h:=pivot2_13 X Y Z a hX hY hZ w hw
    change w 35=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z77 : w 77=pole2 X Y Z a 77*w 66 := by
    have h:=pivot2_12 X Y Z a hX hY hZ w hw
    change w 77=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole2 X Y Z a 36*w 66 := by
    have h:=pivot2_11 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole2 X Y Z a 48*w 66 := by
    have h:=pivot2_10 X Y Z a hX hY hZ w hw
    change w 48=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z7 : w 7=pole2 X Y Z a 7*w 66 := by
    have h:=pivot2_9 X Y Z a hX hY hZ w hw
    change w 7=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole2 X Y Z a 6*w 66 := by
    have h:=pivot2_8 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole2 X Y Z a 3*w 66 := by
    have h:=pivot2_7 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole2 X Y Z a 2*w 66 := by
    have h:=pivot2_6 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole2 X Y Z a 1*w 66 := by
    have h:=pivot2_5 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z78 : w 78=pole2 X Y Z a 78*w 66 := by
    have h:=pivot2_4 X Y Z a hX hY hZ w hw
    change w 78=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z42 : w 42=pole2 X Y Z a 42*w 66 := by
    have h:=pivot2_3 X Y Z a hX hY hZ w hw
    change w 42=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z81 : w 81=pole2 X Y Z a 81*w 66 := by
    have h:=pivot2_2 X Y Z a hX hY hZ w hw
    change w 81=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z82 : w 82=pole2 X Y Z a 82*w 66 := by
    have h:=pivot2_1 X Y Z a hX hY hZ w hw
    change w 82=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole2 X Y Z a 0*w 66 := by
    have h:=pivot2_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  intro j
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
  · change w 66=1*w 66
    exact (one_mul _).symm
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

#print axioms kernel_case2

theorem kernel_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole3 X Y Z a j*w 66 := by
  have z67 : w 67=pole3 X Y Z a 67*w 66 := by
    have h:=pivot3_82 X Y Z a hX hY hZ w hw
    change w 67=((2)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(X^2) + (1*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z73 : w 73=pole3 X Y Z a 73*w 66 := by
    have h:=pivot3_81 X Y Z a hX hY hZ w hw
    change w 73=((1)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(2*X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z59 : w 59=pole3 X Y Z a 59*w 66 := by
    have h:=pivot3_80 X Y Z a hX hY hZ w hw
    change w 59=((1)/(X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole3 X Y Z a 65*w 66 := by
    have h:=pivot3_79 X Y Z a hX hY hZ w hw
    change w 65=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z61 : w 61=pole3 X Y Z a 61*w 66 := by
    have h:=pivot3_78 X Y Z a hX hY hZ w hw
    change w 61=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole3 X Y Z a 21*w 66 := by
    have h:=pivot3_77 X Y Z a hX hY hZ w hw
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole3 X Y Z a 64*w 66 := by
    have h:=pivot3_76 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 64=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z) + ((-2)*X^2)/(Z))*v21
  have z62 : w 62=pole3 X Y Z a 62*w 66 := by
    have h:=pivot3_75 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 62=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v64
  have z69 : w 69=pole3 X Y Z a 69*w 66 := by
    have h:=pivot3_74 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 69=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(Z))*v21
  have z74 : w 74=pole3 X Y Z a 74*w 66 := by
    have h:=pivot3_73 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 74=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z68 : w 68=pole3 X Y Z a 68*w 66 := by
    have h:=pivot3_72 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 68=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z58 : w 58=pole3 X Y Z a 58*w 66 := by
    have h:=pivot3_71 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 58=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z55 : w 55=pole3 X Y Z a 55*w 66 := by
    have h:=pivot3_70 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 55=(((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((-1))*v69
  have z71 : w 71=pole3 X Y Z a 71*w 66 := by
    have h:=pivot3_69 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 71=(((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z18 : w 18=pole3 X Y Z a 18*w 66 := by
    have h:=pivot3_68 X Y Z a hX hY hZ w hw
    change w 18=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z37 : w 37=pole3 X Y Z a 37*w 66 := by
    have h:=pivot3_67 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 37=((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z34 : w 34=pole3 X Y Z a 34*w 66 := by
    have h:=pivot3_66 X Y Z a hX hY hZ w hw
    change w 34=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole3 X Y Z a 32*w 66 := by
    have h:=pivot3_65 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 32=((1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v74
  have z31 : w 31=pole3 X Y Z a 31*w 66 := by
    have h:=pivot3_64 X Y Z a hX hY hZ w hw
    have v73:=z73
    change w 73=((1)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + (1*Z*a)/(2*X^2*Y) + (1)/(2*X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v73
    change w 31=(((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(2*X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v73
  have z29 : w 29=pole3 X Y Z a 29*w 66 := by
    have h:=pivot3_63 X Y Z a hX hY hZ w hw
    have v71:=z71
    change w 71=(((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v71
    change w 29=((1)/(X^2*Y^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v71
  have z27 : w 27=pole3 X Y Z a 27*w 66 := by
    have h:=pivot3_62 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 27=((1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v69
  have z26 : w 26=pole3 X Y Z a 26*w 66 := by
    have h:=pivot3_61 X Y Z a hX hY hZ w hw
    have v68:=z68
    change w 68=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v68
    change w 26=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v68
  have z25 : w 25=pole3 X Y Z a 25*w 66 := by
    have h:=pivot3_60 X Y Z a hX hY hZ w hw
    have v67:=z67
    change w 67=((2)/(X^2*Y^2) + (1*Z)/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + (1*Z*a)/(X^2*Y) + (3)/(2*X^2) + ((-1)*a^2)/(X^2) + (1*Z)/(X^2) + ((-2)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2))*w 66 at v67
    change w 25=(((-2))/(X^2*Y^2) + ((-1)*Z)/(2*X^2*Y^2) + ((-1)*a)/(2*X^2*Y) + ((-1)*Z*a)/(X^2*Y) + ((-3))/(2*X^2) + (1*a^2)/(X^2) + ((-1)*Z)/(X^2) + (2*Y*a)/(X^2) + (1*Y^2)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v67
  have z23 : w 23=pole3 X Y Z a 23*w 66 := by
    have h:=pivot3_59 X Y Z a hX hY hZ w hw
    have v65:=z65
    change w 65=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v65
    change w 23=((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v65
  have z22 : w 22=pole3 X Y Z a 22*w 66 := by
    have h:=pivot3_58 X Y Z a hX hY hZ w hw
    have v64:=z64
    change w 64=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v64
    change w 22=((1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v64
  have z20 : w 20=pole3 X Y Z a 20*w 66 := by
    have h:=pivot3_57 X Y Z a hX hY hZ w hw
    have v62:=z62
    change w 62=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + (1)/(2*Y^2) + ((-1)*a)/(Y))*w 66 at v62
    change w 20=((1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + ((-1))/(2*Y^2) + (1*a)/(Y))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v62
  have z19 : w 19=pole3 X Y Z a 19*w 66 := by
    have h:=pivot3_56 X Y Z a hX hY hZ w hw
    have v61:=z61
    change w 61=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + ((-1)*Y*a)/(2*X^2))*w 66 at v61
    change w 19=((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + (1*Y*a)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v61
  have z17 : w 17=pole3 X Y Z a 17*w 66 := by
    have h:=pivot3_55 X Y Z a hX hY hZ w hw
    have v59:=z59
    change w 59=((1)/(X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1)/(X^2) + ((-1)*a^2)/(2*X^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(2*X^2))*w 66 at v59
    change w 17=(((-1))/(X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + ((-1))/(X^2) + (1*a^2)/(2*X^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v59
  have z16 : w 16=pole3 X Y Z a 16*w 66 := by
    have h:=pivot3_54 X Y Z a hX hY hZ w hw
    have v58:=z58
    change w 58=((1)/(Y^2) + (1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66 at v58
    change w 16=(((-1))/(Y^2) + ((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v58
  have z57 : w 57=pole3 X Y Z a 57*w 66 := by
    have h:=pivot3_53 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 57=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2))*v74
  have z13 : w 13=pole3 X Y Z a 13*w 66 := by
    have h:=pivot3_52 X Y Z a hX hY hZ w hw
    have v55:=z55
    change w 55=(((-1))/(X^2*Y^2) + ((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v55
    change w 13=((1)/(X^2*Y^2) + (1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v55
  have z52 : w 52=pole3 X Y Z a 52*w 66 := by
    have h:=pivot3_51 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 52=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2))*v69
  have z50 : w 50=pole3 X Y Z a 50*w 66 := by
    have h:=pivot3_50 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 50=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2))*v18
  have z47 : w 47=pole3 X Y Z a 47*w 66 := by
    have h:=pivot3_49 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 47=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z5 : w 5=pole3 X Y Z a 5*w 66 := by
    have h:=pivot3_48 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 5=((1*Z)/(2*X^2*Y^4) + ((-1)*a)/(2*X^2*Y^3) + (1)/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2*Z))*v21
  have z76 : w 76=pole3 X Y Z a 76*w 66 := by
    have h:=pivot3_47 X Y Z a hX hY hZ w hw
    change w 76=((1)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z15 : w 15=pole3 X Y Z a 15*w 66 := by
    have h:=pivot3_46 X Y Z a hX hY hZ w hw
    have v74:=z74
    change w 74=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + (1)/(2))*w 66 at v74
    change w 15=((1*Z)/(2*X^2) + ((-1)*Y*a)/(2*X^2) + ((-1)*Y^2)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X^2))*v74
  have z10 : w 10=pole3 X Y Z a 10*w 66 := by
    have h:=pivot3_45 X Y Z a hX hY hZ w hw
    have v69:=z69
    change w 69=(((-1)*Z)/(2*X^2) + (1*Y*a)/(2*X^2) + (1*Y^2)/(2*X^2))*w 66 at v69
    change w 10=((1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2))*v69
  have z8 : w 8=pole3 X Y Z a 8*w 66 := by
    have h:=pivot3_44 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 8=(((-1))/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v18
  have z79 : w 79=pole3 X Y Z a 79*w 66 := by
    have h:=pivot3_43 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 79=(((-1)*Z)/(2*X^2*Y^4) + (1*a)/(2*X^2*Y^3) + ((-1))/(2*X^2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(Y^2*Z))*v21
  have z60 : w 60=pole3 X Y Z a 60*w 66 := by
    have h:=pivot3_42 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 60=(1)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v18
  have z54 : w 54=pole3 X Y Z a 54*w 66 := by
    have h:=pivot3_41 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 54=((1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z51 : w 51=pole3 X Y Z a 51*w 66 := by
    have h:=pivot3_40 X Y Z a hX hY hZ w hw
    change w 51=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole3 X Y Z a 46*w 66 := by
    have h:=pivot3_39 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 46=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z38 : w 38=pole3 X Y Z a 38*w 66 := by
    have h:=pivot3_38 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 38=((1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z33 : w 33=pole3 X Y Z a 33*w 66 := by
    have h:=pivot3_37 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 33=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X^2))*v18
  have z30 : w 30=pole3 X Y Z a 30*w 66 := by
    have h:=pivot3_36 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 30=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z28 : w 28=pole3 X Y Z a 28*w 66 := by
    have h:=pivot3_35 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 28=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v18
  have z24 : w 24=pole3 X Y Z a 24*w 66 := by
    have h:=pivot3_34 X Y Z a hX hY hZ w hw
    change w 24=((-1))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole3 X Y Z a 56*w 66 := by
    have h:=pivot3_33 X Y Z a hX hY hZ w hw
    change w 56=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole3 X Y Z a 12*w 66 := by
    have h:=pivot3_32 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 12=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Z))*v21
  have z75 : w 75=pole3 X Y Z a 75*w 66 := by
    have h:=pivot3_31 X Y Z a hX hY hZ w hw
    have v28:=z28
    change w 28=((1*Z)/(Y^2))*w 66 at v28
    change w 75=((1)/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2*Z))*v28
  have z72 : w 72=pole3 X Y Z a 72*w 66 := by
    have h:=pivot3_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 72=((1*Z)/(2*Y^2) + ((-1)*a)/(2*Y) + (1)/(2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Z))*v21
  have z70 : w 70=pole3 X Y Z a 70*w 66 := by
    have h:=pivot3_29 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((-1))*w 66 at v18
    change w 70=(((-1)*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v18
  have z14 : w 14=pole3 X Y Z a 14*w 66 := by
    have h:=pivot3_28 X Y Z a hX hY hZ w hw
    change w 14=((1*Z)/(Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole3 X Y Z a 63*w 66 := by
    have h:=pivot3_27 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*Z)/(2*Y^2) + (1*a)/(2*Y) + ((-1))/(2))*w 66 at v12
    change w 63=(((-1)*Z^2)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + ((-1)*Z)/(2*X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X^2))*v12
  have z9 : w 9=pole3 X Y Z a 9*w 66 := by
    have h:=pivot3_26 X Y Z a hX hY hZ w hw
    have v56:=z56
    change w 56=(((-1)*Z)/(Y^2))*w 66 at v56
    change w 9=(((-1))/(X^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X^2*Z))*v56
  have z4 : w 4=pole3 X Y Z a 4*w 66 := by
    have h:=pivot3_25 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 4=((1*Z)/(2*Y^4) + ((-1)*a)/(2*Y^3) + (1)/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X^2)/(Y^2*Z))*v21
  have z80 : w 80=pole3 X Y Z a 80*w 66 := by
    have h:=pivot3_24 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Z^2)/(2*X^2*Y^2) + ((-1)*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2))*w 66 at v21
    change w 80=(((-1)*Z)/(2*Y^4) + (1*a)/(2*Y^3) + ((-1))/(2*Y^2))*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X^2)/(Y^2*Z))*v21
  have z11 : w 11=pole3 X Y Z a 11*w 66 := by
    have h:=pivot3_23 X Y Z a hX hY hZ w hw
    change w 11=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z53 : w 53=pole3 X Y Z a 53*w 66 := by
    have h:=pivot3_22 X Y Z a hX hY hZ w hw
    change w 53=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z83 : w 83=pole3 X Y Z a 83*w 66 := by
    have h:=pivot3_21 X Y Z a hX hY hZ w hw
    change w 83=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole3 X Y Z a 49*w 66 := by
    have h:=pivot3_20 X Y Z a hX hY hZ w hw
    change w 49=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole3 X Y Z a 45*w 66 := by
    have h:=pivot3_19 X Y Z a hX hY hZ w hw
    change w 45=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z44 : w 44=pole3 X Y Z a 44*w 66 := by
    have h:=pivot3_18 X Y Z a hX hY hZ w hw
    change w 44=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole3 X Y Z a 43*w 66 := by
    have h:=pivot3_17 X Y Z a hX hY hZ w hw
    change w 43=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole3 X Y Z a 41*w 66 := by
    have h:=pivot3_16 X Y Z a hX hY hZ w hw
    change w 41=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole3 X Y Z a 40*w 66 := by
    have h:=pivot3_15 X Y Z a hX hY hZ w hw
    change w 40=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z39 : w 39=pole3 X Y Z a 39*w 66 := by
    have h:=pivot3_14 X Y Z a hX hY hZ w hw
    change w 39=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z35 : w 35=pole3 X Y Z a 35*w 66 := by
    have h:=pivot3_13 X Y Z a hX hY hZ w hw
    change w 35=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z77 : w 77=pole3 X Y Z a 77*w 66 := by
    have h:=pivot3_12 X Y Z a hX hY hZ w hw
    change w 77=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole3 X Y Z a 36*w 66 := by
    have h:=pivot3_11 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole3 X Y Z a 48*w 66 := by
    have h:=pivot3_10 X Y Z a hX hY hZ w hw
    change w 48=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z7 : w 7=pole3 X Y Z a 7*w 66 := by
    have h:=pivot3_9 X Y Z a hX hY hZ w hw
    change w 7=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole3 X Y Z a 6*w 66 := by
    have h:=pivot3_8 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole3 X Y Z a 3*w 66 := by
    have h:=pivot3_7 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole3 X Y Z a 2*w 66 := by
    have h:=pivot3_6 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole3 X Y Z a 1*w 66 := by
    have h:=pivot3_5 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z78 : w 78=pole3 X Y Z a 78*w 66 := by
    have h:=pivot3_4 X Y Z a hX hY hZ w hw
    change w 78=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z42 : w 42=pole3 X Y Z a 42*w 66 := by
    have h:=pivot3_3 X Y Z a hX hY hZ w hw
    change w 42=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z81 : w 81=pole3 X Y Z a 81*w 66 := by
    have h:=pivot3_2 X Y Z a hX hY hZ w hw
    change w 81=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z82 : w 82=pole3 X Y Z a 82*w 66 := by
    have h:=pivot3_1 X Y Z a hX hY hZ w hw
    change w 82=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole3 X Y Z a 0*w 66 := by
    have h:=pivot3_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 66
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  intro j
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
  · change w 66=1*w 66
    exact (one_mul _).symm
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

#print axioms kernel_case3

end SmallLevelTwentyEightTriangular
end
end
