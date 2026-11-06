module

public import SmallLevelTwentyTwoLaurentTheoryV4

/-! Consolidated chapter: SmallLevelTwentyTwoTriangular. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyTwoTriangularIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot1_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row1_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_0

theorem pivot1_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row1_0 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(X*Z))

#print axioms pivot1_1

theorem pivot1_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row1_1 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot1_2

theorem pivot1_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row1_2 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0)*(1)

#print axioms pivot1_3

theorem pivot1_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row1_3 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot1_4

theorem pivot1_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row1_4 X Y Z a hX hY hZ w hw
  have p4:=pivot1_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X*Y^2)*p4)*(1)

#print axioms pivot1_5

theorem pivot1_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row1_5 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0)*(1)

#print axioms pivot1_6

theorem pivot1_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row1_6 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Y^2*Z))

#print axioms pivot1_7

theorem pivot1_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row1_7 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot1_8

theorem pivot1_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row1_8 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6)*(1)

#print axioms pivot1_9

theorem pivot1_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row1_9 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Z))

#print axioms pivot1_10

theorem pivot1_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row1_10 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1)*(1)

#print axioms pivot1_11

theorem pivot1_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row1_11 X Y Z a hX hY hZ w hw
  have p4:=pivot1_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p4)*(1)

#print axioms pivot1_12

theorem pivot1_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row1_12 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p1)*(1)

#print axioms pivot1_13

theorem pivot1_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 9 + ((1*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row1_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_14

theorem pivot1_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 11 + ((1*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row1_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_15

theorem pivot1_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row1_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(X*Y^2))

#print axioms pivot1_16

theorem pivot1_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row1_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X*Z))

#print axioms pivot1_17

theorem pivot1_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row1_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot1_18

theorem pivot1_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row1_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_19

theorem pivot1_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row1_19 X Y Z a hX hY hZ w hw
  have p19:=pivot1_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p19)*(1)

#print axioms pivot1_20

theorem pivot1_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row1_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot1_21

theorem pivot1_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row1_21 X Y Z a hX hY hZ w hw
  have p19:=pivot1_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X))*p19)*(1)

#print axioms pivot1_22

theorem pivot1_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 37 + (((-1))/(X*Y^2))*w 42=0 := by
  have h:=normalized_row1_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_23

theorem pivot1_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 38 + (((-1)*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row1_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_24

theorem pivot1_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 39 + (((-1))/(X))*w 54=0 := by
  have h:=normalized_row1_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_25

theorem pivot1_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 22 + ((1*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row1_25 X Y Z a hX hY hZ w hw
  have p17:=pivot1_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p17)*((1*Z)/(Y^2))

#print axioms pivot1_26

theorem pivot1_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row1_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot1_27

theorem pivot1_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row1_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot1_28

theorem pivot1_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 7 + (((-1))/(X*Y^2))*w 12=0 := by
  have h:=normalized_row1_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot1_29

theorem pivot1_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 8 + (((-1)*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row1_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot1_30

theorem pivot1_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 24 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row1_30 X Y Z a hX hY hZ w hw
  have p14:=pivot1_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p14)*(1)

#print axioms pivot1_31

theorem pivot1_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row1_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_32

theorem pivot1_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 29 + ((1)/(X*Z))*w 44=0 := by
  have h:=normalized_row1_32 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p31)*(1)

#print axioms pivot1_33

theorem pivot1_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 31 + (((-1))/(X*Y^2))*w 54=0 := by
  have h:=normalized_row1_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot1_34

theorem pivot1_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 5 + (((-1))/(X*Y^2))*w 48=0 := by
  have h:=normalized_row1_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot1_35

theorem pivot1_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 42 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row1_47 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*(((-1)*Y^2)/(Z))

#print axioms pivot1_36

theorem pivot1_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row1_48 X Y Z a hX hY hZ w hw
  have p15:=pivot1_15 X Y Z a hX hY hZ w hw
  have p16:=pivot1_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*(((-1)*X*Y^2)/(Z))

#print axioms pivot1_37

theorem pivot1_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row1_49 X Y Z a hX hY hZ w hw
  have p5:=pivot1_5 X Y Z a hX hY hZ w hw
  have p9:=pivot1_9 X Y Z a hX hY hZ w hw
  have p10:=pivot1_10 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot1_38

theorem pivot1_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row1_50 X Y Z a hX hY hZ w hw
  have p14:=pivot1_14 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - ((1)/(X))*p37)*((-1)*X)

#print axioms pivot1_39

theorem pivot1_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row1_35 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  have p15:=pivot1_15 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot1_40

theorem pivot1_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 20 + (((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44=0 := by
  have h:=normalized_row1_36 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  have p16:=pivot1_16 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot1_41

theorem pivot1_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 15 + (((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row1_51 X Y Z a hX hY hZ w hw
  have p5:=pivot1_5 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p5 - (1)*p39)*(1)

#print axioms pivot1_42

theorem pivot1_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row1_52 X Y Z a hX hY hZ w hw
  have p12:=pivot1_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p12)*(1)

#print axioms pivot1_43

theorem pivot1_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row1_53 X Y Z a hX hY hZ w hw
  have p11:=pivot1_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p11)*(1)

#print axioms pivot1_44

theorem pivot1_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row1_54 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot1_45

theorem pivot1_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row1_37 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  have p5:=pivot1_5 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  have p9:=pivot1_9 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p14:=pivot1_14 X Y Z a hX hY hZ w hw
  have p17:=pivot1_17 X Y Z a hX hY hZ w hw
  have p22:=pivot1_22 X Y Z a hX hY hZ w hw
  have p25:=pivot1_25 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p45:=pivot1_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0 - (1)*p1 - (((-1))/(X))*p5 - (1)*p6 - (((-1))/(X))*p9 - (((-1))/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - (((-1)*Y^2)/(X*Z))*p26 - (((-1))/(X))*p31 - (((-1))/(X))*p37 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot1_46

theorem pivot1_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 10 + (((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row1_55 X Y Z a hX hY hZ w hw
  have p24:=pivot1_24 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  have p45:=pivot1_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - ((1)/(X*Y^2))*p39 - ((1*X)/(Y^2))*p45)*(1*X)

#print axioms pivot1_47

theorem pivot1_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 12 + ((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row1_38 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p47:=pivot1_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - ((1)/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot1_48

theorem pivot1_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row1_39 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot1_49

theorem pivot1_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 21 + ((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row1_56 X Y Z a hX hY hZ w hw
  have p18:=pivot1_18 X Y Z a hX hY hZ w hw
  have p23:=pivot1_23 X Y Z a hX hY hZ w hw
  have p30:=pivot1_30 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - ((1)/(X))*p30 - ((1)/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot1_50

theorem pivot1_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 23 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row1_40 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p46:=pivot1_46 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - ((1)/(X*Z))*p26 - (((-1))/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot1_51

theorem pivot1_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 43 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row1_41 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot1_52

theorem pivot1_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 26 + (((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_58 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p18:=pivot1_18 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot1_53

theorem pivot1_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 13 + ((1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_59 X Y Z a hX hY hZ w hw
  have p40:=pivot1_40 X Y Z a hX hY hZ w hw
  have p53:=pivot1_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - ((1)/(X))*p53)*(1)

#print axioms pivot1_54

theorem pivot1_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row1_60 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p53:=pivot1_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - ((1)/(X*Y^2))*p38 - (((-1))/(X*Y^2))*p48 - (1)*p53)*(1*X)

#print axioms pivot1_55

theorem pivot1_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 19 + (((-1))/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_61 X Y Z a hX hY hZ w hw
  have p24:=pivot1_24 X Y Z a hX hY hZ w hw
  have p45:=pivot1_45 X Y Z a hX hY hZ w hw
  have p55:=pivot1_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot1_56

theorem pivot1_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row1_62 X Y Z a hX hY hZ w hw
  have p22:=pivot1_22 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p46:=pivot1_46 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - ((1)/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - ((1)/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot1_57

theorem pivot1_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 25 + (((-1))/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (2)/(Z) + 1 + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_42 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p5:=pivot1_5 X Y Z a hX hY hZ w hw
  have p9:=pivot1_9 X Y Z a hX hY hZ w hw
  have p10:=pivot1_10 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p16:=pivot1_16 X Y Z a hX hY hZ w hw
  have p21:=pivot1_21 X Y Z a hX hY hZ w hw
  have p23:=pivot1_23 X Y Z a hX hY hZ w hw
  have p29:=pivot1_29 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  have p34:=pivot1_34 X Y Z a hX hY hZ w hw
  have p37:=pivot1_37 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  have p52:=pivot1_52 X Y Z a hX hY hZ w hw
  have p54:=pivot1_54 X Y Z a hX hY hZ w hw
  have p56:=pivot1_56 X Y Z a hX hY hZ w hw
  have p57:=pivot1_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - (((-1))/(X*Y^2))*p31 - (1)*p34 - (((-1)*Z)/(X*Y^2))*p37 - ((1*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot1_58

theorem pivot1_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 40 + ((-1) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_43 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  have p11:=pivot1_11 X Y Z a hX hY hZ w hw
  have p17:=pivot1_17 X Y Z a hX hY hZ w hw
  have p18:=pivot1_18 X Y Z a hX hY hZ w hw
  have p22:=pivot1_22 X Y Z a hX hY hZ w hw
  have p25:=pivot1_25 X Y Z a hX hY hZ w hw
  have p26:=pivot1_26 X Y Z a hX hY hZ w hw
  have p27:=pivot1_27 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p40:=pivot1_40 X Y Z a hX hY hZ w hw
  have p43:=pivot1_43 X Y Z a hX hY hZ w hw
  have p45:=pivot1_45 X Y Z a hX hY hZ w hw
  have p47:=pivot1_47 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  have p55:=pivot1_55 X Y Z a hX hY hZ w hw
  have p57:=pivot1_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p11 - (((-1)*X)/(Y^2))*p17 - (1)*p18 - (((-1)*X)/(Y^2))*p22 - (((-1)*X)/(Y^2))*p25 - ((1)/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - (((-1))/(Y^2) + ((-1)*Z)/(Y^2))*p36 - (1)*p40 - (1)*p43 - (((-1)*X)/(Y^2))*p45 - (1)*p47 - (((-1))/(Y^2))*p48 - (((-1)*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot1_59

theorem pivot1_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 14 + (((-1)*X)/(Y^2*Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row1_63 X Y Z a hX hY hZ w hw
  have p29:=pivot1_29 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p59:=pivot1_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - ((1)/(X*Y^2))*p48 - (1)*p59)*(1*X)

#print axioms pivot1_60

theorem pivot1_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row1_44 X Y Z a hX hY hZ w hw
  have p1:=pivot1_1 X Y Z a hX hY hZ w hw
  have p3:=pivot1_3 X Y Z a hX hY hZ w hw
  have p6:=pivot1_6 X Y Z a hX hY hZ w hw
  have p12:=pivot1_12 X Y Z a hX hY hZ w hw
  have p14:=pivot1_14 X Y Z a hX hY hZ w hw
  have p19:=pivot1_19 X Y Z a hX hY hZ w hw
  have p22:=pivot1_22 X Y Z a hX hY hZ w hw
  have p24:=pivot1_24 X Y Z a hX hY hZ w hw
  have p25:=pivot1_25 X Y Z a hX hY hZ w hw
  have p30:=pivot1_30 X Y Z a hX hY hZ w hw
  have p38:=pivot1_38 X Y Z a hX hY hZ w hw
  have p41:=pivot1_41 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p46:=pivot1_46 X Y Z a hX hY hZ w hw
  have p48:=pivot1_48 X Y Z a hX hY hZ w hw
  have p49:=pivot1_49 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  have p53:=pivot1_53 X Y Z a hX hY hZ w hw
  have p60:=pivot1_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p12 - (((-1)*X)/(Y^2))*p14 - (1)*p19 - (((-1)*X)/(Y^2))*p22 - (1)*p24 - (((-1)*X)/(Y^2))*p25 - (1)*p30 - (((-1))/(Y^2))*p38 - (1)*p41 - (((-1)*X)/(Y^2))*p42 - (((-1)*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - ((1*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot1_61

theorem pivot1_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    (1)*w 41 + (((-1)*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row1_64 X Y Z a hX hY hZ w hw
  have p30:=pivot1_30 X Y Z a hX hY hZ w hw
  have p43:=pivot1_43 X Y Z a hX hY hZ w hw
  have p50:=pivot1_50 X Y Z a hX hY hZ w hw
  have p57:=pivot1_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - ((1)/(X))*p43 - ((1*X)/(Y^2))*p50 - (((-1))/(X))*p57)*(1)

#print axioms pivot1_62

theorem pivot1_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1)/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row1_65 X Y Z a hX hY hZ w hw
  have p32:=pivot1_32 X Y Z a hX hY hZ w hw
  have p42:=pivot1_42 X Y Z a hX hY hZ w hw
  have p60:=pivot1_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot1_63

theorem pivot1_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ((1)/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row1_45 X Y Z a hX hY hZ w hw
  have p0:=pivot1_0 X Y Z a hX hY hZ w hw
  have p5:=pivot1_5 X Y Z a hX hY hZ w hw
  have p9:=pivot1_9 X Y Z a hX hY hZ w hw
  have p10:=pivot1_10 X Y Z a hX hY hZ w hw
  have p13:=pivot1_13 X Y Z a hX hY hZ w hw
  have p15:=pivot1_15 X Y Z a hX hY hZ w hw
  have p20:=pivot1_20 X Y Z a hX hY hZ w hw
  have p28:=pivot1_28 X Y Z a hX hY hZ w hw
  have p31:=pivot1_31 X Y Z a hX hY hZ w hw
  have p33:=pivot1_33 X Y Z a hX hY hZ w hw
  have p35:=pivot1_35 X Y Z a hX hY hZ w hw
  have p36:=pivot1_36 X Y Z a hX hY hZ w hw
  have p39:=pivot1_39 X Y Z a hX hY hZ w hw
  have p44:=pivot1_44 X Y Z a hX hY hZ w hw
  have p51:=pivot1_51 X Y Z a hX hY hZ w hw
  have p61:=pivot1_61 X Y Z a hX hY hZ w hw
  have p62:=pivot1_62 X Y Z a hX hY hZ w hw
  have p63:=pivot1_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - (((-1))/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - (((-1))/(X*Y^2))*p36 - (((-1)*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot1_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot2_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row2_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_0

theorem pivot2_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row2_0 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(X*Z))

#print axioms pivot2_1

theorem pivot2_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row2_1 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot2_2

theorem pivot2_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row2_2 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0)*(1)

#print axioms pivot2_3

theorem pivot2_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row2_3 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot2_4

theorem pivot2_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row2_4 X Y Z a hX hY hZ w hw
  have p4:=pivot2_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X*Y^2)*p4)*(1)

#print axioms pivot2_5

theorem pivot2_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row2_5 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0)*(1)

#print axioms pivot2_6

theorem pivot2_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row2_6 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Y^2*Z))

#print axioms pivot2_7

theorem pivot2_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row2_7 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot2_8

theorem pivot2_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row2_8 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6)*(1)

#print axioms pivot2_9

theorem pivot2_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row2_9 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Z))

#print axioms pivot2_10

theorem pivot2_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row2_10 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1)*(1)

#print axioms pivot2_11

theorem pivot2_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row2_11 X Y Z a hX hY hZ w hw
  have p4:=pivot2_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p4)*(1)

#print axioms pivot2_12

theorem pivot2_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row2_12 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p1)*(1)

#print axioms pivot2_13

theorem pivot2_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 9 + ((1*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row2_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_14

theorem pivot2_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 11 + ((1*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row2_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_15

theorem pivot2_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row2_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(X*Y^2))

#print axioms pivot2_16

theorem pivot2_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row2_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X*Z))

#print axioms pivot2_17

theorem pivot2_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row2_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot2_18

theorem pivot2_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row2_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_19

theorem pivot2_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row2_19 X Y Z a hX hY hZ w hw
  have p19:=pivot2_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p19)*(1)

#print axioms pivot2_20

theorem pivot2_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row2_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot2_21

theorem pivot2_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1)/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row2_21 X Y Z a hX hY hZ w hw
  have p19:=pivot2_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X))*p19)*(1)

#print axioms pivot2_22

theorem pivot2_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 37 + ((1)/(X*Y^2))*w 42=0 := by
  have h:=normalized_row2_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_23

theorem pivot2_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 38 + ((1*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row2_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_24

theorem pivot2_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 39 + ((1)/(X))*w 54=0 := by
  have h:=normalized_row2_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_25

theorem pivot2_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 22 + (((-1)*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row2_25 X Y Z a hX hY hZ w hw
  have p17:=pivot2_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p17)*(((-1)*Z)/(Y^2))

#print axioms pivot2_26

theorem pivot2_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row2_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot2_27

theorem pivot2_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row2_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot2_28

theorem pivot2_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 7 + ((1)/(X*Y^2))*w 12=0 := by
  have h:=normalized_row2_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot2_29

theorem pivot2_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 8 + ((1*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row2_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot2_30

theorem pivot2_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 24 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row2_30 X Y Z a hX hY hZ w hw
  have p14:=pivot2_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p14)*(1)

#print axioms pivot2_31

theorem pivot2_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row2_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_32

theorem pivot2_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 29 + ((1)/(X*Z))*w 44=0 := by
  have h:=normalized_row2_32 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p31)*(1)

#print axioms pivot2_33

theorem pivot2_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 31 + ((1)/(X*Y^2))*w 54=0 := by
  have h:=normalized_row2_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot2_34

theorem pivot2_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row2_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot2_35

theorem pivot2_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 42 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row2_47 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*((1*Y^2)/(Z))

#print axioms pivot2_36

theorem pivot2_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row2_48 X Y Z a hX hY hZ w hw
  have p15:=pivot2_15 X Y Z a hX hY hZ w hw
  have p16:=pivot2_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*(((-1)*X*Y^2)/(Z))

#print axioms pivot2_37

theorem pivot2_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row2_49 X Y Z a hX hY hZ w hw
  have p5:=pivot2_5 X Y Z a hX hY hZ w hw
  have p9:=pivot2_9 X Y Z a hX hY hZ w hw
  have p10:=pivot2_10 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot2_38

theorem pivot2_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row2_50 X Y Z a hX hY hZ w hw
  have p14:=pivot2_14 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - (((-1))/(X))*p37)*(1*X)

#print axioms pivot2_39

theorem pivot2_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row2_35 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  have p15:=pivot2_15 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot2_40

theorem pivot2_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 20 + ((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44=0 := by
  have h:=normalized_row2_36 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  have p16:=pivot2_16 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot2_41

theorem pivot2_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row2_51 X Y Z a hX hY hZ w hw
  have p5:=pivot2_5 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p5 - (1)*p39)*(1)

#print axioms pivot2_42

theorem pivot2_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row2_52 X Y Z a hX hY hZ w hw
  have p12:=pivot2_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p12)*(1)

#print axioms pivot2_43

theorem pivot2_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row2_53 X Y Z a hX hY hZ w hw
  have p11:=pivot2_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p11)*(1)

#print axioms pivot2_44

theorem pivot2_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row2_54 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot2_45

theorem pivot2_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row2_37 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  have p5:=pivot2_5 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  have p9:=pivot2_9 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p14:=pivot2_14 X Y Z a hX hY hZ w hw
  have p17:=pivot2_17 X Y Z a hX hY hZ w hw
  have p22:=pivot2_22 X Y Z a hX hY hZ w hw
  have p25:=pivot2_25 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p45:=pivot2_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0 - (1)*p1 - ((1)/(X))*p5 - (1)*p6 - ((1)/(X))*p9 - ((1)/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - (((-1)*Y^2)/(X*Z))*p26 - ((1)/(X))*p31 - ((1)/(X))*p37 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot2_46

theorem pivot2_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 10 + ((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row2_55 X Y Z a hX hY hZ w hw
  have p24:=pivot2_24 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  have p45:=pivot2_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*X)/(Y^2))*p45)*((-1)*X)

#print axioms pivot2_47

theorem pivot2_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 12 + ((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row2_38 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p47:=pivot2_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (((-1))/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot2_48

theorem pivot2_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row2_39 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot2_49

theorem pivot2_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 21 + ((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row2_56 X Y Z a hX hY hZ w hw
  have p18:=pivot2_18 X Y Z a hX hY hZ w hw
  have p23:=pivot2_23 X Y Z a hX hY hZ w hw
  have p30:=pivot2_30 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - (((-1))/(X))*p30 - (((-1))/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot2_50

theorem pivot2_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 23 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row2_40 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p46:=pivot2_46 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - ((1)/(X*Z))*p26 - ((1)/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot2_51

theorem pivot2_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 43 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row2_41 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot2_52

theorem pivot2_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 26 + ((1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_58 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p18:=pivot2_18 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot2_53

theorem pivot2_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 13 + ((1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_59 X Y Z a hX hY hZ w hw
  have p40:=pivot2_40 X Y Z a hX hY hZ w hw
  have p53:=pivot2_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - (((-1))/(X))*p53)*(1)

#print axioms pivot2_54

theorem pivot2_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row2_60 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p53:=pivot2_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - (((-1))/(X*Y^2))*p38 - ((1)/(X*Y^2))*p48 - (1)*p53)*((-1)*X)

#print axioms pivot2_55

theorem pivot2_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 19 + ((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_61 X Y Z a hX hY hZ w hw
  have p24:=pivot2_24 X Y Z a hX hY hZ w hw
  have p45:=pivot2_45 X Y Z a hX hY hZ w hw
  have p55:=pivot2_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot2_56

theorem pivot2_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row2_62 X Y Z a hX hY hZ w hw
  have p22:=pivot2_22 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p46:=pivot2_46 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - (((-1))/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot2_57

theorem pivot2_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 25 + ((1)/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-2))/(Z) + 1 + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_42 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p5:=pivot2_5 X Y Z a hX hY hZ w hw
  have p9:=pivot2_9 X Y Z a hX hY hZ w hw
  have p10:=pivot2_10 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p16:=pivot2_16 X Y Z a hX hY hZ w hw
  have p21:=pivot2_21 X Y Z a hX hY hZ w hw
  have p23:=pivot2_23 X Y Z a hX hY hZ w hw
  have p29:=pivot2_29 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  have p34:=pivot2_34 X Y Z a hX hY hZ w hw
  have p37:=pivot2_37 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  have p52:=pivot2_52 X Y Z a hX hY hZ w hw
  have p54:=pivot2_54 X Y Z a hX hY hZ w hw
  have p56:=pivot2_56 X Y Z a hX hY hZ w hw
  have p57:=pivot2_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - ((1)/(X*Y^2))*p31 - (1)*p34 - (((-1)*Z)/(X*Y^2))*p37 - ((1*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot2_58

theorem pivot2_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 40 + ((-1) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_43 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  have p11:=pivot2_11 X Y Z a hX hY hZ w hw
  have p17:=pivot2_17 X Y Z a hX hY hZ w hw
  have p18:=pivot2_18 X Y Z a hX hY hZ w hw
  have p22:=pivot2_22 X Y Z a hX hY hZ w hw
  have p25:=pivot2_25 X Y Z a hX hY hZ w hw
  have p26:=pivot2_26 X Y Z a hX hY hZ w hw
  have p27:=pivot2_27 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p40:=pivot2_40 X Y Z a hX hY hZ w hw
  have p43:=pivot2_43 X Y Z a hX hY hZ w hw
  have p45:=pivot2_45 X Y Z a hX hY hZ w hw
  have p47:=pivot2_47 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  have p55:=pivot2_55 X Y Z a hX hY hZ w hw
  have p57:=pivot2_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p11 - ((1*X)/(Y^2))*p17 - (1)*p18 - ((1*X)/(Y^2))*p22 - ((1*X)/(Y^2))*p25 - (((-1))/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - (((-1))/(Y^2) + (1*Z)/(Y^2))*p36 - (1)*p40 - (1)*p43 - ((1*X)/(Y^2))*p45 - (1)*p47 - (((-1))/(Y^2))*p48 - ((1*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot2_59

theorem pivot2_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 14 + (((-1)*X)/(Y^2*Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row2_63 X Y Z a hX hY hZ w hw
  have p29:=pivot2_29 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p59:=pivot2_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - (((-1))/(X*Y^2))*p48 - (1)*p59)*((-1)*X)

#print axioms pivot2_60

theorem pivot2_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row2_44 X Y Z a hX hY hZ w hw
  have p1:=pivot2_1 X Y Z a hX hY hZ w hw
  have p3:=pivot2_3 X Y Z a hX hY hZ w hw
  have p6:=pivot2_6 X Y Z a hX hY hZ w hw
  have p12:=pivot2_12 X Y Z a hX hY hZ w hw
  have p14:=pivot2_14 X Y Z a hX hY hZ w hw
  have p19:=pivot2_19 X Y Z a hX hY hZ w hw
  have p22:=pivot2_22 X Y Z a hX hY hZ w hw
  have p24:=pivot2_24 X Y Z a hX hY hZ w hw
  have p25:=pivot2_25 X Y Z a hX hY hZ w hw
  have p30:=pivot2_30 X Y Z a hX hY hZ w hw
  have p38:=pivot2_38 X Y Z a hX hY hZ w hw
  have p41:=pivot2_41 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p46:=pivot2_46 X Y Z a hX hY hZ w hw
  have p48:=pivot2_48 X Y Z a hX hY hZ w hw
  have p49:=pivot2_49 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  have p53:=pivot2_53 X Y Z a hX hY hZ w hw
  have p60:=pivot2_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p12 - ((1*X)/(Y^2))*p14 - (1)*p19 - ((1*X)/(Y^2))*p22 - (1)*p24 - ((1*X)/(Y^2))*p25 - (1)*p30 - (((-1))/(Y^2))*p38 - (1)*p41 - ((1*X)/(Y^2))*p42 - ((1*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - (((-1)*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot2_61

theorem pivot2_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (1)*w 41 + (((-1)*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row2_64 X Y Z a hX hY hZ w hw
  have p30:=pivot2_30 X Y Z a hX hY hZ w hw
  have p43:=pivot2_43 X Y Z a hX hY hZ w hw
  have p50:=pivot2_50 X Y Z a hX hY hZ w hw
  have p57:=pivot2_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - (((-1))/(X))*p43 - (((-1)*X)/(Y^2))*p50 - ((1)/(X))*p57)*(1)

#print axioms pivot2_62

theorem pivot2_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row2_65 X Y Z a hX hY hZ w hw
  have p32:=pivot2_32 X Y Z a hX hY hZ w hw
  have p42:=pivot2_42 X Y Z a hX hY hZ w hw
  have p60:=pivot2_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot2_63

theorem pivot2_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    (((-1))/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row2_45 X Y Z a hX hY hZ w hw
  have p0:=pivot2_0 X Y Z a hX hY hZ w hw
  have p5:=pivot2_5 X Y Z a hX hY hZ w hw
  have p9:=pivot2_9 X Y Z a hX hY hZ w hw
  have p10:=pivot2_10 X Y Z a hX hY hZ w hw
  have p13:=pivot2_13 X Y Z a hX hY hZ w hw
  have p15:=pivot2_15 X Y Z a hX hY hZ w hw
  have p20:=pivot2_20 X Y Z a hX hY hZ w hw
  have p28:=pivot2_28 X Y Z a hX hY hZ w hw
  have p31:=pivot2_31 X Y Z a hX hY hZ w hw
  have p33:=pivot2_33 X Y Z a hX hY hZ w hw
  have p35:=pivot2_35 X Y Z a hX hY hZ w hw
  have p36:=pivot2_36 X Y Z a hX hY hZ w hw
  have p39:=pivot2_39 X Y Z a hX hY hZ w hw
  have p44:=pivot2_44 X Y Z a hX hY hZ w hw
  have p51:=pivot2_51 X Y Z a hX hY hZ w hw
  have p61:=pivot2_61 X Y Z a hX hY hZ w hw
  have p62:=pivot2_62 X Y Z a hX hY hZ w hw
  have p63:=pivot2_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - ((1)/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - ((1)/(X*Y^2))*p36 - (((-1)*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot2_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot3_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row3_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_0

theorem pivot3_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row3_0 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*((1)/(X*Z))

#print axioms pivot3_1

theorem pivot3_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row3_1 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot3_2

theorem pivot3_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row3_2 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0)*(1)

#print axioms pivot3_3

theorem pivot3_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row3_3 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2*Z))*p0)*(1)

#print axioms pivot3_4

theorem pivot3_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row3_4 X Y Z a hX hY hZ w hw
  have p4:=pivot3_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X*Y^2)*p4)*(1)

#print axioms pivot3_5

theorem pivot3_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row3_5 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0)*(1)

#print axioms pivot3_6

theorem pivot3_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row3_6 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Y^2*Z))

#print axioms pivot3_7

theorem pivot3_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row3_7 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot3_8

theorem pivot3_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row3_8 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6)*(1)

#print axioms pivot3_9

theorem pivot3_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row3_9 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*((1*X)/(Z))

#print axioms pivot3_10

theorem pivot3_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row3_10 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1)*(1)

#print axioms pivot3_11

theorem pivot3_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row3_11 X Y Z a hX hY hZ w hw
  have p4:=pivot3_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p4)*(1)

#print axioms pivot3_12

theorem pivot3_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row3_12 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p1)*(1)

#print axioms pivot3_13

theorem pivot3_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 9 + ((1*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row3_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_14

theorem pivot3_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 11 + ((1*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row3_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_15

theorem pivot3_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row3_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Z)/(X*Y^2))

#print axioms pivot3_16

theorem pivot3_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row3_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*Y^2)/(X*Z))

#print axioms pivot3_17

theorem pivot3_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row3_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot3_18

theorem pivot3_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row3_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_19

theorem pivot3_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row3_19 X Y Z a hX hY hZ w hw
  have p19:=pivot3_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p19)*(1)

#print axioms pivot3_20

theorem pivot3_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row3_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot3_21

theorem pivot3_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1)/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row3_21 X Y Z a hX hY hZ w hw
  have p19:=pivot3_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X))*p19)*(1)

#print axioms pivot3_22

theorem pivot3_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 37 + ((1)/(X*Y^2))*w 42=0 := by
  have h:=normalized_row3_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_23

theorem pivot3_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 38 + ((1*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row3_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_24

theorem pivot3_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 39 + ((1)/(X))*w 54=0 := by
  have h:=normalized_row3_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_25

theorem pivot3_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 22 + (((-1)*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row3_25 X Y Z a hX hY hZ w hw
  have p17:=pivot3_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p17)*(((-1)*Z)/(Y^2))

#print axioms pivot3_26

theorem pivot3_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row3_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot3_27

theorem pivot3_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row3_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot3_28

theorem pivot3_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 7 + ((1)/(X*Y^2))*w 12=0 := by
  have h:=normalized_row3_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot3_29

theorem pivot3_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 8 + ((1*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row3_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot3_30

theorem pivot3_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 24 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row3_30 X Y Z a hX hY hZ w hw
  have p14:=pivot3_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p14)*(1)

#print axioms pivot3_31

theorem pivot3_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row3_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_32

theorem pivot3_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 29 + ((1)/(X*Z))*w 44=0 := by
  have h:=normalized_row3_32 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p31)*(1)

#print axioms pivot3_33

theorem pivot3_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 31 + ((1)/(X*Y^2))*w 54=0 := by
  have h:=normalized_row3_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot3_34

theorem pivot3_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row3_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot3_35

theorem pivot3_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 42 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row3_47 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*((1*Y^2)/(Z))

#print axioms pivot3_36

theorem pivot3_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row3_48 X Y Z a hX hY hZ w hw
  have p15:=pivot3_15 X Y Z a hX hY hZ w hw
  have p16:=pivot3_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*(((-1)*X*Y^2)/(Z))

#print axioms pivot3_37

theorem pivot3_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row3_49 X Y Z a hX hY hZ w hw
  have p5:=pivot3_5 X Y Z a hX hY hZ w hw
  have p9:=pivot3_9 X Y Z a hX hY hZ w hw
  have p10:=pivot3_10 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot3_38

theorem pivot3_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row3_50 X Y Z a hX hY hZ w hw
  have p14:=pivot3_14 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - (((-1))/(X))*p37)*(1*X)

#print axioms pivot3_39

theorem pivot3_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row3_35 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  have p15:=pivot3_15 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot3_40

theorem pivot3_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 20 + ((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44=0 := by
  have h:=normalized_row3_36 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  have p16:=pivot3_16 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Z))*p6 - ((1*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot3_41

theorem pivot3_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row3_51 X Y Z a hX hY hZ w hw
  have p5:=pivot3_5 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p5 - (1)*p39)*(1)

#print axioms pivot3_42

theorem pivot3_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row3_52 X Y Z a hX hY hZ w hw
  have p12:=pivot3_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p12)*(1)

#print axioms pivot3_43

theorem pivot3_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row3_53 X Y Z a hX hY hZ w hw
  have p11:=pivot3_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p11)*(1)

#print axioms pivot3_44

theorem pivot3_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row3_54 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot3_45

theorem pivot3_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row3_37 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  have p5:=pivot3_5 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  have p9:=pivot3_9 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p14:=pivot3_14 X Y Z a hX hY hZ w hw
  have p17:=pivot3_17 X Y Z a hX hY hZ w hw
  have p22:=pivot3_22 X Y Z a hX hY hZ w hw
  have p25:=pivot3_25 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0 - (1)*p1 - (((-1))/(X))*p5 - (1)*p6 - (((-1))/(X))*p9 - (((-1))/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - (((-1)*Y^2)/(X*Z))*p26 - (((-1))/(X))*p31 - (((-2))/(X))*p36 - (((-1))/(X))*p37 - (((-2))/(X))*p38 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot3_46

theorem pivot3_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 10 + ((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row3_55 X Y Z a hX hY hZ w hw
  have p24:=pivot3_24 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*X)/(Y^2))*p45)*((-1)*X)

#print axioms pivot3_47

theorem pivot3_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 12 + ((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row3_38 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p47:=pivot3_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (((-1))/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot3_48

theorem pivot3_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row3_39 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot3_49

theorem pivot3_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 21 + ((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row3_56 X Y Z a hX hY hZ w hw
  have p18:=pivot3_18 X Y Z a hX hY hZ w hw
  have p23:=pivot3_23 X Y Z a hX hY hZ w hw
  have p30:=pivot3_30 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - (((-1))/(X))*p30 - (((-1))/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot3_50

theorem pivot3_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 23 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row3_40 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - ((1)/(X*Z))*p26 - ((1)/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot3_51

theorem pivot3_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 43 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row3_41 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot3_52

theorem pivot3_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 26 + ((1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_58 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p18:=pivot3_18 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot3_53

theorem pivot3_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 13 + ((1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_59 X Y Z a hX hY hZ w hw
  have p40:=pivot3_40 X Y Z a hX hY hZ w hw
  have p53:=pivot3_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - (((-1))/(X))*p53)*(1)

#print axioms pivot3_54

theorem pivot3_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row3_60 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p53:=pivot3_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - (((-1))/(X*Y^2))*p38 - ((1)/(X*Y^2))*p48 - (1)*p53)*((-1)*X)

#print axioms pivot3_55

theorem pivot3_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 19 + ((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_61 X Y Z a hX hY hZ w hw
  have p24:=pivot3_24 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  have p55:=pivot3_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot3_56

theorem pivot3_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row3_62 X Y Z a hX hY hZ w hw
  have p22:=pivot3_22 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - (((-1))/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot3_57

theorem pivot3_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 25 + ((2)/(X*Z) + (1)/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + 1 + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_42 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p5:=pivot3_5 X Y Z a hX hY hZ w hw
  have p9:=pivot3_9 X Y Z a hX hY hZ w hw
  have p10:=pivot3_10 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p16:=pivot3_16 X Y Z a hX hY hZ w hw
  have p21:=pivot3_21 X Y Z a hX hY hZ w hw
  have p23:=pivot3_23 X Y Z a hX hY hZ w hw
  have p29:=pivot3_29 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  have p34:=pivot3_34 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p37:=pivot3_37 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  have p52:=pivot3_52 X Y Z a hX hY hZ w hw
  have p54:=pivot3_54 X Y Z a hX hY hZ w hw
  have p56:=pivot3_56 X Y Z a hX hY hZ w hw
  have p57:=pivot3_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - (((-1))/(X*Y^2))*p31 - (1)*p34 - (((-2))/(X*Y^2))*p36 - (((-2))/(X*Y^2) + ((-1)*Z)/(X*Y^2))*p37 - (((-2))/(X*Y^2))*p38 - ((2)/(X*Y^2) + (1*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot3_58

theorem pivot3_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 40 + (((-2))/(Z) + (-1) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_43 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  have p11:=pivot3_11 X Y Z a hX hY hZ w hw
  have p17:=pivot3_17 X Y Z a hX hY hZ w hw
  have p18:=pivot3_18 X Y Z a hX hY hZ w hw
  have p22:=pivot3_22 X Y Z a hX hY hZ w hw
  have p25:=pivot3_25 X Y Z a hX hY hZ w hw
  have p26:=pivot3_26 X Y Z a hX hY hZ w hw
  have p27:=pivot3_27 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p40:=pivot3_40 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p43:=pivot3_43 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  have p47:=pivot3_47 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  have p55:=pivot3_55 X Y Z a hX hY hZ w hw
  have p57:=pivot3_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p11 - (((-1)*X)/(Y^2))*p17 - (1)*p18 - (((-1)*X)/(Y^2))*p22 - (((-1)*X)/(Y^2))*p25 - ((1)/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - ((1)/(Y^2) + (1*Z)/(Y^2))*p36 - ((2)/(Y^2))*p38 - (1)*p40 - (((-2)*X)/(Y^2))*p42 - (1)*p43 - (((-1)*X)/(Y^2))*p45 - (((-2)*X)/(Y^2))*p46 - (1)*p47 - (((-1))/(Y^2))*p48 - ((1*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot3_59

theorem pivot3_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 14 + (((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row3_63 X Y Z a hX hY hZ w hw
  have p29:=pivot3_29 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p59:=pivot3_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - (((-1))/(X*Y^2))*p48 - (1)*p59)*((-1)*X)

#print axioms pivot3_60

theorem pivot3_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ((2)/(Z) + 1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row3_44 X Y Z a hX hY hZ w hw
  have p1:=pivot3_1 X Y Z a hX hY hZ w hw
  have p3:=pivot3_3 X Y Z a hX hY hZ w hw
  have p6:=pivot3_6 X Y Z a hX hY hZ w hw
  have p12:=pivot3_12 X Y Z a hX hY hZ w hw
  have p14:=pivot3_14 X Y Z a hX hY hZ w hw
  have p19:=pivot3_19 X Y Z a hX hY hZ w hw
  have p22:=pivot3_22 X Y Z a hX hY hZ w hw
  have p24:=pivot3_24 X Y Z a hX hY hZ w hw
  have p25:=pivot3_25 X Y Z a hX hY hZ w hw
  have p30:=pivot3_30 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p41:=pivot3_41 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p45:=pivot3_45 X Y Z a hX hY hZ w hw
  have p46:=pivot3_46 X Y Z a hX hY hZ w hw
  have p48:=pivot3_48 X Y Z a hX hY hZ w hw
  have p49:=pivot3_49 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  have p53:=pivot3_53 X Y Z a hX hY hZ w hw
  have p60:=pivot3_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p12 - (((-1)*X)/(Y^2))*p14 - (1)*p19 - (((-1)*X)/(Y^2))*p22 - (1)*p24 - (((-1)*X)/(Y^2))*p25 - (1)*p30 - ((1)/(Y^2))*p38 - (1)*p41 - (((-1)*X)/(Y^2))*p42 - (((-2)*X)/(Y^2))*p45 - (((-1)*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - (((-1)*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot3_61

theorem pivot3_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (1)*w 41 + (((-1)*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row3_64 X Y Z a hX hY hZ w hw
  have p30:=pivot3_30 X Y Z a hX hY hZ w hw
  have p43:=pivot3_43 X Y Z a hX hY hZ w hw
  have p50:=pivot3_50 X Y Z a hX hY hZ w hw
  have p57:=pivot3_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - (((-1))/(X))*p43 - (((-1)*X)/(Y^2))*p50 - ((1)/(X))*p57)*(1)

#print axioms pivot3_62

theorem pivot3_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-1))/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row3_65 X Y Z a hX hY hZ w hw
  have p32:=pivot3_32 X Y Z a hX hY hZ w hw
  have p42:=pivot3_42 X Y Z a hX hY hZ w hw
  have p60:=pivot3_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot3_63

theorem pivot3_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    (((-2))/(X*Z) + ((-1))/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row3_45 X Y Z a hX hY hZ w hw
  have p0:=pivot3_0 X Y Z a hX hY hZ w hw
  have p5:=pivot3_5 X Y Z a hX hY hZ w hw
  have p9:=pivot3_9 X Y Z a hX hY hZ w hw
  have p10:=pivot3_10 X Y Z a hX hY hZ w hw
  have p13:=pivot3_13 X Y Z a hX hY hZ w hw
  have p15:=pivot3_15 X Y Z a hX hY hZ w hw
  have p20:=pivot3_20 X Y Z a hX hY hZ w hw
  have p28:=pivot3_28 X Y Z a hX hY hZ w hw
  have p31:=pivot3_31 X Y Z a hX hY hZ w hw
  have p33:=pivot3_33 X Y Z a hX hY hZ w hw
  have p35:=pivot3_35 X Y Z a hX hY hZ w hw
  have p36:=pivot3_36 X Y Z a hX hY hZ w hw
  have p38:=pivot3_38 X Y Z a hX hY hZ w hw
  have p39:=pivot3_39 X Y Z a hX hY hZ w hw
  have p44:=pivot3_44 X Y Z a hX hY hZ w hw
  have p51:=pivot3_51 X Y Z a hX hY hZ w hw
  have p61:=pivot3_61 X Y Z a hX hY hZ w hw
  have p62:=pivot3_62 X Y Z a hX hY hZ w hw
  have p63:=pivot3_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - (((-1))/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - (((-1))/(X*Y^2))*p36 - (((-2))/(X*Y^2))*p38 - (((-2))/(X*Y^2) + ((-1)*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot3_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot4_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row4_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_0

theorem pivot4_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row4_0 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X*Z))

#print axioms pivot4_1

theorem pivot4_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row4_1 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot4_2

theorem pivot4_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row4_2 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0)*(1)

#print axioms pivot4_3

theorem pivot4_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row4_3 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot4_4

theorem pivot4_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row4_4 X Y Z a hX hY hZ w hw
  have p4:=pivot4_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X*Y^2)*p4)*(1)

#print axioms pivot4_5

theorem pivot4_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row4_5 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0)*(1)

#print axioms pivot4_6

theorem pivot4_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row4_6 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Y^2*Z))

#print axioms pivot4_7

theorem pivot4_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row4_7 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot4_8

theorem pivot4_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row4_8 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6)*(1)

#print axioms pivot4_9

theorem pivot4_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row4_9 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Z))

#print axioms pivot4_10

theorem pivot4_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row4_10 X Y Z a hX hY hZ w hw
  have p1:=pivot4_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1)*(1)

#print axioms pivot4_11

theorem pivot4_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row4_11 X Y Z a hX hY hZ w hw
  have p4:=pivot4_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p4)*(1)

#print axioms pivot4_12

theorem pivot4_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row4_12 X Y Z a hX hY hZ w hw
  have p1:=pivot4_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p1)*(1)

#print axioms pivot4_13

theorem pivot4_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row4_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_14

theorem pivot4_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 11 + (((-1)*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row4_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_15

theorem pivot4_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row4_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X*Y^2))

#print axioms pivot4_16

theorem pivot4_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row4_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X*Z))

#print axioms pivot4_17

theorem pivot4_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row4_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot4_18

theorem pivot4_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row4_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_19

theorem pivot4_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row4_19 X Y Z a hX hY hZ w hw
  have p19:=pivot4_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p19)*(1)

#print axioms pivot4_20

theorem pivot4_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row4_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot4_21

theorem pivot4_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row4_21 X Y Z a hX hY hZ w hw
  have p19:=pivot4_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X))*p19)*(1)

#print axioms pivot4_22

theorem pivot4_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 37 + (((-1))/(X*Y^2))*w 42=0 := by
  have h:=normalized_row4_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_23

theorem pivot4_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 38 + (((-1)*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row4_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_24

theorem pivot4_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 39 + (((-1))/(X))*w 54=0 := by
  have h:=normalized_row4_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_25

theorem pivot4_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 22 + (((-1)*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row4_25 X Y Z a hX hY hZ w hw
  have p17:=pivot4_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p17)*(((-1)*Z)/(Y^2))

#print axioms pivot4_26

theorem pivot4_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row4_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot4_27

theorem pivot4_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row4_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot4_28

theorem pivot4_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 7 + (((-1))/(X*Y^2))*w 12=0 := by
  have h:=normalized_row4_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot4_29

theorem pivot4_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 8 + (((-1)*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row4_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot4_30

theorem pivot4_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 24 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row4_30 X Y Z a hX hY hZ w hw
  have p14:=pivot4_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p14)*(1)

#print axioms pivot4_31

theorem pivot4_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row4_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_32

theorem pivot4_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 29 + (((-1))/(X*Z))*w 44=0 := by
  have h:=normalized_row4_32 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p31)*(1)

#print axioms pivot4_33

theorem pivot4_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 31 + (((-1))/(X*Y^2))*w 54=0 := by
  have h:=normalized_row4_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot4_34

theorem pivot4_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 5 + (((-1))/(X*Y^2))*w 48=0 := by
  have h:=normalized_row4_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot4_35

theorem pivot4_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 42 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row4_47 X Y Z a hX hY hZ w hw
  have p26:=pivot4_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*((1*Y^2)/(Z))

#print axioms pivot4_36

theorem pivot4_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row4_48 X Y Z a hX hY hZ w hw
  have p15:=pivot4_15 X Y Z a hX hY hZ w hw
  have p16:=pivot4_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*((1*X*Y^2)/(Z))

#print axioms pivot4_37

theorem pivot4_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row4_49 X Y Z a hX hY hZ w hw
  have p5:=pivot4_5 X Y Z a hX hY hZ w hw
  have p9:=pivot4_9 X Y Z a hX hY hZ w hw
  have p10:=pivot4_10 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot4_38

theorem pivot4_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row4_50 X Y Z a hX hY hZ w hw
  have p14:=pivot4_14 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - ((1)/(X))*p37)*((-1)*X)

#print axioms pivot4_39

theorem pivot4_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row4_35 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  have p15:=pivot4_15 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot4_40

theorem pivot4_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 20 + ((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44=0 := by
  have h:=normalized_row4_36 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  have p16:=pivot4_16 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot4_41

theorem pivot4_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row4_51 X Y Z a hX hY hZ w hw
  have p5:=pivot4_5 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p5 - (1)*p39)*(1)

#print axioms pivot4_42

theorem pivot4_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row4_52 X Y Z a hX hY hZ w hw
  have p12:=pivot4_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p12)*(1)

#print axioms pivot4_43

theorem pivot4_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row4_53 X Y Z a hX hY hZ w hw
  have p11:=pivot4_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p11)*(1)

#print axioms pivot4_44

theorem pivot4_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row4_54 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot4_45

theorem pivot4_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row4_37 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p1:=pivot4_1 X Y Z a hX hY hZ w hw
  have p5:=pivot4_5 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  have p9:=pivot4_9 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p14:=pivot4_14 X Y Z a hX hY hZ w hw
  have p17:=pivot4_17 X Y Z a hX hY hZ w hw
  have p22:=pivot4_22 X Y Z a hX hY hZ w hw
  have p25:=pivot4_25 X Y Z a hX hY hZ w hw
  have p26:=pivot4_26 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  have p42:=pivot4_42 X Y Z a hX hY hZ w hw
  have p45:=pivot4_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0 - (1)*p1 - (((-1))/(X))*p5 - (1)*p6 - (((-1))/(X))*p9 - (((-1))/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - ((1*Y^2)/(X*Z))*p26 - (((-1))/(X))*p31 - (((-1))/(X))*p37 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot4_46

theorem pivot4_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 10 + ((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row4_55 X Y Z a hX hY hZ w hw
  have p24:=pivot4_24 X Y Z a hX hY hZ w hw
  have p35:=pivot4_35 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  have p45:=pivot4_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - ((1)/(X*Y^2))*p39 - ((1*X)/(Y^2))*p45)*(1*X)

#print axioms pivot4_47

theorem pivot4_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row4_38 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p26:=pivot4_26 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p38:=pivot4_38 X Y Z a hX hY hZ w hw
  have p47:=pivot4_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (((-1))/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot4_48

theorem pivot4_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row4_39 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot4_49

theorem pivot4_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row4_56 X Y Z a hX hY hZ w hw
  have p18:=pivot4_18 X Y Z a hX hY hZ w hw
  have p23:=pivot4_23 X Y Z a hX hY hZ w hw
  have p30:=pivot4_30 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p38:=pivot4_38 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - ((1)/(X))*p30 - ((1)/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot4_50

theorem pivot4_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 23 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row4_40 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p26:=pivot4_26 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p46:=pivot4_46 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (((-1))/(X*Z))*p26 - (((-1))/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot4_51

theorem pivot4_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 43 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row4_41 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot4_52

theorem pivot4_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 26 + ((1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_58 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p18:=pivot4_18 X Y Z a hX hY hZ w hw
  have p38:=pivot4_38 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot4_53

theorem pivot4_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 13 + (((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_59 X Y Z a hX hY hZ w hw
  have p40:=pivot4_40 X Y Z a hX hY hZ w hw
  have p53:=pivot4_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - ((1)/(X))*p53)*(1)

#print axioms pivot4_54

theorem pivot4_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row4_60 X Y Z a hX hY hZ w hw
  have p28:=pivot4_28 X Y Z a hX hY hZ w hw
  have p38:=pivot4_38 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  have p53:=pivot4_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - ((1)/(X*Y^2))*p38 - (((-1))/(X*Y^2))*p48 - (1)*p53)*(1*X)

#print axioms pivot4_55

theorem pivot4_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 19 + ((1)/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_61 X Y Z a hX hY hZ w hw
  have p24:=pivot4_24 X Y Z a hX hY hZ w hw
  have p45:=pivot4_45 X Y Z a hX hY hZ w hw
  have p55:=pivot4_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot4_56

theorem pivot4_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    ((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row4_62 X Y Z a hX hY hZ w hw
  have p22:=pivot4_22 X Y Z a hX hY hZ w hw
  have p35:=pivot4_35 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  have p42:=pivot4_42 X Y Z a hX hY hZ w hw
  have p46:=pivot4_46 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - ((1)/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - ((1)/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot4_57

theorem pivot4_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 25 + (((-1))/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-2))/(Z) + 1 + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_42 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p5:=pivot4_5 X Y Z a hX hY hZ w hw
  have p9:=pivot4_9 X Y Z a hX hY hZ w hw
  have p10:=pivot4_10 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p16:=pivot4_16 X Y Z a hX hY hZ w hw
  have p21:=pivot4_21 X Y Z a hX hY hZ w hw
  have p23:=pivot4_23 X Y Z a hX hY hZ w hw
  have p29:=pivot4_29 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  have p34:=pivot4_34 X Y Z a hX hY hZ w hw
  have p37:=pivot4_37 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  have p52:=pivot4_52 X Y Z a hX hY hZ w hw
  have p54:=pivot4_54 X Y Z a hX hY hZ w hw
  have p56:=pivot4_56 X Y Z a hX hY hZ w hw
  have p57:=pivot4_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - (((-1))/(X*Y^2))*p31 - (1)*p34 - ((1*Z)/(X*Y^2))*p37 - (((-1)*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot4_58

theorem pivot4_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 40 + ((-1) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_43 X Y Z a hX hY hZ w hw
  have p1:=pivot4_1 X Y Z a hX hY hZ w hw
  have p3:=pivot4_3 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  have p11:=pivot4_11 X Y Z a hX hY hZ w hw
  have p17:=pivot4_17 X Y Z a hX hY hZ w hw
  have p18:=pivot4_18 X Y Z a hX hY hZ w hw
  have p22:=pivot4_22 X Y Z a hX hY hZ w hw
  have p25:=pivot4_25 X Y Z a hX hY hZ w hw
  have p26:=pivot4_26 X Y Z a hX hY hZ w hw
  have p27:=pivot4_27 X Y Z a hX hY hZ w hw
  have p32:=pivot4_32 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p40:=pivot4_40 X Y Z a hX hY hZ w hw
  have p43:=pivot4_43 X Y Z a hX hY hZ w hw
  have p45:=pivot4_45 X Y Z a hX hY hZ w hw
  have p47:=pivot4_47 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  have p55:=pivot4_55 X Y Z a hX hY hZ w hw
  have p57:=pivot4_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p11 - (((-1)*X)/(Y^2))*p17 - (1)*p18 - (((-1)*X)/(Y^2))*p22 - (((-1)*X)/(Y^2))*p25 - (((-1))/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - (((-1))/(Y^2) + (1*Z)/(Y^2))*p36 - (1)*p40 - (1)*p43 - (((-1)*X)/(Y^2))*p45 - (1)*p47 - (((-1))/(Y^2))*p48 - (((-1)*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot4_59

theorem pivot4_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 14 + ((1*X)/(Y^2*Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row4_63 X Y Z a hX hY hZ w hw
  have p29:=pivot4_29 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  have p59:=pivot4_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - ((1)/(X*Y^2))*p48 - (1)*p59)*(1*X)

#print axioms pivot4_60

theorem pivot4_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row4_44 X Y Z a hX hY hZ w hw
  have p1:=pivot4_1 X Y Z a hX hY hZ w hw
  have p3:=pivot4_3 X Y Z a hX hY hZ w hw
  have p6:=pivot4_6 X Y Z a hX hY hZ w hw
  have p12:=pivot4_12 X Y Z a hX hY hZ w hw
  have p14:=pivot4_14 X Y Z a hX hY hZ w hw
  have p19:=pivot4_19 X Y Z a hX hY hZ w hw
  have p22:=pivot4_22 X Y Z a hX hY hZ w hw
  have p24:=pivot4_24 X Y Z a hX hY hZ w hw
  have p25:=pivot4_25 X Y Z a hX hY hZ w hw
  have p30:=pivot4_30 X Y Z a hX hY hZ w hw
  have p38:=pivot4_38 X Y Z a hX hY hZ w hw
  have p41:=pivot4_41 X Y Z a hX hY hZ w hw
  have p42:=pivot4_42 X Y Z a hX hY hZ w hw
  have p46:=pivot4_46 X Y Z a hX hY hZ w hw
  have p48:=pivot4_48 X Y Z a hX hY hZ w hw
  have p49:=pivot4_49 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  have p53:=pivot4_53 X Y Z a hX hY hZ w hw
  have p60:=pivot4_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p12 - (((-1)*X)/(Y^2))*p14 - (1)*p19 - (((-1)*X)/(Y^2))*p22 - (1)*p24 - (((-1)*X)/(Y^2))*p25 - (1)*p30 - (((-1))/(Y^2))*p38 - (1)*p41 - (((-1)*X)/(Y^2))*p42 - (((-1)*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - ((1*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot4_61

theorem pivot4_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (1)*w 41 + ((1*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row4_64 X Y Z a hX hY hZ w hw
  have p30:=pivot4_30 X Y Z a hX hY hZ w hw
  have p43:=pivot4_43 X Y Z a hX hY hZ w hw
  have p50:=pivot4_50 X Y Z a hX hY hZ w hw
  have p57:=pivot4_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - ((1)/(X))*p43 - ((1*X)/(Y^2))*p50 - (((-1))/(X))*p57)*(1)

#print axioms pivot4_62

theorem pivot4_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    (((-1))/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row4_65 X Y Z a hX hY hZ w hw
  have p32:=pivot4_32 X Y Z a hX hY hZ w hw
  have p42:=pivot4_42 X Y Z a hX hY hZ w hw
  have p60:=pivot4_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot4_63

theorem pivot4_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    ((1)/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row4_45 X Y Z a hX hY hZ w hw
  have p0:=pivot4_0 X Y Z a hX hY hZ w hw
  have p5:=pivot4_5 X Y Z a hX hY hZ w hw
  have p9:=pivot4_9 X Y Z a hX hY hZ w hw
  have p10:=pivot4_10 X Y Z a hX hY hZ w hw
  have p13:=pivot4_13 X Y Z a hX hY hZ w hw
  have p15:=pivot4_15 X Y Z a hX hY hZ w hw
  have p20:=pivot4_20 X Y Z a hX hY hZ w hw
  have p28:=pivot4_28 X Y Z a hX hY hZ w hw
  have p31:=pivot4_31 X Y Z a hX hY hZ w hw
  have p33:=pivot4_33 X Y Z a hX hY hZ w hw
  have p35:=pivot4_35 X Y Z a hX hY hZ w hw
  have p36:=pivot4_36 X Y Z a hX hY hZ w hw
  have p39:=pivot4_39 X Y Z a hX hY hZ w hw
  have p44:=pivot4_44 X Y Z a hX hY hZ w hw
  have p51:=pivot4_51 X Y Z a hX hY hZ w hw
  have p61:=pivot4_61 X Y Z a hX hY hZ w hw
  have p62:=pivot4_62 X Y Z a hX hY hZ w hw
  have p63:=pivot4_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - (((-1))/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - (((-1))/(X*Y^2))*p36 - ((1*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot4_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot5_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row5_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_0

theorem pivot5_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row5_0 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X*Z))

#print axioms pivot5_1

theorem pivot5_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row5_1 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot5_2

theorem pivot5_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row5_2 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0)*(1)

#print axioms pivot5_3

theorem pivot5_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row5_3 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot5_4

theorem pivot5_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row5_4 X Y Z a hX hY hZ w hw
  have p4:=pivot5_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X*Y^2)*p4)*(1)

#print axioms pivot5_5

theorem pivot5_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row5_5 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0)*(1)

#print axioms pivot5_6

theorem pivot5_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row5_6 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Y^2*Z))

#print axioms pivot5_7

theorem pivot5_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row5_7 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot5_8

theorem pivot5_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row5_8 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6)*(1)

#print axioms pivot5_9

theorem pivot5_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row5_9 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Z))

#print axioms pivot5_10

theorem pivot5_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row5_10 X Y Z a hX hY hZ w hw
  have p1:=pivot5_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1)*(1)

#print axioms pivot5_11

theorem pivot5_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row5_11 X Y Z a hX hY hZ w hw
  have p4:=pivot5_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p4)*(1)

#print axioms pivot5_12

theorem pivot5_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row5_12 X Y Z a hX hY hZ w hw
  have p1:=pivot5_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p1)*(1)

#print axioms pivot5_13

theorem pivot5_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row5_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_14

theorem pivot5_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 11 + (((-1)*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row5_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_15

theorem pivot5_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row5_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X*Y^2))

#print axioms pivot5_16

theorem pivot5_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row5_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X*Z))

#print axioms pivot5_17

theorem pivot5_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row5_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot5_18

theorem pivot5_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row5_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_19

theorem pivot5_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row5_19 X Y Z a hX hY hZ w hw
  have p19:=pivot5_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p19)*(1)

#print axioms pivot5_20

theorem pivot5_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row5_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot5_21

theorem pivot5_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row5_21 X Y Z a hX hY hZ w hw
  have p19:=pivot5_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*Y^2)/(X))*p19)*(1)

#print axioms pivot5_22

theorem pivot5_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 37 + (((-1))/(X*Y^2))*w 42=0 := by
  have h:=normalized_row5_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_23

theorem pivot5_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 38 + (((-1)*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row5_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_24

theorem pivot5_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 39 + (((-1))/(X))*w 54=0 := by
  have h:=normalized_row5_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_25

theorem pivot5_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 22 + (((-1)*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row5_25 X Y Z a hX hY hZ w hw
  have p17:=pivot5_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p17)*(((-1)*Z)/(Y^2))

#print axioms pivot5_26

theorem pivot5_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row5_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot5_27

theorem pivot5_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row5_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot5_28

theorem pivot5_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 7 + (((-1))/(X*Y^2))*w 12=0 := by
  have h:=normalized_row5_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot5_29

theorem pivot5_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 8 + (((-1)*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row5_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*X)/(Y^2))

#print axioms pivot5_30

theorem pivot5_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 24 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row5_30 X Y Z a hX hY hZ w hw
  have p14:=pivot5_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((-1)*X)*p14)*(1)

#print axioms pivot5_31

theorem pivot5_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row5_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_32

theorem pivot5_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 29 + (((-1))/(X*Z))*w 44=0 := by
  have h:=normalized_row5_32 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p31)*(1)

#print axioms pivot5_33

theorem pivot5_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 31 + (((-1))/(X*Y^2))*w 54=0 := by
  have h:=normalized_row5_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot5_34

theorem pivot5_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 5 + (((-1))/(X*Y^2))*w 48=0 := by
  have h:=normalized_row5_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(X*Y^2))

#print axioms pivot5_35

theorem pivot5_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 42 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row5_47 X Y Z a hX hY hZ w hw
  have p26:=pivot5_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*((1*Y^2)/(Z))

#print axioms pivot5_36

theorem pivot5_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row5_48 X Y Z a hX hY hZ w hw
  have p15:=pivot5_15 X Y Z a hX hY hZ w hw
  have p16:=pivot5_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*((1*X*Y^2)/(Z))

#print axioms pivot5_37

theorem pivot5_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row5_49 X Y Z a hX hY hZ w hw
  have p5:=pivot5_5 X Y Z a hX hY hZ w hw
  have p9:=pivot5_9 X Y Z a hX hY hZ w hw
  have p10:=pivot5_10 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot5_38

theorem pivot5_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row5_50 X Y Z a hX hY hZ w hw
  have p14:=pivot5_14 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - ((1)/(X))*p37)*((-1)*X)

#print axioms pivot5_39

theorem pivot5_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row5_35 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  have p15:=pivot5_15 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot5_40

theorem pivot5_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 20 + ((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44=0 := by
  have h:=normalized_row5_36 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  have p16:=pivot5_16 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot5_41

theorem pivot5_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 15 + ((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row5_51 X Y Z a hX hY hZ w hw
  have p5:=pivot5_5 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p5 - (1)*p39)*(1)

#print axioms pivot5_42

theorem pivot5_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row5_52 X Y Z a hX hY hZ w hw
  have p12:=pivot5_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p12)*(1)

#print axioms pivot5_43

theorem pivot5_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row5_53 X Y Z a hX hY hZ w hw
  have p11:=pivot5_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p11)*(1)

#print axioms pivot5_44

theorem pivot5_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row5_54 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot5_45

theorem pivot5_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row5_37 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p1:=pivot5_1 X Y Z a hX hY hZ w hw
  have p5:=pivot5_5 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  have p9:=pivot5_9 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p14:=pivot5_14 X Y Z a hX hY hZ w hw
  have p17:=pivot5_17 X Y Z a hX hY hZ w hw
  have p22:=pivot5_22 X Y Z a hX hY hZ w hw
  have p25:=pivot5_25 X Y Z a hX hY hZ w hw
  have p26:=pivot5_26 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p42:=pivot5_42 X Y Z a hX hY hZ w hw
  have p45:=pivot5_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0 - (1)*p1 - ((1)/(X))*p5 - (1)*p6 - ((1)/(X))*p9 - ((1)/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - ((1*Y^2)/(X*Z))*p26 - ((1)/(X))*p31 - ((2)/(X))*p36 - ((1)/(X))*p37 - ((2)/(X))*p38 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot5_46

theorem pivot5_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 10 + ((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row5_55 X Y Z a hX hY hZ w hw
  have p24:=pivot5_24 X Y Z a hX hY hZ w hw
  have p35:=pivot5_35 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  have p45:=pivot5_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - ((1)/(X*Y^2))*p39 - ((1*X)/(Y^2))*p45)*(1*X)

#print axioms pivot5_47

theorem pivot5_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row5_38 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p26:=pivot5_26 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p47:=pivot5_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (((-1))/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot5_48

theorem pivot5_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row5_39 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot5_49

theorem pivot5_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row5_56 X Y Z a hX hY hZ w hw
  have p18:=pivot5_18 X Y Z a hX hY hZ w hw
  have p23:=pivot5_23 X Y Z a hX hY hZ w hw
  have p30:=pivot5_30 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - ((1)/(X))*p30 - ((1)/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot5_50

theorem pivot5_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 23 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row5_40 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p26:=pivot5_26 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p46:=pivot5_46 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (((-1))/(X*Z))*p26 - (((-1))/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot5_51

theorem pivot5_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 43 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row5_41 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot5_52

theorem pivot5_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 26 + ((1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_58 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p18:=pivot5_18 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot5_53

theorem pivot5_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 13 + (((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_59 X Y Z a hX hY hZ w hw
  have p40:=pivot5_40 X Y Z a hX hY hZ w hw
  have p53:=pivot5_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - ((1)/(X))*p53)*(1)

#print axioms pivot5_54

theorem pivot5_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row5_60 X Y Z a hX hY hZ w hw
  have p28:=pivot5_28 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  have p53:=pivot5_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - ((1)/(X*Y^2))*p38 - (((-1))/(X*Y^2))*p48 - (1)*p53)*(1*X)

#print axioms pivot5_55

theorem pivot5_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 19 + ((1)/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_61 X Y Z a hX hY hZ w hw
  have p24:=pivot5_24 X Y Z a hX hY hZ w hw
  have p45:=pivot5_45 X Y Z a hX hY hZ w hw
  have p55:=pivot5_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot5_56

theorem pivot5_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    ((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row5_62 X Y Z a hX hY hZ w hw
  have p22:=pivot5_22 X Y Z a hX hY hZ w hw
  have p35:=pivot5_35 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  have p42:=pivot5_42 X Y Z a hX hY hZ w hw
  have p46:=pivot5_46 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - ((1)/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - ((1)/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot5_57

theorem pivot5_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 25 + (((-2))/(X*Z) + ((-1))/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + 1 + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_42 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p5:=pivot5_5 X Y Z a hX hY hZ w hw
  have p9:=pivot5_9 X Y Z a hX hY hZ w hw
  have p10:=pivot5_10 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p16:=pivot5_16 X Y Z a hX hY hZ w hw
  have p21:=pivot5_21 X Y Z a hX hY hZ w hw
  have p23:=pivot5_23 X Y Z a hX hY hZ w hw
  have p29:=pivot5_29 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  have p34:=pivot5_34 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p37:=pivot5_37 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  have p52:=pivot5_52 X Y Z a hX hY hZ w hw
  have p54:=pivot5_54 X Y Z a hX hY hZ w hw
  have p56:=pivot5_56 X Y Z a hX hY hZ w hw
  have p57:=pivot5_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - ((1)/(X*Y^2))*p31 - (1)*p34 - ((2)/(X*Y^2))*p36 - ((2)/(X*Y^2) + (1*Z)/(X*Y^2))*p37 - ((2)/(X*Y^2))*p38 - (((-2))/(X*Y^2) + ((-1)*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot5_58

theorem pivot5_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 40 + (((-2))/(Z) + (-1) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_43 X Y Z a hX hY hZ w hw
  have p1:=pivot5_1 X Y Z a hX hY hZ w hw
  have p3:=pivot5_3 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  have p11:=pivot5_11 X Y Z a hX hY hZ w hw
  have p17:=pivot5_17 X Y Z a hX hY hZ w hw
  have p18:=pivot5_18 X Y Z a hX hY hZ w hw
  have p22:=pivot5_22 X Y Z a hX hY hZ w hw
  have p25:=pivot5_25 X Y Z a hX hY hZ w hw
  have p26:=pivot5_26 X Y Z a hX hY hZ w hw
  have p27:=pivot5_27 X Y Z a hX hY hZ w hw
  have p32:=pivot5_32 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p40:=pivot5_40 X Y Z a hX hY hZ w hw
  have p42:=pivot5_42 X Y Z a hX hY hZ w hw
  have p43:=pivot5_43 X Y Z a hX hY hZ w hw
  have p45:=pivot5_45 X Y Z a hX hY hZ w hw
  have p46:=pivot5_46 X Y Z a hX hY hZ w hw
  have p47:=pivot5_47 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  have p55:=pivot5_55 X Y Z a hX hY hZ w hw
  have p57:=pivot5_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p11 - ((1*X)/(Y^2))*p17 - (1)*p18 - ((1*X)/(Y^2))*p22 - ((1*X)/(Y^2))*p25 - ((1)/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - ((1)/(Y^2) + (1*Z)/(Y^2))*p36 - ((2)/(Y^2))*p38 - (1)*p40 - ((2*X)/(Y^2))*p42 - (1)*p43 - ((1*X)/(Y^2))*p45 - ((2*X)/(Y^2))*p46 - (1)*p47 - (((-1))/(Y^2))*p48 - (((-1)*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot5_59

theorem pivot5_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 14 + ((1*X)/(Y^2*Z) + (2*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row5_63 X Y Z a hX hY hZ w hw
  have p29:=pivot5_29 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  have p59:=pivot5_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - ((1)/(X*Y^2))*p48 - (1)*p59)*(1*X)

#print axioms pivot5_60

theorem pivot5_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    ((2)/(Z) + 1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row5_44 X Y Z a hX hY hZ w hw
  have p1:=pivot5_1 X Y Z a hX hY hZ w hw
  have p3:=pivot5_3 X Y Z a hX hY hZ w hw
  have p6:=pivot5_6 X Y Z a hX hY hZ w hw
  have p12:=pivot5_12 X Y Z a hX hY hZ w hw
  have p14:=pivot5_14 X Y Z a hX hY hZ w hw
  have p19:=pivot5_19 X Y Z a hX hY hZ w hw
  have p22:=pivot5_22 X Y Z a hX hY hZ w hw
  have p24:=pivot5_24 X Y Z a hX hY hZ w hw
  have p25:=pivot5_25 X Y Z a hX hY hZ w hw
  have p30:=pivot5_30 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p41:=pivot5_41 X Y Z a hX hY hZ w hw
  have p42:=pivot5_42 X Y Z a hX hY hZ w hw
  have p45:=pivot5_45 X Y Z a hX hY hZ w hw
  have p46:=pivot5_46 X Y Z a hX hY hZ w hw
  have p48:=pivot5_48 X Y Z a hX hY hZ w hw
  have p49:=pivot5_49 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  have p53:=pivot5_53 X Y Z a hX hY hZ w hw
  have p60:=pivot5_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p12 - ((1*X)/(Y^2))*p14 - (1)*p19 - ((1*X)/(Y^2))*p22 - (1)*p24 - ((1*X)/(Y^2))*p25 - (1)*p30 - ((1)/(Y^2))*p38 - (1)*p41 - ((1*X)/(Y^2))*p42 - ((2*X)/(Y^2))*p45 - ((1*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - ((1*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot5_61

theorem pivot5_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (1)*w 41 + ((1*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row5_64 X Y Z a hX hY hZ w hw
  have p30:=pivot5_30 X Y Z a hX hY hZ w hw
  have p43:=pivot5_43 X Y Z a hX hY hZ w hw
  have p50:=pivot5_50 X Y Z a hX hY hZ w hw
  have p57:=pivot5_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - ((1)/(X))*p43 - ((1*X)/(Y^2))*p50 - (((-1))/(X))*p57)*(1)

#print axioms pivot5_62

theorem pivot5_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    (((-1))/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row5_65 X Y Z a hX hY hZ w hw
  have p32:=pivot5_32 X Y Z a hX hY hZ w hw
  have p42:=pivot5_42 X Y Z a hX hY hZ w hw
  have p60:=pivot5_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot5_63

theorem pivot5_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    ((2)/(X*Z) + (1)/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row5_45 X Y Z a hX hY hZ w hw
  have p0:=pivot5_0 X Y Z a hX hY hZ w hw
  have p5:=pivot5_5 X Y Z a hX hY hZ w hw
  have p9:=pivot5_9 X Y Z a hX hY hZ w hw
  have p10:=pivot5_10 X Y Z a hX hY hZ w hw
  have p13:=pivot5_13 X Y Z a hX hY hZ w hw
  have p15:=pivot5_15 X Y Z a hX hY hZ w hw
  have p20:=pivot5_20 X Y Z a hX hY hZ w hw
  have p28:=pivot5_28 X Y Z a hX hY hZ w hw
  have p31:=pivot5_31 X Y Z a hX hY hZ w hw
  have p33:=pivot5_33 X Y Z a hX hY hZ w hw
  have p35:=pivot5_35 X Y Z a hX hY hZ w hw
  have p36:=pivot5_36 X Y Z a hX hY hZ w hw
  have p38:=pivot5_38 X Y Z a hX hY hZ w hw
  have p39:=pivot5_39 X Y Z a hX hY hZ w hw
  have p44:=pivot5_44 X Y Z a hX hY hZ w hw
  have p51:=pivot5_51 X Y Z a hX hY hZ w hw
  have p61:=pivot5_61 X Y Z a hX hY hZ w hw
  have p62:=pivot5_62 X Y Z a hX hY hZ w hw
  have p63:=pivot5_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - ((1)/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - ((1)/(X*Y^2))*p36 - ((2)/(X*Y^2))*p38 - ((2)/(X*Y^2) + (1*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot5_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot6_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row6_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_0

theorem pivot6_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row6_0 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X*Z))

#print axioms pivot6_1

theorem pivot6_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row6_1 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot6_2

theorem pivot6_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row6_2 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0)*(1)

#print axioms pivot6_3

theorem pivot6_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row6_3 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot6_4

theorem pivot6_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row6_4 X Y Z a hX hY hZ w hw
  have p4:=pivot6_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X*Y^2)*p4)*(1)

#print axioms pivot6_5

theorem pivot6_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row6_5 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0)*(1)

#print axioms pivot6_6

theorem pivot6_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row6_6 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Y^2*Z))

#print axioms pivot6_7

theorem pivot6_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row6_7 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot6_8

theorem pivot6_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row6_8 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6)*(1)

#print axioms pivot6_9

theorem pivot6_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row6_9 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Z))

#print axioms pivot6_10

theorem pivot6_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row6_10 X Y Z a hX hY hZ w hw
  have p1:=pivot6_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1)*(1)

#print axioms pivot6_11

theorem pivot6_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row6_11 X Y Z a hX hY hZ w hw
  have p4:=pivot6_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p4)*(1)

#print axioms pivot6_12

theorem pivot6_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row6_12 X Y Z a hX hY hZ w hw
  have p1:=pivot6_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p1)*(1)

#print axioms pivot6_13

theorem pivot6_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row6_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_14

theorem pivot6_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 11 + (((-1)*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row6_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_15

theorem pivot6_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-1)*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row6_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X*Y^2))

#print axioms pivot6_16

theorem pivot6_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-1)*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row6_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X*Z))

#print axioms pivot6_17

theorem pivot6_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row6_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot6_18

theorem pivot6_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row6_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_19

theorem pivot6_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row6_19 X Y Z a hX hY hZ w hw
  have p19:=pivot6_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p19)*(1)

#print axioms pivot6_20

theorem pivot6_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row6_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot6_21

theorem pivot6_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row6_21 X Y Z a hX hY hZ w hw
  have p19:=pivot6_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X))*p19)*(1)

#print axioms pivot6_22

theorem pivot6_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 37 + ((1)/(X*Y^2))*w 42=0 := by
  have h:=normalized_row6_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_23

theorem pivot6_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 38 + ((1*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row6_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_24

theorem pivot6_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 39 + ((1)/(X))*w 54=0 := by
  have h:=normalized_row6_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_25

theorem pivot6_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 22 + ((1*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row6_25 X Y Z a hX hY hZ w hw
  have p17:=pivot6_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p17)*((1*Z)/(Y^2))

#print axioms pivot6_26

theorem pivot6_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row6_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot6_27

theorem pivot6_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row6_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot6_28

theorem pivot6_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 7 + ((1)/(X*Y^2))*w 12=0 := by
  have h:=normalized_row6_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot6_29

theorem pivot6_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 8 + ((1*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row6_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot6_30

theorem pivot6_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 24 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row6_30 X Y Z a hX hY hZ w hw
  have p14:=pivot6_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p14)*(1)

#print axioms pivot6_31

theorem pivot6_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row6_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_32

theorem pivot6_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 29 + (((-1))/(X*Z))*w 44=0 := by
  have h:=normalized_row6_32 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p31)*(1)

#print axioms pivot6_33

theorem pivot6_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 31 + ((1)/(X*Y^2))*w 54=0 := by
  have h:=normalized_row6_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot6_34

theorem pivot6_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row6_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot6_35

theorem pivot6_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 42 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row6_47 X Y Z a hX hY hZ w hw
  have p26:=pivot6_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*(((-1)*Y^2)/(Z))

#print axioms pivot6_36

theorem pivot6_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row6_48 X Y Z a hX hY hZ w hw
  have p15:=pivot6_15 X Y Z a hX hY hZ w hw
  have p16:=pivot6_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*((1*X*Y^2)/(Z))

#print axioms pivot6_37

theorem pivot6_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row6_49 X Y Z a hX hY hZ w hw
  have p5:=pivot6_5 X Y Z a hX hY hZ w hw
  have p9:=pivot6_9 X Y Z a hX hY hZ w hw
  have p10:=pivot6_10 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot6_38

theorem pivot6_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row6_50 X Y Z a hX hY hZ w hw
  have p14:=pivot6_14 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - (((-1))/(X))*p37)*(1*X)

#print axioms pivot6_39

theorem pivot6_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row6_35 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  have p15:=pivot6_15 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot6_40

theorem pivot6_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 20 + (((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44=0 := by
  have h:=normalized_row6_36 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  have p16:=pivot6_16 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot6_41

theorem pivot6_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 15 + (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row6_51 X Y Z a hX hY hZ w hw
  have p5:=pivot6_5 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p5 - (1)*p39)*(1)

#print axioms pivot6_42

theorem pivot6_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row6_52 X Y Z a hX hY hZ w hw
  have p12:=pivot6_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p12)*(1)

#print axioms pivot6_43

theorem pivot6_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row6_53 X Y Z a hX hY hZ w hw
  have p11:=pivot6_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p11)*(1)

#print axioms pivot6_44

theorem pivot6_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row6_54 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot6_45

theorem pivot6_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row6_37 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p1:=pivot6_1 X Y Z a hX hY hZ w hw
  have p5:=pivot6_5 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  have p9:=pivot6_9 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p14:=pivot6_14 X Y Z a hX hY hZ w hw
  have p17:=pivot6_17 X Y Z a hX hY hZ w hw
  have p22:=pivot6_22 X Y Z a hX hY hZ w hw
  have p25:=pivot6_25 X Y Z a hX hY hZ w hw
  have p26:=pivot6_26 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p42:=pivot6_42 X Y Z a hX hY hZ w hw
  have p45:=pivot6_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p0 - (1)*p1 - (((-1))/(X))*p5 - (1)*p6 - (((-1))/(X))*p9 - (((-1))/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - ((1*Y^2)/(X*Z))*p26 - (((-1))/(X))*p31 - (((-2))/(X))*p36 - (((-1))/(X))*p37 - (((-2))/(X))*p38 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot6_46

theorem pivot6_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 10 + (((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row6_55 X Y Z a hX hY hZ w hw
  have p24:=pivot6_24 X Y Z a hX hY hZ w hw
  have p35:=pivot6_35 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  have p45:=pivot6_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*X)/(Y^2))*p45)*((-1)*X)

#print axioms pivot6_47

theorem pivot6_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row6_38 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p26:=pivot6_26 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p47:=pivot6_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - ((1)/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot6_48

theorem pivot6_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row6_39 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot6_49

theorem pivot6_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row6_56 X Y Z a hX hY hZ w hw
  have p18:=pivot6_18 X Y Z a hX hY hZ w hw
  have p23:=pivot6_23 X Y Z a hX hY hZ w hw
  have p30:=pivot6_30 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - (((-1))/(X))*p30 - (((-1))/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot6_50

theorem pivot6_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 23 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row6_40 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p26:=pivot6_26 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p46:=pivot6_46 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (((-1))/(X*Z))*p26 - ((1)/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot6_51

theorem pivot6_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 43 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row6_41 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot6_52

theorem pivot6_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 26 + (((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_58 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p18:=pivot6_18 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot6_53

theorem pivot6_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 13 + (((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_59 X Y Z a hX hY hZ w hw
  have p40:=pivot6_40 X Y Z a hX hY hZ w hw
  have p53:=pivot6_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - (((-1))/(X))*p53)*(1)

#print axioms pivot6_54

theorem pivot6_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row6_60 X Y Z a hX hY hZ w hw
  have p28:=pivot6_28 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  have p53:=pivot6_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - (((-1))/(X*Y^2))*p38 - ((1)/(X*Y^2))*p48 - (1)*p53)*((-1)*X)

#print axioms pivot6_55

theorem pivot6_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 19 + (((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_61 X Y Z a hX hY hZ w hw
  have p24:=pivot6_24 X Y Z a hX hY hZ w hw
  have p45:=pivot6_45 X Y Z a hX hY hZ w hw
  have p55:=pivot6_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot6_56

theorem pivot6_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row6_62 X Y Z a hX hY hZ w hw
  have p22:=pivot6_22 X Y Z a hX hY hZ w hw
  have p35:=pivot6_35 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  have p42:=pivot6_42 X Y Z a hX hY hZ w hw
  have p46:=pivot6_46 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - (((-1))/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot6_57

theorem pivot6_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 25 + (((-2))/(X*Z) + (1)/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + 1 + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_42 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p5:=pivot6_5 X Y Z a hX hY hZ w hw
  have p9:=pivot6_9 X Y Z a hX hY hZ w hw
  have p10:=pivot6_10 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p16:=pivot6_16 X Y Z a hX hY hZ w hw
  have p21:=pivot6_21 X Y Z a hX hY hZ w hw
  have p23:=pivot6_23 X Y Z a hX hY hZ w hw
  have p29:=pivot6_29 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  have p34:=pivot6_34 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p37:=pivot6_37 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  have p52:=pivot6_52 X Y Z a hX hY hZ w hw
  have p54:=pivot6_54 X Y Z a hX hY hZ w hw
  have p56:=pivot6_56 X Y Z a hX hY hZ w hw
  have p57:=pivot6_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - (((-1))/(X*Y^2))*p31 - (1)*p34 - (((-2))/(X*Y^2))*p36 - (((-2))/(X*Y^2) + (1*Z)/(X*Y^2))*p37 - (((-2))/(X*Y^2))*p38 - ((2)/(X*Y^2) + ((-1)*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot6_58

theorem pivot6_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 40 + ((2)/(Z) + (-1) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_43 X Y Z a hX hY hZ w hw
  have p1:=pivot6_1 X Y Z a hX hY hZ w hw
  have p3:=pivot6_3 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  have p11:=pivot6_11 X Y Z a hX hY hZ w hw
  have p17:=pivot6_17 X Y Z a hX hY hZ w hw
  have p18:=pivot6_18 X Y Z a hX hY hZ w hw
  have p22:=pivot6_22 X Y Z a hX hY hZ w hw
  have p25:=pivot6_25 X Y Z a hX hY hZ w hw
  have p26:=pivot6_26 X Y Z a hX hY hZ w hw
  have p27:=pivot6_27 X Y Z a hX hY hZ w hw
  have p32:=pivot6_32 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p40:=pivot6_40 X Y Z a hX hY hZ w hw
  have p42:=pivot6_42 X Y Z a hX hY hZ w hw
  have p43:=pivot6_43 X Y Z a hX hY hZ w hw
  have p45:=pivot6_45 X Y Z a hX hY hZ w hw
  have p46:=pivot6_46 X Y Z a hX hY hZ w hw
  have p47:=pivot6_47 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  have p55:=pivot6_55 X Y Z a hX hY hZ w hw
  have p57:=pivot6_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p11 - (((-1)*X)/(Y^2))*p17 - (1)*p18 - (((-1)*X)/(Y^2))*p22 - (((-1)*X)/(Y^2))*p25 - (((-1))/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - ((1)/(Y^2) + ((-1)*Z)/(Y^2))*p36 - ((2)/(Y^2))*p38 - (1)*p40 - (((-2)*X)/(Y^2))*p42 - (1)*p43 - (((-1)*X)/(Y^2))*p45 - (((-2)*X)/(Y^2))*p46 - (1)*p47 - (((-1))/(Y^2))*p48 - ((1*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot6_59

theorem pivot6_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 14 + ((1*X)/(Y^2*Z) + (2*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row6_63 X Y Z a hX hY hZ w hw
  have p29:=pivot6_29 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  have p59:=pivot6_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - (((-1))/(X*Y^2))*p48 - (1)*p59)*((-1)*X)

#print axioms pivot6_60

theorem pivot6_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (((-2))/(Z) + 1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row6_44 X Y Z a hX hY hZ w hw
  have p1:=pivot6_1 X Y Z a hX hY hZ w hw
  have p3:=pivot6_3 X Y Z a hX hY hZ w hw
  have p6:=pivot6_6 X Y Z a hX hY hZ w hw
  have p12:=pivot6_12 X Y Z a hX hY hZ w hw
  have p14:=pivot6_14 X Y Z a hX hY hZ w hw
  have p19:=pivot6_19 X Y Z a hX hY hZ w hw
  have p22:=pivot6_22 X Y Z a hX hY hZ w hw
  have p24:=pivot6_24 X Y Z a hX hY hZ w hw
  have p25:=pivot6_25 X Y Z a hX hY hZ w hw
  have p30:=pivot6_30 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p41:=pivot6_41 X Y Z a hX hY hZ w hw
  have p42:=pivot6_42 X Y Z a hX hY hZ w hw
  have p45:=pivot6_45 X Y Z a hX hY hZ w hw
  have p46:=pivot6_46 X Y Z a hX hY hZ w hw
  have p48:=pivot6_48 X Y Z a hX hY hZ w hw
  have p49:=pivot6_49 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  have p53:=pivot6_53 X Y Z a hX hY hZ w hw
  have p60:=pivot6_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2))*p1 - (((-1)*X)/(Y^2))*p3 - (((-1)*X)/(Y^2))*p6 - (1)*p12 - (((-1)*X)/(Y^2))*p14 - (1)*p19 - (((-1)*X)/(Y^2))*p22 - (1)*p24 - (((-1)*X)/(Y^2))*p25 - (1)*p30 - ((1)/(Y^2))*p38 - (1)*p41 - (((-1)*X)/(Y^2))*p42 - (((-2)*X)/(Y^2))*p45 - (((-1)*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - (((-1)*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot6_61

theorem pivot6_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    (1)*w 41 + ((1*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row6_64 X Y Z a hX hY hZ w hw
  have p30:=pivot6_30 X Y Z a hX hY hZ w hw
  have p43:=pivot6_43 X Y Z a hX hY hZ w hw
  have p50:=pivot6_50 X Y Z a hX hY hZ w hw
  have p57:=pivot6_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - (((-1))/(X))*p43 - (((-1)*X)/(Y^2))*p50 - ((1)/(X))*p57)*(1)

#print axioms pivot6_62

theorem pivot6_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row6_65 X Y Z a hX hY hZ w hw
  have p32:=pivot6_32 X Y Z a hX hY hZ w hw
  have p42:=pivot6_42 X Y Z a hX hY hZ w hw
  have p60:=pivot6_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot6_63

theorem pivot6_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ((2)/(X*Z) + ((-1))/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row6_45 X Y Z a hX hY hZ w hw
  have p0:=pivot6_0 X Y Z a hX hY hZ w hw
  have p5:=pivot6_5 X Y Z a hX hY hZ w hw
  have p9:=pivot6_9 X Y Z a hX hY hZ w hw
  have p10:=pivot6_10 X Y Z a hX hY hZ w hw
  have p13:=pivot6_13 X Y Z a hX hY hZ w hw
  have p15:=pivot6_15 X Y Z a hX hY hZ w hw
  have p20:=pivot6_20 X Y Z a hX hY hZ w hw
  have p28:=pivot6_28 X Y Z a hX hY hZ w hw
  have p31:=pivot6_31 X Y Z a hX hY hZ w hw
  have p33:=pivot6_33 X Y Z a hX hY hZ w hw
  have p35:=pivot6_35 X Y Z a hX hY hZ w hw
  have p36:=pivot6_36 X Y Z a hX hY hZ w hw
  have p38:=pivot6_38 X Y Z a hX hY hZ w hw
  have p39:=pivot6_39 X Y Z a hX hY hZ w hw
  have p44:=pivot6_44 X Y Z a hX hY hZ w hw
  have p51:=pivot6_51 X Y Z a hX hY hZ w hw
  have p61:=pivot6_61 X Y Z a hX hY hZ w hw
  have p62:=pivot6_62 X Y Z a hX hY hZ w hw
  have p63:=pivot6_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2))*p0 - (((-1))/(X*Y^2))*p5 - (((-1))/(X*Y^2))*p9 - (((-1))/(X*Y^2))*p10 - (((-1))/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - (((-1))/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - (((-1))/(X*Y^2))*p36 - (((-2))/(X*Y^2))*p38 - (((-2))/(X*Y^2) + (1*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot6_64

end SmallLevelTwentyTwoTriangular
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem pivot7_0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 0=0 := by
  have h:=normalized_row7_46 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_0

theorem pivot7_1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 63=0 := by
  have h:=normalized_row7_0 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p0)*(((-1))/(X*Z))

#print axioms pivot7_1

theorem pivot7_2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 1=0 := by
  have h:=normalized_row7_1 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot7_2

theorem pivot7_3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 3=0 := by
  have h:=normalized_row7_2 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0)*(1)

#print axioms pivot7_3

theorem pivot7_4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 65=0 := by
  have h:=normalized_row7_3 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Y^2*Z))*p0)*(1)

#print axioms pivot7_4

theorem pivot7_5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 30=0 := by
  have h:=normalized_row7_4 X Y Z a hX hY hZ w hw
  have p4:=pivot7_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X*Y^2)*p4)*(1)

#print axioms pivot7_5

theorem pivot7_6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 33=0 := by
  have h:=normalized_row7_5 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0)*(1)

#print axioms pivot7_6

theorem pivot7_7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 64=0 := by
  have h:=normalized_row7_6 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Y^2*Z))

#print axioms pivot7_7

theorem pivot7_8 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 2=0 := by
  have h:=normalized_row7_7 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Y^2*Z))*p6)*(1)

#print axioms pivot7_8

theorem pivot7_9 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 6=0 := by
  have h:=normalized_row7_8 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6)*(1)

#print axioms pivot7_9

theorem pivot7_10 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 60=0 := by
  have h:=normalized_row7_9 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p6)*(((-1)*X)/(Z))

#print axioms pivot7_10

theorem pivot7_11 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 34=0 := by
  have h:=normalized_row7_10 X Y Z a hX hY hZ w hw
  have p1:=pivot7_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1)*(1)

#print axioms pivot7_11

theorem pivot7_12 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 32=0 := by
  have h:=normalized_row7_11 X Y Z a hX hY hZ w hw
  have p4:=pivot7_4 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p4)*(1)

#print axioms pivot7_12

theorem pivot7_13 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 36=0 := by
  have h:=normalized_row7_12 X Y Z a hX hY hZ w hw
  have p1:=pivot7_1 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p1)*(1)

#print axioms pivot7_13

theorem pivot7_14 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 9 + (((-1)*Y^2)/(X*Z))*w 44=0 := by
  have h:=normalized_row7_13 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_14

theorem pivot7_15 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 11 + (((-1)*Z)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row7_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_15

theorem pivot7_16 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1)*Z)/(X*Y^2))*w 18 + (1)*w 55=0 := by
  have h:=normalized_row7_15 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Z)/(X*Y^2))

#print axioms pivot7_16

theorem pivot7_17 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1)*Y^2)/(X*Z))*w 22 + (1)*w 57=0 := by
  have h:=normalized_row7_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1)*Y^2)/(X*Z))

#print axioms pivot7_17

theorem pivot7_18 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 4 + (((-1))/(Y^2))*w 54=0 := by
  have h:=normalized_row7_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(((-1))/(Y^2))

#print axioms pivot7_18

theorem pivot7_19 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1))/(Y^2))*w 12 + (1)*w 62=0 := by
  have h:=normalized_row7_18 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_19

theorem pivot7_20 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 12 + (1)*w 35=0 := by
  have h:=normalized_row7_19 X Y Z a hX hY hZ w hw
  have p19:=pivot7_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p19)*(1)

#print axioms pivot7_20

theorem pivot7_21 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 18 + (1)*w 61=0 := by
  have h:=normalized_row7_20 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot7_21

theorem pivot7_22 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(X))*w 12 + (1)*w 27=0 := by
  have h:=normalized_row7_21 X Y Z a hX hY hZ w hw
  have p19:=pivot7_19 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*Y^2)/(X))*p19)*(1)

#print axioms pivot7_22

theorem pivot7_23 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 37 + ((1)/(X*Y^2))*w 42=0 := by
  have h:=normalized_row7_22 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_23

theorem pivot7_24 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 38 + ((1*X)/(Y^2))*w 51=0 := by
  have h:=normalized_row7_23 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_24

theorem pivot7_25 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 39 + ((1)/(X))*w 54=0 := by
  have h:=normalized_row7_24 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_25

theorem pivot7_26 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 22 + ((1*Z)/(Y^2))*w 42=0 := by
  have h:=normalized_row7_25 X Y Z a hX hY hZ w hw
  have p17:=pivot7_17 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p17)*((1*Z)/(Y^2))

#print axioms pivot7_26

theorem pivot7_27 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 45 + (1)*w 58=0 := by
  have h:=normalized_row7_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot7_27

theorem pivot7_28 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(X*Y^2))*w 54 + (1)*w 59=0 := by
  have h:=normalized_row7_27 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot7_28

theorem pivot7_29 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 7 + ((1)/(X*Y^2))*w 12=0 := by
  have h:=normalized_row7_28 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot7_29

theorem pivot7_30 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 8 + ((1*X)/(Y^2))*w 21=0 := by
  have h:=normalized_row7_29 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1*X)/(Y^2))

#print axioms pivot7_30

theorem pivot7_31 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 24 + ((1*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row7_30 X Y Z a hX hY hZ w hw
  have p14:=pivot7_14 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1*X)*p14)*(1)

#print axioms pivot7_31

theorem pivot7_32 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1*X)/(Y^2))*w 15 + (1)*w 28=0 := by
  have h:=normalized_row7_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_32

theorem pivot7_33 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 29 + (((-1))/(X*Z))*w 44=0 := by
  have h:=normalized_row7_32 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p31)*(1)

#print axioms pivot7_33

theorem pivot7_34 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 31 + ((1)/(X*Y^2))*w 54=0 := by
  have h:=normalized_row7_33 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*(1)

#print axioms pivot7_34

theorem pivot7_35 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 5 + ((1)/(X*Y^2))*w 48=0 := by
  have h:=normalized_row7_34 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h)*((1)/(X*Y^2))

#print axioms pivot7_35

theorem pivot7_36 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 42 + (((-1)*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row7_47 X Y Z a hX hY hZ w hw
  have p26:=pivot7_26 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p26)*(((-1)*Y^2)/(Z))

#print axioms pivot7_36

theorem pivot7_37 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 18 + (1)*w 48=0 := by
  have h:=normalized_row7_48 X Y Z a hX hY hZ w hw
  have p15:=pivot7_15 X Y Z a hX hY hZ w hw
  have p16:=pivot7_16 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p15 - (1)*p16)*((1*X*Y^2)/(Z))

#print axioms pivot7_37

theorem pivot7_38 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 12 + (1)*w 54=0 := by
  have h:=normalized_row7_49 X Y Z a hX hY hZ w hw
  have p5:=pivot7_5 X Y Z a hX hY hZ w hw
  have p9:=pivot7_9 X Y Z a hX hY hZ w hw
  have p10:=pivot7_10 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p5 - (1)*p9 - (1)*p10 - (1)*p13 - (1)*p31 - (1)*p36 - (1)*p37)*(1)

#print axioms pivot7_38

theorem pivot7_39 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 48=0 := by
  have h:=normalized_row7_50 X Y Z a hX hY hZ w hw
  have p14:=pivot7_14 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p14 - (1)*p36 - (((-1))/(X))*p37)*(1*X)

#print axioms pivot7_39

theorem pivot7_40 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44 + (1)*w 46=0 := by
  have h:=normalized_row7_35 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  have p15:=pivot7_15 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p15 - (1)*p31 - (((-1))/(Y^2))*p39)*(1)

#print axioms pivot7_40

theorem pivot7_41 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 20 + (((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44=0 := by
  have h:=normalized_row7_36 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  have p16:=pivot7_16 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1)*X)/(Z))*p6 - (((-1)*X)/(Z))*p16 - (1)*p36 - (((-1))/(Y^2))*p37 - ((1)/(Y^2))*p39)*(1)

#print axioms pivot7_41

theorem pivot7_42 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 15 + (((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44=0 := by
  have h:=normalized_row7_51 X Y Z a hX hY hZ w hw
  have p5:=pivot7_5 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p5 - (1)*p39)*(1)

#print axioms pivot7_42

theorem pivot7_43 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 16 + (1)*w 49=0 := by
  have h:=normalized_row7_52 X Y Z a hX hY hZ w hw
  have p12:=pivot7_12 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p12)*(1)

#print axioms pivot7_43

theorem pivot7_44 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 17 + (1)*w 50=0 := by
  have h:=normalized_row7_53 X Y Z a hX hY hZ w hw
  have p11:=pivot7_11 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p11)*(1)

#print axioms pivot7_44

theorem pivot7_45 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 + (1)*w 51=0 := by
  have h:=normalized_row7_54 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p13 - (1)*p37 - ((-1))*p39)*(1)

#print axioms pivot7_45

theorem pivot7_46 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 21 + (1)*w 45=0 := by
  have h:=normalized_row7_37 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p1:=pivot7_1 X Y Z a hX hY hZ w hw
  have p5:=pivot7_5 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  have p9:=pivot7_9 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p14:=pivot7_14 X Y Z a hX hY hZ w hw
  have p17:=pivot7_17 X Y Z a hX hY hZ w hw
  have p22:=pivot7_22 X Y Z a hX hY hZ w hw
  have p25:=pivot7_25 X Y Z a hX hY hZ w hw
  have p26:=pivot7_26 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  have p42:=pivot7_42 X Y Z a hX hY hZ w hw
  have p45:=pivot7_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X))*p0 - (1)*p1 - ((1)/(X))*p5 - (1)*p6 - ((1)/(X))*p9 - ((1)/(X))*p13 - (1)*p14 - (1)*p17 - (1)*p22 - (1)*p25 - ((1*Y^2)/(X*Z))*p26 - ((1)/(X))*p31 - ((1)/(X))*p37 - (1)*p42 - (1)*p45)*(1)

#print axioms pivot7_46

theorem pivot7_47 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 10 + (((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row7_55 X Y Z a hX hY hZ w hw
  have p24:=pivot7_24 X Y Z a hX hY hZ w hw
  have p35:=pivot7_35 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  have p45:=pivot7_45 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p24 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*X)/(Y^2))*p45)*((-1)*X)

#print axioms pivot7_47

theorem pivot7_48 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 12 + (((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row7_38 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p26:=pivot7_26 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p38:=pivot7_38 X Y Z a hX hY hZ w hw
  have p47:=pivot7_47 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - ((1)/(Z))*p26 - (((-1))/(Y^2))*p36 - (1)*p38 - (1)*p47)*((-1))

#print axioms pivot7_48

theorem pivot7_49 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 + (1)*w 56=0 := by
  have h:=normalized_row7_39 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Z))*p0 - (1)*p48)*(1)

#print axioms pivot7_49

theorem pivot7_50 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 21 + (((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row7_56 X Y Z a hX hY hZ w hw
  have p18:=pivot7_18 X Y Z a hX hY hZ w hw
  have p23:=pivot7_23 X Y Z a hX hY hZ w hw
  have p30:=pivot7_30 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p38:=pivot7_38 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p18 - (1)*p23 - (((-1))/(X))*p30 - (((-1))/(X*Y^2))*p36 - ((1)/(Y^2))*p38 - (((-1))/(Y^2))*p48)*(1*Y^2)

#print axioms pivot7_50

theorem pivot7_51 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 23 + ((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row7_40 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p26:=pivot7_26 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p46:=pivot7_46 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (((-1))/(X*Z))*p26 - ((1)/(X*Y^2))*p36 - (1)*p46 - ((-1))*p50)*(1)

#print axioms pivot7_51

theorem pivot7_52 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 43 + (((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44=0 := by
  have h:=normalized_row7_41 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X*Z))*p0 - (1)*p50)*(1)

#print axioms pivot7_52

theorem pivot7_53 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 26 + (((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_58 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p18:=pivot7_18 X Y Z a hX hY hZ w hw
  have p38:=pivot7_38 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(Y^2))*p13 - (1)*p18 - ((1)/(Y^2))*p38 - (1)*p39 - (((-1))/(Y^2) + ((-1)*a)/(Y))*p48)*(1)

#print axioms pivot7_53

theorem pivot7_54 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 13 + (((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_59 X Y Z a hX hY hZ w hw
  have p40:=pivot7_40 X Y Z a hX hY hZ w hw
  have p53:=pivot7_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p40 - (((-1))/(X))*p53)*(1)

#print axioms pivot7_54

theorem pivot7_55 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44 + (1)*w 52=0 := by
  have h:=normalized_row7_60 X Y Z a hX hY hZ w hw
  have p28:=pivot7_28 X Y Z a hX hY hZ w hw
  have p38:=pivot7_38 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  have p53:=pivot7_53 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p28 - (((-1))/(X*Y^2))*p38 - ((1)/(X*Y^2))*p48 - (1)*p53)*((-1)*X)

#print axioms pivot7_55

theorem pivot7_56 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 19 + (((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_61 X Y Z a hX hY hZ w hw
  have p24:=pivot7_24 X Y Z a hX hY hZ w hw
  have p45:=pivot7_45 X Y Z a hX hY hZ w hw
  have p55:=pivot7_55 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p24 - ((1)/(Y^2))*p45 - (1)*p55)*(1)

#print axioms pivot7_56

theorem pivot7_57 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 + (1)*w 49=0 := by
  have h:=normalized_row7_62 X Y Z a hX hY hZ w hw
  have p22:=pivot7_22 X Y Z a hX hY hZ w hw
  have p35:=pivot7_35 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  have p42:=pivot7_42 X Y Z a hX hY hZ w hw
  have p46:=pivot7_46 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p22 - (1)*p35 - (((-1))/(X*Y^2))*p39 - (((-1)*a)/(Y))*p42 - ((1)/(Y^2))*p46 - (((-1))/(X))*p48 - (((-1))/(Y^2))*p50)*(1)

#print axioms pivot7_57

theorem pivot7_58 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 25 + ((1)/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (2)/(Z) + 1 + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_42 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p5:=pivot7_5 X Y Z a hX hY hZ w hw
  have p9:=pivot7_9 X Y Z a hX hY hZ w hw
  have p10:=pivot7_10 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p16:=pivot7_16 X Y Z a hX hY hZ w hw
  have p21:=pivot7_21 X Y Z a hX hY hZ w hw
  have p23:=pivot7_23 X Y Z a hX hY hZ w hw
  have p29:=pivot7_29 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  have p34:=pivot7_34 X Y Z a hX hY hZ w hw
  have p37:=pivot7_37 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  have p52:=pivot7_52 X Y Z a hX hY hZ w hw
  have p54:=pivot7_54 X Y Z a hX hY hZ w hw
  have p56:=pivot7_56 X Y Z a hX hY hZ w hw
  have p57:=pivot7_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p16 - (1)*p21 - (1)*p23 - (1)*p29 - ((1)/(X*Y^2))*p31 - (1)*p34 - ((1*Z)/(X*Y^2))*p37 - (((-1)*Z)/(X*Y^2))*p39 - (1)*p52 - (1)*p54 - (1)*p56 - (1)*p57)*(1)

#print axioms pivot7_58

theorem pivot7_59 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 40 + ((-1) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_43 X Y Z a hX hY hZ w hw
  have p1:=pivot7_1 X Y Z a hX hY hZ w hw
  have p3:=pivot7_3 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  have p11:=pivot7_11 X Y Z a hX hY hZ w hw
  have p17:=pivot7_17 X Y Z a hX hY hZ w hw
  have p18:=pivot7_18 X Y Z a hX hY hZ w hw
  have p22:=pivot7_22 X Y Z a hX hY hZ w hw
  have p25:=pivot7_25 X Y Z a hX hY hZ w hw
  have p26:=pivot7_26 X Y Z a hX hY hZ w hw
  have p27:=pivot7_27 X Y Z a hX hY hZ w hw
  have p32:=pivot7_32 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p40:=pivot7_40 X Y Z a hX hY hZ w hw
  have p43:=pivot7_43 X Y Z a hX hY hZ w hw
  have p45:=pivot7_45 X Y Z a hX hY hZ w hw
  have p47:=pivot7_47 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  have p55:=pivot7_55 X Y Z a hX hY hZ w hw
  have p57:=pivot7_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p11 - ((1*X)/(Y^2))*p17 - (1)*p18 - ((1*X)/(Y^2))*p22 - ((1*X)/(Y^2))*p25 - ((1)/(Z) + 1)*p26 - (1)*p27 - (1)*p32 - (((-1))/(Y^2) + ((-1)*Z)/(Y^2))*p36 - (1)*p40 - (1)*p43 - ((1*X)/(Y^2))*p45 - (1)*p47 - (((-1))/(Y^2))*p48 - ((1*X)/(Y^2))*p50 - (1)*p55 - ((-1))*p57)*(1)

#print axioms pivot7_59

theorem pivot7_60 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 14 + ((1*X)/(Y^2*Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44=0 := by
  have h:=normalized_row7_63 X Y Z a hX hY hZ w hw
  have p29:=pivot7_29 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  have p59:=pivot7_59 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p29 - (((-1))/(X*Y^2))*p48 - (1)*p59)*((-1)*X)

#print axioms pivot7_60

theorem pivot7_61 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 50=0 := by
  have h:=normalized_row7_44 X Y Z a hX hY hZ w hw
  have p1:=pivot7_1 X Y Z a hX hY hZ w hw
  have p3:=pivot7_3 X Y Z a hX hY hZ w hw
  have p6:=pivot7_6 X Y Z a hX hY hZ w hw
  have p12:=pivot7_12 X Y Z a hX hY hZ w hw
  have p14:=pivot7_14 X Y Z a hX hY hZ w hw
  have p19:=pivot7_19 X Y Z a hX hY hZ w hw
  have p22:=pivot7_22 X Y Z a hX hY hZ w hw
  have p24:=pivot7_24 X Y Z a hX hY hZ w hw
  have p25:=pivot7_25 X Y Z a hX hY hZ w hw
  have p30:=pivot7_30 X Y Z a hX hY hZ w hw
  have p38:=pivot7_38 X Y Z a hX hY hZ w hw
  have p41:=pivot7_41 X Y Z a hX hY hZ w hw
  have p42:=pivot7_42 X Y Z a hX hY hZ w hw
  have p46:=pivot7_46 X Y Z a hX hY hZ w hw
  have p48:=pivot7_48 X Y Z a hX hY hZ w hw
  have p49:=pivot7_49 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  have p53:=pivot7_53 X Y Z a hX hY hZ w hw
  have p60:=pivot7_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1*X)/(Y^2))*p1 - ((1*X)/(Y^2))*p3 - ((1*X)/(Y^2))*p6 - (1)*p12 - ((1*X)/(Y^2))*p14 - (1)*p19 - ((1*X)/(Y^2))*p22 - (1)*p24 - ((1*X)/(Y^2))*p25 - (1)*p30 - (((-1))/(Y^2))*p38 - (1)*p41 - ((1*X)/(Y^2))*p42 - ((1*X)/(Y^2))*p46 - ((1)/(Y^2))*p48 - (1)*p49 - (((-1)*X)/(Y^2))*p50 - (1)*p53 - (1)*p60)*(1)

#print axioms pivot7_61

theorem pivot7_62 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (1)*w 41 + ((1*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44=0 := by
  have h:=normalized_row7_64 X Y Z a hX hY hZ w hw
  have p30:=pivot7_30 X Y Z a hX hY hZ w hw
  have p43:=pivot7_43 X Y Z a hX hY hZ w hw
  have p50:=pivot7_50 X Y Z a hX hY hZ w hw
  have p57:=pivot7_57 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (1)*p30 - (((-1))/(X))*p43 - (((-1)*X)/(Y^2))*p50 - ((1)/(X))*p57)*(1)

#print axioms pivot7_62

theorem pivot7_63 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 + (1)*w 47=0 := by
  have h:=normalized_row7_65 X Y Z a hX hY hZ w hw
  have p32:=pivot7_32 X Y Z a hX hY hZ w hw
  have p42:=pivot7_42 X Y Z a hX hY hZ w hw
  have p60:=pivot7_60 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - (((-1))/(X))*p32 - ((1)/(Y^2))*p42 - (1)*p60)*(1)

#print axioms pivot7_63

theorem pivot7_64 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    (((-1))/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44 + (1)*w 53=0 := by
  have h:=normalized_row7_45 X Y Z a hX hY hZ w hw
  have p0:=pivot7_0 X Y Z a hX hY hZ w hw
  have p5:=pivot7_5 X Y Z a hX hY hZ w hw
  have p9:=pivot7_9 X Y Z a hX hY hZ w hw
  have p10:=pivot7_10 X Y Z a hX hY hZ w hw
  have p13:=pivot7_13 X Y Z a hX hY hZ w hw
  have p15:=pivot7_15 X Y Z a hX hY hZ w hw
  have p20:=pivot7_20 X Y Z a hX hY hZ w hw
  have p28:=pivot7_28 X Y Z a hX hY hZ w hw
  have p31:=pivot7_31 X Y Z a hX hY hZ w hw
  have p33:=pivot7_33 X Y Z a hX hY hZ w hw
  have p35:=pivot7_35 X Y Z a hX hY hZ w hw
  have p36:=pivot7_36 X Y Z a hX hY hZ w hw
  have p39:=pivot7_39 X Y Z a hX hY hZ w hw
  have p44:=pivot7_44 X Y Z a hX hY hZ w hw
  have p51:=pivot7_51 X Y Z a hX hY hZ w hw
  have p61:=pivot7_61 X Y Z a hX hY hZ w hw
  have p62:=pivot7_62 X Y Z a hX hY hZ w hw
  have p63:=pivot7_63 X Y Z a hX hY hZ w hw
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (h - ((1)/(X*Y^2))*p0 - ((1)/(X*Y^2))*p5 - ((1)/(X*Y^2))*p9 - ((1)/(X*Y^2))*p10 - ((1)/(X*Y^2))*p13 - (1)*p15 - (1)*p20 - (1)*p28 - ((1)/(X*Y^2))*p31 - (1)*p33 - (1)*p35 - ((1)/(X*Y^2))*p36 - ((1*Z)/(X*Y^2))*p39 - (1)*p44 - (1)*p51 - ((-1))*p61 - (1)*p62 - (1)*p63)*(1)

#print axioms pivot7_64

end SmallLevelTwentyTwoTriangular
end
end
end

/-! ## SmallLevelTwentyTwoTriangularKernelCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyTwoTriangular
open Complex SmallLevelTwentyTwoLaurent

theorem kernel_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole1 X Y Z a j*w 44 := by
  have z53 : w 53=pole1 X Y Z a 53*w 44 := by
    have h:=pivot1_64 X Y Z a hX hY hZ w hw
    change w 53=(((-1))/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole1 X Y Z a 47*w 44 := by
    have h:=pivot1_63 X Y Z a hX hY hZ w hw
    change w 47=(((-1))/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole1 X Y Z a 41*w 44 := by
    have h:=pivot1_62 X Y Z a hX hY hZ w hw
    change w 41=((1*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole1 X Y Z a 50*w 44 := by
    have h:=pivot1_61 X Y Z a hX hY hZ w hw
    change w 50=((-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole1 X Y Z a 14*w 44 := by
    have h:=pivot1_60 X Y Z a hX hY hZ w hw
    change w 14=((1*X)/(Y^2*Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole1 X Y Z a 40*w 44 := by
    have h:=pivot1_59 X Y Z a hX hY hZ w hw
    change w 40=(1 + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole1 X Y Z a 25*w 44 := by
    have h:=pivot1_58 X Y Z a hX hY hZ w hw
    change w 25=((1)/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-2))/(Z) + (-1) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole1 X Y Z a 49*w 44 := by
    have h:=pivot1_57 X Y Z a hX hY hZ w hw
    change w 49=((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole1 X Y Z a 19*w 44 := by
    have h:=pivot1_56 X Y Z a hX hY hZ w hw
    change w 19=((1)/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole1 X Y Z a 52*w 44 := by
    have h:=pivot1_55 X Y Z a hX hY hZ w hw
    change w 52=(((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole1 X Y Z a 13*w 44 := by
    have h:=pivot1_54 X Y Z a hX hY hZ w hw
    change w 13=(((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole1 X Y Z a 26*w 44 := by
    have h:=pivot1_53 X Y Z a hX hY hZ w hw
    change w 26=((1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole1 X Y Z a 43*w 44 := by
    have h:=pivot1_52 X Y Z a hX hY hZ w hw
    change w 43=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole1 X Y Z a 23*w 44 := by
    have h:=pivot1_51 X Y Z a hX hY hZ w hw
    change w 23=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole1 X Y Z a 21*w 44 := by
    have h:=pivot1_50 X Y Z a hX hY hZ w hw
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole1 X Y Z a 56*w 44 := by
    have h:=pivot1_49 X Y Z a hX hY hZ w hw
    change w 56=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole1 X Y Z a 12*w 44 := by
    have h:=pivot1_48 X Y Z a hX hY hZ w hw
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole1 X Y Z a 10*w 44 := by
    have h:=pivot1_47 X Y Z a hX hY hZ w hw
    change w 10=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole1 X Y Z a 45*w 44 := by
    have h:=pivot1_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole1 X Y Z a 51*w 44 := by
    have h:=pivot1_45 X Y Z a hX hY hZ w hw
    change w 51=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole1 X Y Z a 17*w 44 := by
    have h:=pivot1_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=((-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=(1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole1 X Y Z a 16*w 44 := by
    have h:=pivot1_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=(((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole1 X Y Z a 15*w 44 := by
    have h:=pivot1_42 X Y Z a hX hY hZ w hw
    change w 15=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole1 X Y Z a 20*w 44 := by
    have h:=pivot1_41 X Y Z a hX hY hZ w hw
    change w 20=((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole1 X Y Z a 46*w 44 := by
    have h:=pivot1_40 X Y Z a hX hY hZ w hw
    change w 46=(((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole1 X Y Z a 48*w 44 := by
    have h:=pivot1_39 X Y Z a hX hY hZ w hw
    change w 48=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole1 X Y Z a 54*w 44 := by
    have h:=pivot1_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 54=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole1 X Y Z a 18*w 44 := by
    have h:=pivot1_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 18=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole1 X Y Z a 42*w 44 := by
    have h:=pivot1_36 X Y Z a hX hY hZ w hw
    change w 42=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole1 X Y Z a 5*w 44 := by
    have h:=pivot1_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 5=(((-1))/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v48
  have z31 : w 31=pole1 X Y Z a 31*w 44 := by
    have h:=pivot1_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 31=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z29 : w 29=pole1 X Y Z a 29*w 44 := by
    have h:=pivot1_33 X Y Z a hX hY hZ w hw
    change w 29=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole1 X Y Z a 28*w 44 := by
    have h:=pivot1_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v15
    change w 28=((1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v15
  have z24 : w 24=pole1 X Y Z a 24*w 44 := by
    have h:=pivot1_31 X Y Z a hX hY hZ w hw
    change w 24=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole1 X Y Z a 8*w 44 := by
    have h:=pivot1_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 8=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v21
  have z7 : w 7=pole1 X Y Z a 7*w 44 := by
    have h:=pivot1_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 7=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z59 : w 59=pole1 X Y Z a 59*w 44 := by
    have h:=pivot1_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 59=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z58 : w 58=pole1 X Y Z a 58*w 44 := by
    have h:=pivot1_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v45
    change w 58=((1)/(Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v45
  have z22 : w 22=pole1 X Y Z a 22*w 44 := by
    have h:=pivot1_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v42
  have z39 : w 39=pole1 X Y Z a 39*w 44 := by
    have h:=pivot1_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 39=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v54
  have z38 : w 38=pole1 X Y Z a 38*w 44 := by
    have h:=pivot1_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v51
    change w 38=(((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v51
  have z37 : w 37=pole1 X Y Z a 37*w 44 := by
    have h:=pivot1_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 37=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v42
  have z27 : w 27=pole1 X Y Z a 27*w 44 := by
    have h:=pivot1_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 27=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v12
  have z61 : w 61=pole1 X Y Z a 61*w 44 := by
    have h:=pivot1_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 61=((1)/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v18
  have z35 : w 35=pole1 X Y Z a 35*w 44 := by
    have h:=pivot1_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 35=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z62 : w 62=pole1 X Y Z a 62*w 44 := by
    have h:=pivot1_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 62=(((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole1 X Y Z a 4*w 44 := by
    have h:=pivot1_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 4=((1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole1 X Y Z a 57*w 44 := by
    have h:=pivot1_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X*Z))*v22
  have z55 : w 55=pole1 X Y Z a 55*w 44 := by
    have h:=pivot1_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 55=(((-1))/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v18
  have z11 : w 11=pole1 X Y Z a 11*w 44 := by
    have h:=pivot1_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 11=((1)/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v48
  have z9 : w 9=pole1 X Y Z a 9*w 44 := by
    have h:=pivot1_14 X Y Z a hX hY hZ w hw
    change w 9=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole1 X Y Z a 36*w 44 := by
    have h:=pivot1_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole1 X Y Z a 32*w 44 := by
    have h:=pivot1_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole1 X Y Z a 34*w 44 := by
    have h:=pivot1_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole1 X Y Z a 60*w 44 := by
    have h:=pivot1_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole1 X Y Z a 6*w 44 := by
    have h:=pivot1_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole1 X Y Z a 2*w 44 := by
    have h:=pivot1_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole1 X Y Z a 64*w 44 := by
    have h:=pivot1_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole1 X Y Z a 33*w 44 := by
    have h:=pivot1_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole1 X Y Z a 30*w 44 := by
    have h:=pivot1_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole1 X Y Z a 65*w 44 := by
    have h:=pivot1_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole1 X Y Z a 3*w 44 := by
    have h:=pivot1_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole1 X Y Z a 1*w 44 := by
    have h:=pivot1_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole1 X Y Z a 63*w 44 := by
    have h:=pivot1_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole1 X Y Z a 0*w 44 := by
    have h:=pivot1_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case1

theorem kernel_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole2 X Y Z a j*w 44 := by
  have z53 : w 53=pole2 X Y Z a 53*w 44 := by
    have h:=pivot2_64 X Y Z a hX hY hZ w hw
    change w 53=((1)/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole2 X Y Z a 47*w 44 := by
    have h:=pivot2_63 X Y Z a hX hY hZ w hw
    change w 47=((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole2 X Y Z a 41*w 44 := by
    have h:=pivot2_62 X Y Z a hX hY hZ w hw
    change w 41=((1*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole2 X Y Z a 50*w 44 := by
    have h:=pivot2_61 X Y Z a hX hY hZ w hw
    change w 50=((-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole2 X Y Z a 14*w 44 := by
    have h:=pivot2_60 X Y Z a hX hY hZ w hw
    change w 14=((1*X)/(Y^2*Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole2 X Y Z a 40*w 44 := by
    have h:=pivot2_59 X Y Z a hX hY hZ w hw
    change w 40=(1 + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole2 X Y Z a 25*w 44 := by
    have h:=pivot2_58 X Y Z a hX hY hZ w hw
    change w 25=(((-1))/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (2)/(Z) + (-1) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole2 X Y Z a 49*w 44 := by
    have h:=pivot2_57 X Y Z a hX hY hZ w hw
    change w 49=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole2 X Y Z a 19*w 44 := by
    have h:=pivot2_56 X Y Z a hX hY hZ w hw
    change w 19=(((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole2 X Y Z a 52*w 44 := by
    have h:=pivot2_55 X Y Z a hX hY hZ w hw
    change w 52=(((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole2 X Y Z a 13*w 44 := by
    have h:=pivot2_54 X Y Z a hX hY hZ w hw
    change w 13=(((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole2 X Y Z a 26*w 44 := by
    have h:=pivot2_53 X Y Z a hX hY hZ w hw
    change w 26=(((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole2 X Y Z a 43*w 44 := by
    have h:=pivot2_52 X Y Z a hX hY hZ w hw
    change w 43=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole2 X Y Z a 23*w 44 := by
    have h:=pivot2_51 X Y Z a hX hY hZ w hw
    change w 23=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole2 X Y Z a 21*w 44 := by
    have h:=pivot2_50 X Y Z a hX hY hZ w hw
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole2 X Y Z a 56*w 44 := by
    have h:=pivot2_49 X Y Z a hX hY hZ w hw
    change w 56=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole2 X Y Z a 12*w 44 := by
    have h:=pivot2_48 X Y Z a hX hY hZ w hw
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole2 X Y Z a 10*w 44 := by
    have h:=pivot2_47 X Y Z a hX hY hZ w hw
    change w 10=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole2 X Y Z a 45*w 44 := by
    have h:=pivot2_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole2 X Y Z a 51*w 44 := by
    have h:=pivot2_45 X Y Z a hX hY hZ w hw
    change w 51=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole2 X Y Z a 17*w 44 := by
    have h:=pivot2_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=((-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=(1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole2 X Y Z a 16*w 44 := by
    have h:=pivot2_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole2 X Y Z a 15*w 44 := by
    have h:=pivot2_42 X Y Z a hX hY hZ w hw
    change w 15=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole2 X Y Z a 20*w 44 := by
    have h:=pivot2_41 X Y Z a hX hY hZ w hw
    change w 20=(((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole2 X Y Z a 46*w 44 := by
    have h:=pivot2_40 X Y Z a hX hY hZ w hw
    change w 46=((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole2 X Y Z a 48*w 44 := by
    have h:=pivot2_39 X Y Z a hX hY hZ w hw
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole2 X Y Z a 54*w 44 := by
    have h:=pivot2_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole2 X Y Z a 18*w 44 := by
    have h:=pivot2_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole2 X Y Z a 42*w 44 := by
    have h:=pivot2_36 X Y Z a hX hY hZ w hw
    change w 42=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole2 X Y Z a 5*w 44 := by
    have h:=pivot2_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 5=(((-1))/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v48
  have z31 : w 31=pole2 X Y Z a 31*w 44 := by
    have h:=pivot2_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 31=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z29 : w 29=pole2 X Y Z a 29*w 44 := by
    have h:=pivot2_33 X Y Z a hX hY hZ w hw
    change w 29=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole2 X Y Z a 28*w 44 := by
    have h:=pivot2_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v15
    change w 28=((1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v15
  have z24 : w 24=pole2 X Y Z a 24*w 44 := by
    have h:=pivot2_31 X Y Z a hX hY hZ w hw
    change w 24=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole2 X Y Z a 8*w 44 := by
    have h:=pivot2_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 8=((1)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v21
  have z7 : w 7=pole2 X Y Z a 7*w 44 := by
    have h:=pivot2_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 7=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z59 : w 59=pole2 X Y Z a 59*w 44 := by
    have h:=pivot2_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 59=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z58 : w 58=pole2 X Y Z a 58*w 44 := by
    have h:=pivot2_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v45
    change w 58=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v45
  have z22 : w 22=pole2 X Y Z a 22*w 44 := by
    have h:=pivot2_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v42
  have z39 : w 39=pole2 X Y Z a 39*w 44 := by
    have h:=pivot2_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 39=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v54
  have z38 : w 38=pole2 X Y Z a 38*w 44 := by
    have h:=pivot2_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v51
    change w 38=(((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v51
  have z37 : w 37=pole2 X Y Z a 37*w 44 := by
    have h:=pivot2_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 37=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v42
  have z27 : w 27=pole2 X Y Z a 27*w 44 := by
    have h:=pivot2_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 27=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v12
  have z61 : w 61=pole2 X Y Z a 61*w 44 := by
    have h:=pivot2_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 61=((1)/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v18
  have z35 : w 35=pole2 X Y Z a 35*w 44 := by
    have h:=pivot2_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 35=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z62 : w 62=pole2 X Y Z a 62*w 44 := by
    have h:=pivot2_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 62=(((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole2 X Y Z a 4*w 44 := by
    have h:=pivot2_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 4=((1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole2 X Y Z a 57*w 44 := by
    have h:=pivot2_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X*Z))*v22
  have z55 : w 55=pole2 X Y Z a 55*w 44 := by
    have h:=pivot2_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 55=((1)/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v18
  have z11 : w 11=pole2 X Y Z a 11*w 44 := by
    have h:=pivot2_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 11=(((-1))/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v48
  have z9 : w 9=pole2 X Y Z a 9*w 44 := by
    have h:=pivot2_14 X Y Z a hX hY hZ w hw
    change w 9=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole2 X Y Z a 36*w 44 := by
    have h:=pivot2_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole2 X Y Z a 32*w 44 := by
    have h:=pivot2_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole2 X Y Z a 34*w 44 := by
    have h:=pivot2_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole2 X Y Z a 60*w 44 := by
    have h:=pivot2_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole2 X Y Z a 6*w 44 := by
    have h:=pivot2_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole2 X Y Z a 2*w 44 := by
    have h:=pivot2_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole2 X Y Z a 64*w 44 := by
    have h:=pivot2_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole2 X Y Z a 33*w 44 := by
    have h:=pivot2_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole2 X Y Z a 30*w 44 := by
    have h:=pivot2_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole2 X Y Z a 65*w 44 := by
    have h:=pivot2_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole2 X Y Z a 3*w 44 := by
    have h:=pivot2_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole2 X Y Z a 1*w 44 := by
    have h:=pivot2_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole2 X Y Z a 63*w 44 := by
    have h:=pivot2_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole2 X Y Z a 0*w 44 := by
    have h:=pivot2_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case2

theorem kernel_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (-1) (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole3 X Y Z a j*w 44 := by
  have z53 : w 53=pole3 X Y Z a 53*w 44 := by
    have h:=pivot3_64 X Y Z a hX hY hZ w hw
    change w 53=((2)/(X*Z) + (1)/(X) + ((-1)*Y*a)/(X*Z) + (1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole3 X Y Z a 47*w 44 := by
    have h:=pivot3_63 X Y Z a hX hY hZ w hw
    change w 47=((1)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole3 X Y Z a 41*w 44 := by
    have h:=pivot3_62 X Y Z a hX hY hZ w hw
    change w 41=((1*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole3 X Y Z a 50*w 44 := by
    have h:=pivot3_61 X Y Z a hX hY hZ w hw
    change w 50=(((-2))/(Z) + (-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole3 X Y Z a 14*w 44 := by
    have h:=pivot3_60 X Y Z a hX hY hZ w hw
    change w 14=((1*X)/(Y^2*Z) + (2*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole3 X Y Z a 40*w 44 := by
    have h:=pivot3_59 X Y Z a hX hY hZ w hw
    change w 40=((2)/(Z) + 1 + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole3 X Y Z a 25*w 44 := by
    have h:=pivot3_58 X Y Z a hX hY hZ w hw
    change w 25=(((-2))/(X*Z) + ((-1))/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (-1) + (1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole3 X Y Z a 49*w 44 := by
    have h:=pivot3_57 X Y Z a hX hY hZ w hw
    change w 49=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole3 X Y Z a 19*w 44 := by
    have h:=pivot3_56 X Y Z a hX hY hZ w hw
    change w 19=(((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole3 X Y Z a 52*w 44 := by
    have h:=pivot3_55 X Y Z a hX hY hZ w hw
    change w 52=(((-1)*X)/(Y^2*Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole3 X Y Z a 13*w 44 := by
    have h:=pivot3_54 X Y Z a hX hY hZ w hw
    change w 13=(((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole3 X Y Z a 26*w 44 := by
    have h:=pivot3_53 X Y Z a hX hY hZ w hw
    change w 26=(((-1)*Y^2)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole3 X Y Z a 43*w 44 := by
    have h:=pivot3_52 X Y Z a hX hY hZ w hw
    change w 43=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole3 X Y Z a 23*w 44 := by
    have h:=pivot3_51 X Y Z a hX hY hZ w hw
    change w 23=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole3 X Y Z a 21*w 44 := by
    have h:=pivot3_50 X Y Z a hX hY hZ w hw
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole3 X Y Z a 56*w 44 := by
    have h:=pivot3_49 X Y Z a hX hY hZ w hw
    change w 56=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole3 X Y Z a 12*w 44 := by
    have h:=pivot3_48 X Y Z a hX hY hZ w hw
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole3 X Y Z a 10*w 44 := by
    have h:=pivot3_47 X Y Z a hX hY hZ w hw
    change w 10=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole3 X Y Z a 45*w 44 := by
    have h:=pivot3_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole3 X Y Z a 51*w 44 := by
    have h:=pivot3_45 X Y Z a hX hY hZ w hw
    change w 51=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole3 X Y Z a 17*w 44 := by
    have h:=pivot3_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=(((-2))/(Z) + (-1) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=((2)/(Z) + 1 + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole3 X Y Z a 16*w 44 := by
    have h:=pivot3_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole3 X Y Z a 15*w 44 := by
    have h:=pivot3_42 X Y Z a hX hY hZ w hw
    change w 15=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole3 X Y Z a 20*w 44 := by
    have h:=pivot3_41 X Y Z a hX hY hZ w hw
    change w 20=(((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole3 X Y Z a 46*w 44 := by
    have h:=pivot3_40 X Y Z a hX hY hZ w hw
    change w 46=((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole3 X Y Z a 48*w 44 := by
    have h:=pivot3_39 X Y Z a hX hY hZ w hw
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole3 X Y Z a 54*w 44 := by
    have h:=pivot3_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole3 X Y Z a 18*w 44 := by
    have h:=pivot3_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole3 X Y Z a 42*w 44 := by
    have h:=pivot3_36 X Y Z a hX hY hZ w hw
    change w 42=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole3 X Y Z a 5*w 44 := by
    have h:=pivot3_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 5=(((-1))/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v48
  have z31 : w 31=pole3 X Y Z a 31*w 44 := by
    have h:=pivot3_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 31=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z29 : w 29=pole3 X Y Z a 29*w 44 := by
    have h:=pivot3_33 X Y Z a hX hY hZ w hw
    change w 29=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole3 X Y Z a 28*w 44 := by
    have h:=pivot3_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v15
    change w 28=((1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v15
  have z24 : w 24=pole3 X Y Z a 24*w 44 := by
    have h:=pivot3_31 X Y Z a hX hY hZ w hw
    change w 24=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole3 X Y Z a 8*w 44 := by
    have h:=pivot3_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v21
    change w 8=((1)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v21
  have z7 : w 7=pole3 X Y Z a 7*w 44 := by
    have h:=pivot3_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 7=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z59 : w 59=pole3 X Y Z a 59*w 44 := by
    have h:=pivot3_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 59=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z58 : w 58=pole3 X Y Z a 58*w 44 := by
    have h:=pivot3_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v45
    change w 58=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v45
  have z22 : w 22=pole3 X Y Z a 22*w 44 := by
    have h:=pivot3_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v42
  have z39 : w 39=pole3 X Y Z a 39*w 44 := by
    have h:=pivot3_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 39=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v54
  have z38 : w 38=pole3 X Y Z a 38*w 44 := by
    have h:=pivot3_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v51
    change w 38=(((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v51
  have z37 : w 37=pole3 X Y Z a 37*w 44 := by
    have h:=pivot3_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 37=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v42
  have z27 : w 27=pole3 X Y Z a 27*w 44 := by
    have h:=pivot3_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 27=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v12
  have z61 : w 61=pole3 X Y Z a 61*w 44 := by
    have h:=pivot3_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 61=((1)/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v18
  have z35 : w 35=pole3 X Y Z a 35*w 44 := by
    have h:=pivot3_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 35=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z62 : w 62=pole3 X Y Z a 62*w 44 := by
    have h:=pivot3_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v12
    change w 62=(((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole3 X Y Z a 4*w 44 := by
    have h:=pivot3_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v54
    change w 4=((1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole3 X Y Z a 57*w 44 := by
    have h:=pivot3_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Y^2)/(X*Z))*v22
  have z55 : w 55=pole3 X Y Z a 55*w 44 := by
    have h:=pivot3_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v18
    change w 55=((1)/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v18
  have z11 : w 11=pole3 X Y Z a 11*w 44 := by
    have h:=pivot3_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v48
    change w 11=(((-1))/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(X*Y^2))*v48
  have z9 : w 9=pole3 X Y Z a 9*w 44 := by
    have h:=pivot3_14 X Y Z a hX hY hZ w hw
    change w 9=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole3 X Y Z a 36*w 44 := by
    have h:=pivot3_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole3 X Y Z a 32*w 44 := by
    have h:=pivot3_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole3 X Y Z a 34*w 44 := by
    have h:=pivot3_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole3 X Y Z a 60*w 44 := by
    have h:=pivot3_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole3 X Y Z a 6*w 44 := by
    have h:=pivot3_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole3 X Y Z a 2*w 44 := by
    have h:=pivot3_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole3 X Y Z a 64*w 44 := by
    have h:=pivot3_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole3 X Y Z a 33*w 44 := by
    have h:=pivot3_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole3 X Y Z a 30*w 44 := by
    have h:=pivot3_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole3 X Y Z a 65*w 44 := by
    have h:=pivot3_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole3 X Y Z a 3*w 44 := by
    have h:=pivot3_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole3 X Y Z a 1*w 44 := by
    have h:=pivot3_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole3 X Y Z a 63*w 44 := by
    have h:=pivot3_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole3 X Y Z a 0*w 44 := by
    have h:=pivot3_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case3

theorem kernel_case4 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole4 X Y Z a j*w 44 := by
  have z53 : w 53=pole4 X Y Z a 53*w 44 := by
    have h:=pivot4_64 X Y Z a hX hY hZ w hw
    change w 53=(((-1))/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole4 X Y Z a 47*w 44 := by
    have h:=pivot4_63 X Y Z a hX hY hZ w hw
    change w 47=((1)/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole4 X Y Z a 41*w 44 := by
    have h:=pivot4_62 X Y Z a hX hY hZ w hw
    change w 41=(((-1)*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole4 X Y Z a 50*w 44 := by
    have h:=pivot4_61 X Y Z a hX hY hZ w hw
    change w 50=((-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole4 X Y Z a 14*w 44 := by
    have h:=pivot4_60 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*X)/(Y^2*Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole4 X Y Z a 40*w 44 := by
    have h:=pivot4_59 X Y Z a hX hY hZ w hw
    change w 40=(1 + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole4 X Y Z a 25*w 44 := by
    have h:=pivot4_58 X Y Z a hX hY hZ w hw
    change w 25=((1)/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (2)/(Z) + (-1) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole4 X Y Z a 49*w 44 := by
    have h:=pivot4_57 X Y Z a hX hY hZ w hw
    change w 49=(((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole4 X Y Z a 19*w 44 := by
    have h:=pivot4_56 X Y Z a hX hY hZ w hw
    change w 19=(((-1))/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole4 X Y Z a 52*w 44 := by
    have h:=pivot4_55 X Y Z a hX hY hZ w hw
    change w 52=((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole4 X Y Z a 13*w 44 := by
    have h:=pivot4_54 X Y Z a hX hY hZ w hw
    change w 13=((1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole4 X Y Z a 26*w 44 := by
    have h:=pivot4_53 X Y Z a hX hY hZ w hw
    change w 26=(((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole4 X Y Z a 43*w 44 := by
    have h:=pivot4_52 X Y Z a hX hY hZ w hw
    change w 43=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole4 X Y Z a 23*w 44 := by
    have h:=pivot4_51 X Y Z a hX hY hZ w hw
    change w 23=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole4 X Y Z a 21*w 44 := by
    have h:=pivot4_50 X Y Z a hX hY hZ w hw
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole4 X Y Z a 56*w 44 := by
    have h:=pivot4_49 X Y Z a hX hY hZ w hw
    change w 56=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole4 X Y Z a 12*w 44 := by
    have h:=pivot4_48 X Y Z a hX hY hZ w hw
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole4 X Y Z a 10*w 44 := by
    have h:=pivot4_47 X Y Z a hX hY hZ w hw
    change w 10=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole4 X Y Z a 45*w 44 := by
    have h:=pivot4_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole4 X Y Z a 51*w 44 := by
    have h:=pivot4_45 X Y Z a hX hY hZ w hw
    change w 51=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole4 X Y Z a 17*w 44 := by
    have h:=pivot4_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=((-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=(1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole4 X Y Z a 16*w 44 := by
    have h:=pivot4_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=(((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole4 X Y Z a 15*w 44 := by
    have h:=pivot4_42 X Y Z a hX hY hZ w hw
    change w 15=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole4 X Y Z a 20*w 44 := by
    have h:=pivot4_41 X Y Z a hX hY hZ w hw
    change w 20=(((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole4 X Y Z a 46*w 44 := by
    have h:=pivot4_40 X Y Z a hX hY hZ w hw
    change w 46=((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole4 X Y Z a 48*w 44 := by
    have h:=pivot4_39 X Y Z a hX hY hZ w hw
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole4 X Y Z a 54*w 44 := by
    have h:=pivot4_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole4 X Y Z a 18*w 44 := by
    have h:=pivot4_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole4 X Y Z a 42*w 44 := by
    have h:=pivot4_36 X Y Z a hX hY hZ w hw
    change w 42=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole4 X Y Z a 5*w 44 := by
    have h:=pivot4_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 5=((1)/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v48
  have z31 : w 31=pole4 X Y Z a 31*w 44 := by
    have h:=pivot4_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 31=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z29 : w 29=pole4 X Y Z a 29*w 44 := by
    have h:=pivot4_33 X Y Z a hX hY hZ w hw
    change w 29=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole4 X Y Z a 28*w 44 := by
    have h:=pivot4_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v15
    change w 28=(((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v15
  have z24 : w 24=pole4 X Y Z a 24*w 44 := by
    have h:=pivot4_31 X Y Z a hX hY hZ w hw
    change w 24=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole4 X Y Z a 8*w 44 := by
    have h:=pivot4_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 8=((1)/(Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v21
  have z7 : w 7=pole4 X Y Z a 7*w 44 := by
    have h:=pivot4_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 7=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z59 : w 59=pole4 X Y Z a 59*w 44 := by
    have h:=pivot4_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 59=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z58 : w 58=pole4 X Y Z a 58*w 44 := by
    have h:=pivot4_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v45
    change w 58=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v45
  have z22 : w 22=pole4 X Y Z a 22*w 44 := by
    have h:=pivot4_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v42
  have z39 : w 39=pole4 X Y Z a 39*w 44 := by
    have h:=pivot4_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 39=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v54
  have z38 : w 38=pole4 X Y Z a 38*w 44 := by
    have h:=pivot4_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v51
    change w 38=((1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v51
  have z37 : w 37=pole4 X Y Z a 37*w 44 := by
    have h:=pivot4_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 37=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v42
  have z27 : w 27=pole4 X Y Z a 27*w 44 := by
    have h:=pivot4_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 27=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v12
  have z61 : w 61=pole4 X Y Z a 61*w 44 := by
    have h:=pivot4_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 61=(((-1))/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v18
  have z35 : w 35=pole4 X Y Z a 35*w 44 := by
    have h:=pivot4_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 35=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z62 : w 62=pole4 X Y Z a 62*w 44 := by
    have h:=pivot4_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 62=((1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole4 X Y Z a 4*w 44 := by
    have h:=pivot4_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 4=(((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole4 X Y Z a 57*w 44 := by
    have h:=pivot4_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X*Z))*v22
  have z55 : w 55=pole4 X Y Z a 55*w 44 := by
    have h:=pivot4_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 55=(((-1))/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v18
  have z11 : w 11=pole4 X Y Z a 11*w 44 := by
    have h:=pivot4_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 11=((1)/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v48
  have z9 : w 9=pole4 X Y Z a 9*w 44 := by
    have h:=pivot4_14 X Y Z a hX hY hZ w hw
    change w 9=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole4 X Y Z a 36*w 44 := by
    have h:=pivot4_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole4 X Y Z a 32*w 44 := by
    have h:=pivot4_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole4 X Y Z a 34*w 44 := by
    have h:=pivot4_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole4 X Y Z a 60*w 44 := by
    have h:=pivot4_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole4 X Y Z a 6*w 44 := by
    have h:=pivot4_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole4 X Y Z a 2*w 44 := by
    have h:=pivot4_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole4 X Y Z a 64*w 44 := by
    have h:=pivot4_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole4 X Y Z a 33*w 44 := by
    have h:=pivot4_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole4 X Y Z a 30*w 44 := by
    have h:=pivot4_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole4 X Y Z a 65*w 44 := by
    have h:=pivot4_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole4 X Y Z a 3*w 44 := by
    have h:=pivot4_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole4 X Y Z a 1*w 44 := by
    have h:=pivot4_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole4 X Y Z a 63*w 44 := by
    have h:=pivot4_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole4 X Y Z a 0*w 44 := by
    have h:=pivot4_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case4

theorem kernel_case5 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole5 X Y Z a j*w 44 := by
  have z53 : w 53=pole5 X Y Z a 53*w 44 := by
    have h:=pivot5_64 X Y Z a hX hY hZ w hw
    change w 53=(((-2))/(X*Z) + ((-1))/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1))/(Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole5 X Y Z a 47*w 44 := by
    have h:=pivot5_63 X Y Z a hX hY hZ w hw
    change w 47=((1)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole5 X Y Z a 41*w 44 := by
    have h:=pivot5_62 X Y Z a hX hY hZ w hw
    change w 41=(((-1)*Y*a)/(X*Z) + (1)/(Y^2*Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole5 X Y Z a 50*w 44 := by
    have h:=pivot5_61 X Y Z a hX hY hZ w hw
    change w 50=(((-2))/(Z) + (-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole5 X Y Z a 14*w 44 := by
    have h:=pivot5_60 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole5 X Y Z a 40*w 44 := by
    have h:=pivot5_59 X Y Z a hX hY hZ w hw
    change w 40=((2)/(Z) + 1 + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole5 X Y Z a 25*w 44 := by
    have h:=pivot5_58 X Y Z a hX hY hZ w hw
    change w 25=((2)/(X*Z) + (1)/(X) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (-1) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole5 X Y Z a 49*w 44 := by
    have h:=pivot5_57 X Y Z a hX hY hZ w hw
    change w 49=(((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole5 X Y Z a 19*w 44 := by
    have h:=pivot5_56 X Y Z a hX hY hZ w hw
    change w 19=(((-1))/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole5 X Y Z a 52*w 44 := by
    have h:=pivot5_55 X Y Z a hX hY hZ w hw
    change w 52=((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole5 X Y Z a 13*w 44 := by
    have h:=pivot5_54 X Y Z a hX hY hZ w hw
    change w 13=((1*Y^2)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-1))/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole5 X Y Z a 26*w 44 := by
    have h:=pivot5_53 X Y Z a hX hY hZ w hw
    change w 26=(((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole5 X Y Z a 43*w 44 := by
    have h:=pivot5_52 X Y Z a hX hY hZ w hw
    change w 43=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole5 X Y Z a 23*w 44 := by
    have h:=pivot5_51 X Y Z a hX hY hZ w hw
    change w 23=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole5 X Y Z a 21*w 44 := by
    have h:=pivot5_50 X Y Z a hX hY hZ w hw
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole5 X Y Z a 56*w 44 := by
    have h:=pivot5_49 X Y Z a hX hY hZ w hw
    change w 56=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole5 X Y Z a 12*w 44 := by
    have h:=pivot5_48 X Y Z a hX hY hZ w hw
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole5 X Y Z a 10*w 44 := by
    have h:=pivot5_47 X Y Z a hX hY hZ w hw
    change w 10=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole5 X Y Z a 45*w 44 := by
    have h:=pivot5_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole5 X Y Z a 51*w 44 := by
    have h:=pivot5_45 X Y Z a hX hY hZ w hw
    change w 51=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole5 X Y Z a 17*w 44 := by
    have h:=pivot5_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=(((-2))/(Z) + (-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=((2)/(Z) + 1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole5 X Y Z a 16*w 44 := by
    have h:=pivot5_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=(((-1)*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=((1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole5 X Y Z a 15*w 44 := by
    have h:=pivot5_42 X Y Z a hX hY hZ w hw
    change w 15=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole5 X Y Z a 20*w 44 := by
    have h:=pivot5_41 X Y Z a hX hY hZ w hw
    change w 20=(((-1))/(Z) + (1*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole5 X Y Z a 46*w 44 := by
    have h:=pivot5_40 X Y Z a hX hY hZ w hw
    change w 46=((1)/(Z) + ((-1)*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole5 X Y Z a 48*w 44 := by
    have h:=pivot5_39 X Y Z a hX hY hZ w hw
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole5 X Y Z a 54*w 44 := by
    have h:=pivot5_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole5 X Y Z a 18*w 44 := by
    have h:=pivot5_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole5 X Y Z a 42*w 44 := by
    have h:=pivot5_36 X Y Z a hX hY hZ w hw
    change w 42=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole5 X Y Z a 5*w 44 := by
    have h:=pivot5_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 5=((1)/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v48
  have z31 : w 31=pole5 X Y Z a 31*w 44 := by
    have h:=pivot5_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 31=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z29 : w 29=pole5 X Y Z a 29*w 44 := by
    have h:=pivot5_33 X Y Z a hX hY hZ w hw
    change w 29=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole5 X Y Z a 28*w 44 := by
    have h:=pivot5_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v15
    change w 28=(((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v15
  have z24 : w 24=pole5 X Y Z a 24*w 44 := by
    have h:=pivot5_31 X Y Z a hX hY hZ w hw
    change w 24=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole5 X Y Z a 8*w 44 := by
    have h:=pivot5_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 8=((1)/(Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v21
  have z7 : w 7=pole5 X Y Z a 7*w 44 := by
    have h:=pivot5_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 7=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z59 : w 59=pole5 X Y Z a 59*w 44 := by
    have h:=pivot5_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 59=(((-1))/(Y^2*Z) + (1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v54
  have z58 : w 58=pole5 X Y Z a 58*w 44 := by
    have h:=pivot5_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v45
    change w 58=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v45
  have z22 : w 22=pole5 X Y Z a 22*w 44 := by
    have h:=pivot5_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(Y^2))*v42
  have z39 : w 39=pole5 X Y Z a 39*w 44 := by
    have h:=pivot5_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 39=(((-1))/(Z) + (1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v54
  have z38 : w 38=pole5 X Y Z a 38*w 44 := by
    have h:=pivot5_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v51
    change w 38=((1*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*X)/(Y^2))*v51
  have z37 : w 37=pole5 X Y Z a 37*w 44 := by
    have h:=pivot5_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=(((-1)*Y^2)/(Z))*w 44 at v42
    change w 37=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v42
  have z27 : w 27=pole5 X Y Z a 27*w 44 := by
    have h:=pivot5_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 27=((1)/(Z) + ((-1)*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X))*v12
  have z61 : w 61=pole5 X Y Z a 61*w 44 := by
    have h:=pivot5_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 61=(((-1))/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v18
  have z35 : w 35=pole5 X Y Z a 35*w 44 := by
    have h:=pivot5_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 35=((1)/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(X*Y^2))*v12
  have z62 : w 62=pole5 X Y Z a 62*w 44 := by
    have h:=pivot5_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + ((-1)*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 62=((1*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole5 X Y Z a 4*w 44 := by
    have h:=pivot5_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + (1*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 4=(((-1)*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole5 X Y Z a 57*w 44 := by
    have h:=pivot5_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X*Z))*v22
  have z55 : w 55=pole5 X Y Z a 55*w 44 := by
    have h:=pivot5_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=(((-1)*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 55=(((-1))/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v18
  have z11 : w 11=pole5 X Y Z a 11*w 44 := by
    have h:=pivot5_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=((1*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 11=((1)/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v48
  have z9 : w 9=pole5 X Y Z a 9*w 44 := by
    have h:=pivot5_14 X Y Z a hX hY hZ w hw
    change w 9=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole5 X Y Z a 36*w 44 := by
    have h:=pivot5_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole5 X Y Z a 32*w 44 := by
    have h:=pivot5_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole5 X Y Z a 34*w 44 := by
    have h:=pivot5_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole5 X Y Z a 60*w 44 := by
    have h:=pivot5_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole5 X Y Z a 6*w 44 := by
    have h:=pivot5_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole5 X Y Z a 2*w 44 := by
    have h:=pivot5_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole5 X Y Z a 64*w 44 := by
    have h:=pivot5_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole5 X Y Z a 33*w 44 := by
    have h:=pivot5_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole5 X Y Z a 30*w 44 := by
    have h:=pivot5_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole5 X Y Z a 65*w 44 := by
    have h:=pivot5_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole5 X Y Z a 3*w 44 := by
    have h:=pivot5_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole5 X Y Z a 1*w 44 := by
    have h:=pivot5_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole5 X Y Z a 63*w 44 := by
    have h:=pivot5_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole5 X Y Z a 0*w 44 := by
    have h:=pivot5_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case5

theorem kernel_case6 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole6 X Y Z a j*w 44 := by
  have z53 : w 53=pole6 X Y Z a 53*w 44 := by
    have h:=pivot6_64 X Y Z a hX hY hZ w hw
    change w 53=(((-2))/(X*Z) + (1)/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole6 X Y Z a 47*w 44 := by
    have h:=pivot6_63 X Y Z a hX hY hZ w hw
    change w 47=(((-1))/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole6 X Y Z a 41*w 44 := by
    have h:=pivot6_62 X Y Z a hX hY hZ w hw
    change w 41=(((-1)*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole6 X Y Z a 50*w 44 := by
    have h:=pivot6_61 X Y Z a hX hY hZ w hw
    change w 50=((2)/(Z) + (-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole6 X Y Z a 14*w 44 := by
    have h:=pivot6_60 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*X)/(Y^2*Z) + ((-2)*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole6 X Y Z a 40*w 44 := by
    have h:=pivot6_59 X Y Z a hX hY hZ w hw
    change w 40=(((-2))/(Z) + 1 + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole6 X Y Z a 25*w 44 := by
    have h:=pivot6_58 X Y Z a hX hY hZ w hw
    change w 25=((2)/(X*Z) + ((-1))/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + (-1) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole6 X Y Z a 49*w 44 := by
    have h:=pivot6_57 X Y Z a hX hY hZ w hw
    change w 49=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole6 X Y Z a 19*w 44 := by
    have h:=pivot6_56 X Y Z a hX hY hZ w hw
    change w 19=((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole6 X Y Z a 52*w 44 := by
    have h:=pivot6_55 X Y Z a hX hY hZ w hw
    change w 52=((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole6 X Y Z a 13*w 44 := by
    have h:=pivot6_54 X Y Z a hX hY hZ w hw
    change w 13=((1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole6 X Y Z a 26*w 44 := by
    have h:=pivot6_53 X Y Z a hX hY hZ w hw
    change w 26=((1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole6 X Y Z a 43*w 44 := by
    have h:=pivot6_52 X Y Z a hX hY hZ w hw
    change w 43=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole6 X Y Z a 23*w 44 := by
    have h:=pivot6_51 X Y Z a hX hY hZ w hw
    change w 23=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole6 X Y Z a 21*w 44 := by
    have h:=pivot6_50 X Y Z a hX hY hZ w hw
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole6 X Y Z a 56*w 44 := by
    have h:=pivot6_49 X Y Z a hX hY hZ w hw
    change w 56=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole6 X Y Z a 12*w 44 := by
    have h:=pivot6_48 X Y Z a hX hY hZ w hw
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole6 X Y Z a 10*w 44 := by
    have h:=pivot6_47 X Y Z a hX hY hZ w hw
    change w 10=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole6 X Y Z a 45*w 44 := by
    have h:=pivot6_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole6 X Y Z a 51*w 44 := by
    have h:=pivot6_45 X Y Z a hX hY hZ w hw
    change w 51=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole6 X Y Z a 17*w 44 := by
    have h:=pivot6_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=((2)/(Z) + (-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + (1*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=(((-2))/(Z) + 1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + ((-1)*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole6 X Y Z a 16*w 44 := by
    have h:=pivot6_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole6 X Y Z a 15*w 44 := by
    have h:=pivot6_42 X Y Z a hX hY hZ w hw
    change w 15=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole6 X Y Z a 20*w 44 := by
    have h:=pivot6_41 X Y Z a hX hY hZ w hw
    change w 20=((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole6 X Y Z a 46*w 44 := by
    have h:=pivot6_40 X Y Z a hX hY hZ w hw
    change w 46=(((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole6 X Y Z a 48*w 44 := by
    have h:=pivot6_39 X Y Z a hX hY hZ w hw
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole6 X Y Z a 54*w 44 := by
    have h:=pivot6_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole6 X Y Z a 18*w 44 := by
    have h:=pivot6_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole6 X Y Z a 42*w 44 := by
    have h:=pivot6_36 X Y Z a hX hY hZ w hw
    change w 42=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole6 X Y Z a 5*w 44 := by
    have h:=pivot6_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 5=((1)/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v48
  have z31 : w 31=pole6 X Y Z a 31*w 44 := by
    have h:=pivot6_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 31=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z29 : w 29=pole6 X Y Z a 29*w 44 := by
    have h:=pivot6_33 X Y Z a hX hY hZ w hw
    change w 29=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole6 X Y Z a 28*w 44 := by
    have h:=pivot6_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v15
    change w 28=(((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v15
  have z24 : w 24=pole6 X Y Z a 24*w 44 := by
    have h:=pivot6_31 X Y Z a hX hY hZ w hw
    change w 24=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole6 X Y Z a 8*w 44 := by
    have h:=pivot6_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 8=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v21
  have z7 : w 7=pole6 X Y Z a 7*w 44 := by
    have h:=pivot6_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 7=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z59 : w 59=pole6 X Y Z a 59*w 44 := by
    have h:=pivot6_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 59=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z58 : w 58=pole6 X Y Z a 58*w 44 := by
    have h:=pivot6_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v45
    change w 58=((1)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v45
  have z22 : w 22=pole6 X Y Z a 22*w 44 := by
    have h:=pivot6_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v42
  have z39 : w 39=pole6 X Y Z a 39*w 44 := by
    have h:=pivot6_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 39=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v54
  have z38 : w 38=pole6 X Y Z a 38*w 44 := by
    have h:=pivot6_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v51
    change w 38=((1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v51
  have z37 : w 37=pole6 X Y Z a 37*w 44 := by
    have h:=pivot6_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 37=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v42
  have z27 : w 27=pole6 X Y Z a 27*w 44 := by
    have h:=pivot6_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 27=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v12
  have z61 : w 61=pole6 X Y Z a 61*w 44 := by
    have h:=pivot6_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 61=(((-1))/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v18
  have z35 : w 35=pole6 X Y Z a 35*w 44 := by
    have h:=pivot6_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 35=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z62 : w 62=pole6 X Y Z a 62*w 44 := by
    have h:=pivot6_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 62=((1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole6 X Y Z a 4*w 44 := by
    have h:=pivot6_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 4=(((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole6 X Y Z a 57*w 44 := by
    have h:=pivot6_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X*Z))*v22
  have z55 : w 55=pole6 X Y Z a 55*w 44 := by
    have h:=pivot6_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 55=((1)/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v18
  have z11 : w 11=pole6 X Y Z a 11*w 44 := by
    have h:=pivot6_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 11=(((-1))/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v48
  have z9 : w 9=pole6 X Y Z a 9*w 44 := by
    have h:=pivot6_14 X Y Z a hX hY hZ w hw
    change w 9=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole6 X Y Z a 36*w 44 := by
    have h:=pivot6_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole6 X Y Z a 32*w 44 := by
    have h:=pivot6_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole6 X Y Z a 34*w 44 := by
    have h:=pivot6_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole6 X Y Z a 60*w 44 := by
    have h:=pivot6_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole6 X Y Z a 6*w 44 := by
    have h:=pivot6_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole6 X Y Z a 2*w 44 := by
    have h:=pivot6_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole6 X Y Z a 64*w 44 := by
    have h:=pivot6_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole6 X Y Z a 33*w 44 := by
    have h:=pivot6_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole6 X Y Z a 30*w 44 := by
    have h:=pivot6_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole6 X Y Z a 65*w 44 := by
    have h:=pivot6_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole6 X Y Z a 3*w 44 := by
    have h:=pivot6_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole6 X Y Z a 1*w 44 := by
    have h:=pivot6_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole6 X Y Z a 63*w 44 := by
    have h:=pivot6_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole6 X Y Z a 0*w 44 := by
    have h:=pivot6_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case6

theorem kernel_case7 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 66→ℂ) (hw : coreRows (1) (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole7 X Y Z a j*w 44 := by
  have z53 : w 53=pole7 X Y Z a 53*w 44 := by
    have h:=pivot7_64 X Y Z a hX hY hZ w hw
    change w 53=((1)/(X) + (1*Y*a)/(X*Z) + ((-1)*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1)/(Z) + (1*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z47 : w 47=pole7 X Y Z a 47*w 44 := by
    have h:=pivot7_63 X Y Z a hX hY hZ w hw
    change w 47=(((-1))/(Z) + (1*X)/(Y^2*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + (1*X^3*Y^2)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z41 : w 41=pole7 X Y Z a 41*w 44 := by
    have h:=pivot7_62 X Y Z a hX hY hZ w hw
    change w 41=(((-1)*Y*a)/(X*Z) + ((-1))/(Y^2*Z) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z50 : w 50=pole7 X Y Z a 50*w 44 := by
    have h:=pivot7_61 X Y Z a hX hY hZ w hw
    change w 50=((-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z14 : w 14=pole7 X Y Z a 14*w 44 := by
    have h:=pivot7_60 X Y Z a hX hY hZ w hw
    change w 14=(((-1)*X)/(Y^2*Z) + 1*X + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + (1*X^3)/(Z) + ((-1)*X^3*Y^2)/(Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z40 : w 40=pole7 X Y Z a 40*w 44 := by
    have h:=pivot7_59 X Y Z a hX hY hZ w hw
    change w 40=(1 + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Y^2*Z) + (2*X)/(Z) + (1*X*Y*a)/(Z) + ((-1)*X*Y^2)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + (1*X^2)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^3)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z25 : w 25=pole7 X Y Z a 25*w 44 := by
    have h:=pivot7_58 X Y Z a hX hY hZ w hw
    change w 25=(((-1))/(X) + ((-1))/(Y^2*Z) + ((-1)*a)/(Y*Z) + ((-2))/(Z) + (-1) + ((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-2)*X)/(Z) + ((-1)*X*Y*a)/(Z) + (1*X*Y^2)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^3)/(Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z49 : w 49=pole7 X Y Z a 49*w 44 := by
    have h:=pivot7_57 X Y Z a hX hY hZ w hw
    change w 49=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z19 : w 19=pole7 X Y Z a 19*w 44 := by
    have h:=pivot7_56 X Y Z a hX hY hZ w hw
    change w 19=((1)/(Z) + ((-1)*X)/(Y^2*Z) + (1*X)/(Z) + ((-1)*X*Y^2)/(Z) + ((-2)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-1)*X^2*Y^2)/(Z) + ((-2)*X^3)/(Y^2*Z) + ((-1)*X^3*a)/(Y*Z) + ((-1)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z52 : w 52=pole7 X Y Z a 52*w 44 := by
    have h:=pivot7_55 X Y Z a hX hY hZ w hw
    change w 52=((1*X)/(Y^2*Z) + (1*X*Y^2)/(Z) + (2*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^2*Y^2)/(Z) + (2*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z) + (1*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z13 : w 13=pole7 X Y Z a 13*w 44 := by
    have h:=pivot7_54 X Y Z a hX hY hZ w hw
    change w 13=((1*Y^2)/(X*Z) + (1)/(Y^2*Z) + (1*a)/(Y*Z) + (1)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z26 : w 26=pole7 X Y Z a 26*w 44 := by
    have h:=pivot7_53 X Y Z a hX hY hZ w hw
    change w 26=((1*Y^2)/(Z) + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X*Y^2)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (1*X^3)/(Y^2*Z) + (1*X^3*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z43 : w 43=pole7 X Y Z a 43*w 44 := by
    have h:=pivot7_52 X Y Z a hX hY hZ w hw
    change w 43=((1)/(X*Z) + ((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z23 : w 23=pole7 X Y Z a 23*w 44 := by
    have h:=pivot7_51 X Y Z a hX hY hZ w hw
    change w 23=(((-1))/(X*Z) + (1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z21 : w 21=pole7 X Y Z a 21*w 44 := by
    have h:=pivot7_50 X Y Z a hX hY hZ w hw
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z56 : w 56=pole7 X Y Z a 56*w 44 := by
    have h:=pivot7_49 X Y Z a hX hY hZ w hw
    change w 56=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z12 : w 12=pole7 X Y Z a 12*w 44 := by
    have h:=pivot7_48 X Y Z a hX hY hZ w hw
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z10 : w 10=pole7 X Y Z a 10*w 44 := by
    have h:=pivot7_47 X Y Z a hX hY hZ w hw
    change w 10=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z45 : w 45=pole7 X Y Z a 45*w 44 := by
    have h:=pivot7_46 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v21
  have z51 : w 51=pole7 X Y Z a 51*w 44 := by
    have h:=pivot7_45 X Y Z a hX hY hZ w hw
    change w 51=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z17 : w 17=pole7 X Y Z a 17*w 44 := by
    have h:=pivot7_44 X Y Z a hX hY hZ w hw
    have v50:=z50
    change w 50=((-1) + ((-1)*X)/(Y^2*Z) + ((-1)*X*a)/(Y*Z) + ((-1)*X)/(Z) + (-1)*X + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2*a)/(Y*Z) + ((-2)*X^2)/(Z) + ((-1)*X^2*Y*a)/(Z) + (1*X^2*Y^2)/(Z) + (1*X^3)/(Y^2*Z) + (1*X^3*Y^2)/(Z) + (2*X^4)/(Y^2*Z) + (1*X^4*a)/(Y*Z) + (1*X^4)/(Z) + (2*X^5)/(Y^2*Z) + (1*X^5*a)/(Y*Z))*w 44 at v50
    change w 17=(1 + (1*X)/(Y^2*Z) + (1*X*a)/(Y*Z) + (1*X)/(Z) + 1*X + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2*a)/(Y*Z) + (2*X^2)/(Z) + (1*X^2*Y*a)/(Z) + ((-1)*X^2*Y^2)/(Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^3*Y^2)/(Z) + ((-2)*X^4)/(Y^2*Z) + ((-1)*X^4*a)/(Y*Z) + ((-1)*X^4)/(Z) + ((-2)*X^5)/(Y^2*Z) + ((-1)*X^5*a)/(Y*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v50
  have z16 : w 16=pole7 X Y Z a 16*w 44 := by
    have h:=pivot7_43 X Y Z a hX hY hZ w hw
    have v49:=z49
    change w 49=((1*Y*a)/(Z) + (1*X)/(Y^2*Z) + (1*X)/(Z) + (1*X*Y*a)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^2)/(Z) + (1*X^3)/(Y^2*Z))*w 44 at v49
    change w 16=(((-1)*Y*a)/(Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X)/(Z) + ((-1)*X*Y*a)/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v49
  have z15 : w 15=pole7 X Y Z a 15*w 44 := by
    have h:=pivot7_42 X Y Z a hX hY hZ w hw
    change w 15=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z20 : w 20=pole7 X Y Z a 20*w 44 := by
    have h:=pivot7_41 X Y Z a hX hY hZ w hw
    change w 20=((1)/(Z) + ((-1)*Y^2)/(Z) + (1*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z46 : w 46=pole7 X Y Z a 46*w 44 := by
    have h:=pivot7_40 X Y Z a hX hY hZ w hw
    change w 46=(((-1))/(Z) + (1*Y^2)/(Z) + ((-1)*X)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z48 : w 48=pole7 X Y Z a 48*w 44 := by
    have h:=pivot7_39 X Y Z a hX hY hZ w hw
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z54 : w 54=pole7 X Y Z a 54*w 44 := by
    have h:=pivot7_38 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v12
  have z18 : w 18=pole7 X Y Z a 18*w 44 := by
    have h:=pivot7_37 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (1)*v48
  have z42 : w 42=pole7 X Y Z a 42*w 44 := by
    have h:=pivot7_36 X Y Z a hX hY hZ w hw
    change w 42=((1*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z5 : w 5=pole7 X Y Z a 5*w 44 := by
    have h:=pivot7_35 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 5=((1)/(X*Z) + (1)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v48
  have z31 : w 31=pole7 X Y Z a 31*w 44 := by
    have h:=pivot7_34 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 31=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z29 : w 29=pole7 X Y Z a 29*w 44 := by
    have h:=pivot7_33 X Y Z a hX hY hZ w hw
    change w 29=((1)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z28 : w 28=pole7 X Y Z a 28*w 44 := by
    have h:=pivot7_32 X Y Z a hX hY hZ w hw
    have v15:=z15
    change w 15=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v15
    change w 28=(((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v15
  have z24 : w 24=pole7 X Y Z a 24*w 44 := by
    have h:=pivot7_31 X Y Z a hX hY hZ w hw
    change w 24=(((-1)*Y^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z8 : w 8=pole7 X Y Z a 8*w 44 := by
    have h:=pivot7_30 X Y Z a hX hY hZ w hw
    have v21:=z21
    change w 21=((1*Y^2)/(X*Z) + (1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v21
    change w 8=(((-1))/(Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z) + ((-1)*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v21
  have z7 : w 7=pole7 X Y Z a 7*w 44 := by
    have h:=pivot7_29 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 7=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z59 : w 59=pole7 X Y Z a 59*w 44 := by
    have h:=pivot7_28 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 59=((1)/(Y^2*Z) + (1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v54
  have z58 : w 58=pole7 X Y Z a 58*w 44 := by
    have h:=pivot7_27 X Y Z a hX hY hZ w hw
    have v45:=z45
    change w 45=(((-1)*Y^2)/(X*Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v45
    change w 58=((1)/(Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z) + (1*X^4)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v45
  have z22 : w 22=pole7 X Y Z a 22*w 44 := by
    have h:=pivot7_26 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 22=((-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*Z)/(Y^2))*v42
  have z39 : w 39=pole7 X Y Z a 39*w 44 := by
    have h:=pivot7_25 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 39=((1)/(Z) + (1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v54
  have z38 : w 38=pole7 X Y Z a 38*w 44 := by
    have h:=pivot7_24 X Y Z a hX hY hZ w hw
    have v51:=z51
    change w 51=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v51
    change w 38=((1*X)/(Z) + (1*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1*X)/(Y^2))*v51
  have z37 : w 37=pole7 X Y Z a 37*w 44 := by
    have h:=pivot7_23 X Y Z a hX hY hZ w hw
    have v42:=z42
    change w 42=((1*Y^2)/(Z))*w 44 at v42
    change w 37=(((-1))/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v42
  have z27 : w 27=pole7 X Y Z a 27*w 44 := by
    have h:=pivot7_22 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 27=(((-1))/(Z) + ((-1)*X)/(Z) + ((-1)*X^2)/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X))*v12
  have z61 : w 61=pole7 X Y Z a 61*w 44 := by
    have h:=pivot7_21 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 61=(((-1))/(X*Z) + ((-1))/(Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v18
  have z35 : w 35=pole7 X Y Z a 35*w 44 := by
    have h:=pivot7_20 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 35=(((-1))/(Y^2*Z) + ((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - ((1)/(X*Y^2))*v12
  have z62 : w 62=pole7 X Y Z a 62*w 44 := by
    have h:=pivot7_19 X Y Z a hX hY hZ w hw
    have v12:=z12
    change w 12=((1*X)/(Z) + (1*X^2)/(Z) + (1*X^3)/(Z))*w 44 at v12
    change w 62=((1*X)/(Y^2*Z) + (1*X^2)/(Y^2*Z) + (1*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v12
  have z4 : w 4=pole7 X Y Z a 4*w 44 := by
    have h:=pivot7_18 X Y Z a hX hY hZ w hw
    have v54:=z54
    change w 54=(((-1)*X)/(Z) + ((-1)*X^2)/(Z) + ((-1)*X^3)/(Z))*w 44 at v54
    change w 4=(((-1)*X)/(Y^2*Z) + ((-1)*X^2)/(Y^2*Z) + ((-1)*X^3)/(Y^2*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1))/(Y^2))*v54
  have z57 : w 57=pole7 X Y Z a 57*w 44 := by
    have h:=pivot7_17 X Y Z a hX hY hZ w hw
    have v22:=z22
    change w 22=((-1))*w 44 at v22
    change w 57=(((-1)*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Y^2)/(X*Z))*v22
  have z55 : w 55=pole7 X Y Z a 55*w 44 := by
    have h:=pivot7_16 X Y Z a hX hY hZ w hw
    have v18:=z18
    change w 18=((1*Y^2)/(Z) + (1*X*Y^2)/(Z))*w 44 at v18
    change w 55=((1)/(X) + 1)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v18
  have z11 : w 11=pole7 X Y Z a 11*w 44 := by
    have h:=pivot7_15 X Y Z a hX hY hZ w hw
    have v48:=z48
    change w 48=(((-1)*Y^2)/(Z) + ((-1)*X*Y^2)/(Z))*w 44 at v48
    change w 11=(((-1))/(X) + (-1))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h - (((-1)*Z)/(X*Y^2))*v48
  have z9 : w 9=pole7 X Y Z a 9*w 44 := by
    have h:=pivot7_14 X Y Z a hX hY hZ w hw
    change w 9=((1*Y^2)/(X*Z))*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z36 : w 36=pole7 X Y Z a 36*w 44 := by
    have h:=pivot7_13 X Y Z a hX hY hZ w hw
    change w 36=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z32 : w 32=pole7 X Y Z a 32*w 44 := by
    have h:=pivot7_12 X Y Z a hX hY hZ w hw
    change w 32=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z34 : w 34=pole7 X Y Z a 34*w 44 := by
    have h:=pivot7_11 X Y Z a hX hY hZ w hw
    change w 34=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z60 : w 60=pole7 X Y Z a 60*w 44 := by
    have h:=pivot7_10 X Y Z a hX hY hZ w hw
    change w 60=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z6 : w 6=pole7 X Y Z a 6*w 44 := by
    have h:=pivot7_9 X Y Z a hX hY hZ w hw
    change w 6=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z2 : w 2=pole7 X Y Z a 2*w 44 := by
    have h:=pivot7_8 X Y Z a hX hY hZ w hw
    change w 2=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z64 : w 64=pole7 X Y Z a 64*w 44 := by
    have h:=pivot7_7 X Y Z a hX hY hZ w hw
    change w 64=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z33 : w 33=pole7 X Y Z a 33*w 44 := by
    have h:=pivot7_6 X Y Z a hX hY hZ w hw
    change w 33=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z30 : w 30=pole7 X Y Z a 30*w 44 := by
    have h:=pivot7_5 X Y Z a hX hY hZ w hw
    change w 30=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z65 : w 65=pole7 X Y Z a 65*w 44 := by
    have h:=pivot7_4 X Y Z a hX hY hZ w hw
    change w 65=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z3 : w 3=pole7 X Y Z a 3*w 44 := by
    have h:=pivot7_3 X Y Z a hX hY hZ w hw
    change w 3=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z1 : w 1=pole7 X Y Z a 1*w 44 := by
    have h:=pivot7_2 X Y Z a hX hY hZ w hw
    change w 1=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z63 : w 63=pole7 X Y Z a 63*w 44 := by
    have h:=pivot7_1 X Y Z a hX hY hZ w hw
    change w 63=(0)*w 44
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h
  have z0 : w 0=pole7 X Y Z a 0*w 44 := by
    have h:=pivot7_0 X Y Z a hX hY hZ w hw
    change w 0=(0)*w 44
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
  · change w 44=1*w 44
    exact (one_mul _).symm
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

#print axioms kernel_case7

end SmallLevelTwentyTwoTriangular
end
end
