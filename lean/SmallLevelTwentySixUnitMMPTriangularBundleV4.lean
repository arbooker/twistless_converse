module
public import SmallLevelTwentySixUnitMMPRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 6000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixUnitMMP
open Complex

theorem pivot_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 0=0 := by
  have h:=hv 9
  change ((1))*v 0=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 765=0 := by
  have h:=hv 0
  change ((1))*v 0 + ((1*X^3*Z))*v 765=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p0)*(1/((1*X^3*Z)))

theorem pivot_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 750=0 := by
  have h:=hv 3
  change ((1))*v 0 + ((1*X*Z))*v 750=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p0)*(1/((1*X*Z)))

theorem pivot_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 1=0 := by
  have h:=hv 10
  change (((1)/(X^3*Y^2*Z*W^2)))*v 0 + ((1))*v 1=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Y^2*Z*W^2)))*p0)*(1/((1)))

theorem pivot_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 2=0 := by
  have h:=hv 11
  change (((1)/(X*Y^2*Z*W^2)))*v 0 + ((1))*v 2=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z*W^2)))*p0)*(1/((1)))

theorem pivot_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 3=0 := by
  have h:=hv 12
  change (((1)/(X^3*Z*W^2)))*v 0 + ((1))*v 3=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Z*W^2)))*p0)*(1/((1)))

theorem pivot_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 5=0 := by
  have h:=hv 14
  change (((1)/(X^3*Y^2*Z)))*v 0 + ((1))*v 5=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Y^2*Z)))*p0)*(1/((1)))

theorem pivot_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 6=0 := by
  have h:=hv 15
  change (((1)/(X*Z*W^2)))*v 0 + ((1))*v 6=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z*W^2)))*p0)*(1/((1)))

theorem pivot_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 10=0 := by
  have h:=hv 18
  change (((1)/(X*Y^2*Z)))*v 0 + ((1))*v 10=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z)))*p0)*(1/((1)))

theorem pivot_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 15=0 := by
  have h:=hv 21
  change (((1)/(X^3*Z)))*v 0 + ((1))*v 15=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Z)))*p0)*(1/((1)))

theorem pivot_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 30=0 := by
  have h:=hv 27
  change (((1)/(X*Z)))*v 0 + ((1))*v 30=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p0)*(1/((1)))

theorem pivot_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 770=0 := by
  have h:=hv 64
  change (((1)/(X*Y^2*Z)))*v 0 + ((1))*v 770=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z)))*p0)*(1/((1)))

theorem pivot_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 774=0 := by
  have h:=hv 67
  change (((1)/(X*Z*W^2)))*v 0 + ((1))*v 774=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z*W^2)))*p0)*(1/((1)))

theorem pivot_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 775=0 := by
  have h:=hv 68
  change (((1)/(X^3*Y^2*Z)))*v 0 + ((1))*v 775=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Y^2*Z)))*p0)*(1/((1)))

theorem pivot_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 777=0 := by
  have h:=hv 70
  change (((1)/(X^3*Z*W^2)))*v 0 + ((1))*v 777=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Z*W^2)))*p0)*(1/((1)))

theorem pivot_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 778=0 := by
  have h:=hv 71
  change (((1)/(X*Y^2*Z*W^2)))*v 0 + ((1))*v 778=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z*W^2)))*p0)*(1/((1)))

#print axioms pivot_15

theorem pivot_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 779=0 := by
  have h:=hv 72
  change (((1)/(X^3*Y^2*Z*W^2)))*v 0 + ((1))*v 779=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^3*Y^2*Z*W^2)))*p0)*(1/((1)))

theorem pivot_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 724=0 := by
  have h:=hv 104
  change ((((-1)*Y^2*W^2)/(X)))*v 724 + ((1))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p2)*(1/((((-1)*Y^2*W^2)/(X))))

theorem pivot_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 360=0 := by
  have h:=hv 109
  change ((1))*v 360 + (((-1)*X*Y^2))*v 770=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*Y^2))*p11)*(1/((1)))

theorem pivot_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 715=0 := by
  have h:=hv 56
  change ((1))*v 360 + (((1*X^3*Y^2)/(Z)))*v 715=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18)*(1/(((1*X^3*Y^2)/(Z))))

theorem pivot_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 752=0 := by
  have h:=hv 76
  change ((1))*v 360 + (((-1)*Y^2*W^2))*v 752=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18)*(1/(((-1)*Y^2*W^2)))

theorem pivot_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 384=0 := by
  have h:=hv 112
  change ((1))*v 384 + (((-1)*X))*v 774=0 at h
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p12)*(1/((1)))

theorem pivot_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 388=0 := by
  have h:=hv 114
  change ((1))*v 388 + ((((-1)*X^3)/(Y^2)))*v 777=0 at h
  have p14:=pivot_14 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X^3)/(Y^2)))*p14)*(1/((1)))

theorem pivot_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 390=0 := by
  have h:=hv 115
  change ((((-1))/(X)))*v 0 + ((1))*v 390=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p0)*(1/((1)))

theorem pivot_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 768=0 := by
  have h:=hv 2
  change ((1))*v 390 + (((1*Z*W^2)/(X)))*v 768=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p23)*(1/(((1*Z*W^2)/(X))))

theorem pivot_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 760=0 := by
  have h:=hv 7
  change ((1))*v 390 + (((1*Y^2*Z)/(X)))*v 760=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p23)*(1/(((1*Y^2*Z)/(X))))

theorem pivot_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 4=0 := by
  have h:=hv 13
  change ((1))*v 4 + (((1*X)/(Y^2*Z*W^2)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Y^2*Z*W^2)))*p23)*(1/((1)))

theorem pivot_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 12=0 := by
  have h:=hv 19
  change ((1))*v 12 + (((1*X)/(Z*W^2)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z*W^2)))*p23)*(1/((1)))

theorem pivot_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 20=0 := by
  have h:=hv 23
  change ((1))*v 20 + (((1*X)/(Y^2*Z)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Y^2*Z)))*p23)*(1/((1)))

theorem pivot_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 60=0 := by
  have h:=hv 34
  change ((1))*v 60 + (((1*X)/(Z)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z)))*p23)*(1/((1)))

theorem pivot_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 720=0 := by
  have h:=hv 57
  change ((1))*v 390 + (((1*Z)/(X)))*v 720=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p23)*(1/(((1*Z)/(X))))

theorem pivot_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 776=0 := by
  have h:=hv 69
  change (((1*X)/(Y^2*Z*W^2)))*v 390 + ((1))*v 776=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Y^2*Z*W^2)))*p23)*(1/((1)))

#print axioms pivot_31

theorem pivot_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 387=0 := by
  have h:=hv 113
  change ((1))*v 387 + ((((-1)*Y^2)/(X^3)))*v 776=0 at h
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X^3)))*p31)*(1/((1)))

theorem pivot_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 392=0 := by
  have h:=hv 116
  change ((((-1)*X)/(Y^2)))*v 6 + ((1))*v 392=0 at h
  have p7:=pivot_7 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2)))*p7)*(1/((1)))

theorem pivot_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 393=0 := by
  have h:=hv 117
  change ((((-1))/(X^3)))*v 12 + ((1))*v 393=0 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3)))*p27)*(1/((1)))

theorem pivot_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 395=0 := by
  have h:=hv 119
  change ((((-1))/(X^3*Y^2)))*v 60 + ((1))*v 395=0 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*Y^2)))*p29)*(1/((1)))

theorem pivot_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 396=0 := by
  have h:=hv 120
  change ((1))*v 396=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 400=0 := by
  have h:=hv 124
  change ((1))*v 400 + ((((-1)*X)/(Y^2)))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2)))*p2)*(1/((1)))

theorem pivot_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 405=0 := by
  have h:=hv 127
  change ((1))*v 405 + ((((-1)*Y^2)/(X^3)))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X^3)))*p25)*(1/((1)))

theorem pivot_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 420=0 := by
  have h:=hv 130
  change ((1))*v 420 + (((-1)*X^3))*v 765=0 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3))*p1)*(1/((1)))

theorem pivot_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 65=0 := by
  have h:=hv 35
  change ((1))*v 65 + (((1*Z)/(X^3*Y^2)))*v 420=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X^3*Y^2)))*p39)*(1/((1)))

theorem pivot_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 28=0 := by
  have h:=hv 99
  change ((1))*v 28 + ((((-1))/(Y^2*W^2)))*v 420=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(Y^2*W^2)))*p39)*(1/((1)))

theorem pivot_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 375=0 := by
  have h:=hv 136
  change ((1))*v 375 + ((((-1)*W^2)/(X^3)))*v 768=0 at h
  have p24:=pivot_24 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X^3)))*p24)*(1/((1)))

theorem pivot_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 380=0 := by
  have h:=hv 137
  change ((1))*v 380 + (((-1)*X))*v 770=0 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p11)*(1/((1)))

theorem pivot_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 425=0 := by
  have h:=hv 140
  change ((1))*v 425 + ((((-1)*W^2)/(X^3)))*v 752=0 at h
  have p20:=pivot_20 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X^3)))*p20)*(1/((1)))

theorem pivot_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 725=0 := by
  have h:=hv 145
  change ((1))*v 60 + (((-1)*X^3*Y^2))*v 725=0 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p29)*(1/(((-1)*X^3*Y^2)))

theorem pivot_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 66=0 := by
  have h:=hv 85
  change ((((-1)*W^2)/(X^2*Y^2)))*v 66 + ((1))*v 725=0 at h
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p45)*(1/((((-1)*W^2)/(X^2*Y^2))))

theorem pivot_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 416=0 := by
  have h:=hv 157
  change ((((-1)*X)/(Y^2*W^2)))*v 390 + ((1))*v 416=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2*W^2)))*p23)*(1/((1)))

#print axioms pivot_47

theorem pivot_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 418=0 := by
  have h:=hv 159
  change ((((-1))/(X*Y^2*W^2)))*v 60 + ((1))*v 418=0 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p29)*(1/((1)))

theorem pivot_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 426=0 := by
  have h:=hv 165
  change ((((-1))/(X*W^2)))*v 420 + ((1))*v 426=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p39)*(1/((1)))

theorem pivot_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 714=0 := by
  have h:=hv 182
  change (((-1)*X*W^2))*v 714 + ((1))*v 720=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p30)*(1/(((-1)*X*W^2)))

theorem pivot_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 55=0 := by
  have h:=hv 84
  change ((((-1)*X^2*Y^2)/(W^2)))*v 55 + ((1))*v 714=0 at h
  have p50:=pivot_50 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p50)*(1/((((-1)*X^2*Y^2)/(W^2))))

theorem pivot_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 354=0 := by
  have h:=hv 194
  change ((1))*v 354 + ((((-1))/(X*W^2)))*v 360=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p18)*(1/((1)))

theorem pivot_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 355=0 := by
  have h:=hv 195
  change ((1))*v 355 + ((((-1))/(X^3*Y^2)))*v 420=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*Y^2)))*p39)*(1/((1)))

theorem pivot_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 362=0 := by
  have h:=hv 201
  change ((1))*v 362 + ((((-1))/(X*Y^2*W^2)))*v 720=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p30)*(1/((1)))

theorem pivot_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 364=0 := by
  have h:=hv 203
  change ((1))*v 364 + ((((-1)*X)/(Y^2*W^2)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2*W^2)))*p23)*(1/((1)))

theorem pivot_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 385=0 := by
  have h:=hv 208
  change ((1))*v 385 + ((((-1)*W^2)/(X^3*Y^2)))*v 768=0 at h
  have p24:=pivot_24 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X^3*Y^2)))*p24)*(1/((1)))

theorem pivot_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 56=0 := by
  have h:=hv 220
  change ((1))*v 30 + ((((-1)*Y^2*W^2)/(X)))*v 56=0 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p10)*(1/((((-1)*Y^2*W^2)/(X))))

theorem pivot_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 389=0 := by
  have h:=hv 233
  change ((1))*v 389 + (((1)/(X^2*Y^2*Z*W^2)))*v 390=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^2*Y^2*Z*W^2)))*p23)*(1/((1)))

theorem pivot_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 391=0 := by
  have h:=hv 234
  change (((1)/(X^2*Y^2*Z*W^2)))*v 390 + ((1))*v 391=0 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X^2*Y^2*Z*W^2)))*p23)*(1/((1)))

theorem pivot_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^3*Y^2*W^2)))*v 240 + ((1))*v 767=0 := by
  have h:=hv 1
  change ((1))*v 240 + (((1*X^3*Y^2*W^2)/(Z)))*v 767=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*Y^2*W^2)/(Z))))

theorem pivot_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X*Y^2*W^2)))*v 120 + ((1))*v 754=0 := by
  have h:=hv 4
  change ((1))*v 120 + (((1*X*Y^2*W^2)/(Z)))*v 754=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Y^2*W^2)/(Z))))

theorem pivot_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*W^2)/(X^3*Y^2*Z)))*v 156 + ((1))*v 755=0 := by
  have h:=hv 5
  change ((1))*v 156 + (((1*X^3*Y^2*Z)/(W^2)))*v 755=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*Y^2*Z)/(W^2))))

theorem pivot_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Z*W^2)))*v 195 + ((1))*v 756=0 := by
  have h:=hv 6
  change ((1))*v 195 + (((1*Z*W^2)/(X^3)))*v 756=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*Z*W^2)/(X^3))))

#print axioms pivot_63

theorem pivot_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*Z*W^2)))*v 520 + ((1))*v 762=0 := by
  have h:=hv 8
  change ((1))*v 520 + (((1*X*Z*W^2)/(Y^2)))*v 762=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Z*W^2)/(Y^2))))

theorem pivot_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 8 + (((1*X^3)/(Y^2*Z*W^2)))*v 195=0 := by
  have h:=hv 16
  change ((1))*v 8 + (((1*X^3)/(Y^2*Z*W^2)))*v 195=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 9 + (((1*Y^2)/(X^3*Z*W^2)))*v 520=0 := by
  have h:=hv 17
  change ((1))*v 9 + (((1*Y^2)/(X^3*Z*W^2)))*v 520=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 13 + (((1*Z)/(X^3*Y^2*W^2)))*v 540=0 := by
  have h:=hv 20
  change ((1))*v 13 + (((1*Z)/(X^3*Y^2*W^2)))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 18 + (((1*Y^2)/(X*Z*W^2)))*v 260=0 := by
  have h:=hv 22
  change ((1))*v 18 + (((1*Y^2)/(X*Z*W^2)))*v 260=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 24 + (((1*X^3)/(Z*W^2)))*v 585=0 := by
  have h:=hv 24
  change ((1))*v 24 + (((1*X^3)/(Z*W^2)))*v 585=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 25 + (((1*W^2)/(X^3*Y^2*Z)))*v 624=0 := by
  have h:=hv 25
  change ((1))*v 25 + (((1*W^2)/(X^3*Y^2*Z)))*v 624=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 26 + (((1*Z)/(X*Y^2*W^2)))*v 660=0 := by
  have h:=hv 26
  change ((1))*v 26 + (((1*Z)/(X*Y^2*W^2)))*v 660=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 36 + (((1*X*Y^2)/(Z*W^2)))*v 130=0 := by
  have h:=hv 28
  change ((1))*v 36 + (((1*X*Y^2)/(Z*W^2)))*v 130=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 39 + (((1*Z)/(X^3*W^2)))*v 180=0 := by
  have h:=hv 29
  change ((1))*v 39 + (((1*Z)/(X^3*W^2)))*v 180=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 40 + (((1*X^3)/(Y^2*Z)))*v 195=0 := by
  have h:=hv 30
  change ((1))*v 40 + (((1*X^3)/(Y^2*Z)))*v 195=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 45 + (((1*Y^2)/(X^3*Z)))*v 260=0 := by
  have h:=hv 31
  change ((1))*v 45 + (((1*Y^2)/(X^3*Z)))*v 260=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 50 + (((1*W^2)/(X*Y^2*Z)))*v 312=0 := by
  have h:=hv 32
  change ((1))*v 50 + (((1*W^2)/(X*Y^2*Z)))*v 312=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 52 + (((1*X*Z)/(Y^2*W^2)))*v 330=0 := by
  have h:=hv 33
  change ((1))*v 52 + (((1*X*Z)/(Y^2*W^2)))*v 330=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 72 + (((1*X^3*Y^2)/(Z*W^2)))*v 455=0 := by
  have h:=hv 36
  change ((1))*v 72 + (((1*X^3*Y^2)/(Z*W^2)))*v 455=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 75 + (((1*W^2)/(X^3*Z)))*v 468=0 := by
  have h:=hv 37
  change ((1))*v 75 + (((1*W^2)/(X^3*Z)))*v 468=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_79

theorem pivot_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 78 + (((1*Z)/(X*W^2)))*v 480=0 := by
  have h:=hv 38
  change ((1))*v 78 + (((1*Z)/(X*W^2)))*v 480=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 90 + (((1*Y^2)/(X*Z)))*v 520=0 := by
  have h:=hv 39
  change ((1))*v 90 + (((1*Y^2)/(X*Z)))*v 520=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2*Z)/(X*W^2)))*v 100 + ((1))*v 546=0 := by
  have h:=hv 40
  change ((1))*v 100 + (((1*X*W^2)/(Y^2*Z)))*v 546=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*W^2)/(Y^2*Z))))

theorem pivot_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2*W^2)/(X^3*Z)))*v 104 + ((1))*v 555=0 := by
  have h:=hv 41
  change ((1))*v 104 + (((1*X^3*Z)/(Y^2*W^2)))*v 555=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*Z)/(Y^2*W^2))))

theorem pivot_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 117 + (((1*Y^2*Z)/(X^3*W^2)))*v 580=0 := by
  have h:=hv 42
  change ((1))*v 117 + (((1*Y^2*Z)/(X^3*W^2)))*v 580=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^3)))*v 120 + ((1))*v 585=0 := by
  have h:=hv 43
  change ((1))*v 120 + (((1*X^3)/(Z)))*v 585=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3)/(Z))))

theorem pivot_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 130 + (((1*Z)/(X*Y^2)))*v 600=0 := by
  have h:=hv 44
  change ((1))*v 130 + (((1*Z)/(X*Y^2)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X*Z)/(W^2)))*v 150 + ((1))*v 624=0 := by
  have h:=hv 45
  change ((1))*v 150 + (((1*W^2)/(X*Z)))*v 624=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*W^2)/(X*Z))))

theorem pivot_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 156 + (((1*X*Z)/(W^2)))*v 630=0 := by
  have h:=hv 46
  change ((1))*v 156 + (((1*X*Z)/(W^2)))*v 630=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X*Y^2)))*v 180 + ((1))*v 650=0 := by
  have h:=hv 47
  change ((1))*v 180 + (((1*X*Y^2)/(Z)))*v 650=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Y^2)/(Z))))

theorem pivot_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Z)))*v 195 + ((1))*v 660=0 := by
  have h:=hv 48
  change ((1))*v 195 + (((1*Z)/(X^3)))*v 660=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*Z)/(X^3))))

theorem pivot_91 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2*Z)/(X^3*W^2)))*v 200 + ((1))*v 663=0 := by
  have h:=hv 49
  change ((1))*v 200 + (((1*X^3*W^2)/(Y^2*Z)))*v 663=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*W^2)/(Y^2*Z))))

theorem pivot_92 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 225 + (((1*Y^2*W^2)/(X^3*Z)))*v 676=0 := by
  have h:=hv 50
  change ((1))*v 225 + (((1*Y^2*W^2)/(X^3*Z)))*v 676=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_93 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 234 + (((1*Y^2*Z)/(X*W^2)))*v 680=0 := by
  have h:=hv 51
  change ((1))*v 234 + (((1*Y^2*Z)/(X*W^2)))*v 680=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*Z)))*v 260 + ((1))*v 690=0 := by
  have h:=hv 52
  change ((1))*v 260 + (((1*X*Z)/(Y^2)))*v 690=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Z)/(Y^2))))

theorem pivot_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X*W^2)))*v 300 + ((1))*v 702=0 := by
  have h:=hv 53
  change ((1))*v 300 + (((1*X*W^2)/(Z)))*v 702=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*W^2)/(Z))))

#print axioms pivot_95

theorem pivot_96 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*W^2)/(X^3*Z)))*v 312 + ((1))*v 705=0 := by
  have h:=hv 54
  change ((1))*v 312 + (((1*X^3*Z)/(W^2)))*v 705=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*Z)/(W^2))))

theorem pivot_97 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 325 + (((1*Z*W^2)/(X^3*Y^2)))*v 708=0 := by
  have h:=hv 55
  change ((1))*v 325 + (((1*Z*W^2)/(X^3*Y^2)))*v 708=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X*Z)/(Y^2*W^2)))*v 450 + ((1))*v 728=0 := by
  have h:=hv 58
  change ((1))*v 450 + (((1*Y^2*W^2)/(X*Z)))*v 728=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*Y^2*W^2)/(X*Z))))

theorem pivot_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*W^2)/(X*Y^2*Z)))*v 468 + ((1))*v 730=0 := by
  have h:=hv 59
  change ((1))*v 468 + (((1*X*Y^2*Z)/(W^2)))*v 730=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Y^2*Z)/(W^2))))

theorem pivot_100 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^3*Z)))*v 520 + ((1))*v 735=0 := by
  have h:=hv 60
  change ((1))*v 520 + (((1*X^3*Z)/(Y^2)))*v 735=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*Z)/(Y^2))))

theorem pivot_101 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2)))*v 120 + ((1))*v 740=0 := by
  have h:=hv 61
  change ((1))*v 585 + (((1*Y^2*Z)/(X^3)))*v 740=0 at h
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p85)*(1/(((1*Y^2*Z)/(X^3))))

theorem pivot_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^3*W^2)))*v 600 + ((1))*v 741=0 := by
  have h:=hv 62
  change ((1))*v 600 + (((1*X^3*W^2)/(Z)))*v 741=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^3*W^2)/(Z))))

theorem pivot_103 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(W^2)))*v 180 + ((1))*v 744=0 := by
  have h:=hv 63
  change ((1))*v 650 + (((1*Z*W^2)/(X*Y^2)))*v 744=0 at h
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p89)*(1/(((1*Z*W^2)/(X*Y^2))))

theorem pivot_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^3*Z*W^2)))*v 260 + ((1))*v 771=0 := by
  have h:=hv 65
  change (((1*Y^2)/(X^3*Z*W^2)))*v 260 + ((1))*v 771=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 120 + ((1))*v 772=0 := by
  have h:=hv 66
  change (((1*X^3)/(Y^2*Z*W^2)))*v 585 + ((1))*v 772=0 at h
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X^3)/(Y^2*Z*W^2)))*p85)*(1/((1)))

theorem pivot_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^3*Z*W^2)))*v 260 + ((1))*v 751=0 := by
  have h:=hv 73
  change ((1))*v 690 + (((-1)*X^2*Y^2*W^2))*v 751=0 at h
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p94)*(1/(((-1)*X^2*Y^2*W^2)))

theorem pivot_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 31 + ((((-1))/(X^2*Y^2*W^2)))*v 630=0 := by
  have h:=hv 74
  change (((-1)*X^2*Y^2*W^2))*v 31 + ((1))*v 630=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^2*Y^2*W^2)))

theorem pivot_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 570 + ((1))*v 766=0 := by
  have h:=hv 75
  change ((1))*v 570 + (((-1)*Y^2*W^2))*v 766=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

theorem pivot_109 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)))*v 510 + ((1))*v 753=0 := by
  have h:=hv 77
  change ((1))*v 510 + (((-1)*X^2*W^2))*v 753=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^2*W^2)))

theorem pivot_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2*W^2)))*v 710 + ((1))*v 759=0 := by
  have h:=hv 78
  change ((1))*v 710 + ((((-1)*X^2*W^2)/(Y^2)))*v 759=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^2*W^2)/(Y^2))))

theorem pivot_111 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 32 + ((((-1))/(Y^2*W^2)))*v 300=0 := by
  have h:=hv 79
  change (((-1)*Y^2*W^2))*v 32 + ((1))*v 300=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

#print axioms pivot_111

theorem pivot_112 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 33 + ((((-1))/(X^2*W^2)))*v 450=0 := by
  have h:=hv 80
  change (((-1)*X^2*W^2))*v 33 + ((1))*v 450=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^2*W^2)))

theorem pivot_113 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 35 + ((((-1))/(X^2*Y^2)))*v 570=0 := by
  have h:=hv 81
  change (((-1)*X^2*Y^2))*v 35 + ((1))*v 570=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^2*Y^2)))

theorem pivot_114 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 42 + ((((-1)*X^2)/(W^2)))*v 675=0 := by
  have h:=hv 82
  change ((((-1)*W^2)/(X^2)))*v 42 + ((1))*v 675=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X^2))))

theorem pivot_115 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 48 + ((((-1)*Y^2)/(W^2)))*v 700=0 := by
  have h:=hv 83
  change ((((-1)*W^2)/(Y^2)))*v 48 + ((1))*v 700=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(Y^2))))

theorem pivot_116 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(W^2)))*v 80 + ((1))*v 732=0 := by
  have h:=hv 86
  change ((((-1)*Y^2)/(W^2)))*v 80 + ((1))*v 732=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^2)/(W^2)))*v 105 + ((1))*v 738=0 := by
  have h:=hv 87
  change ((((-1)*X^2)/(W^2)))*v 105 + ((1))*v 738=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_118 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Y^2)))*v 210 + ((1))*v 745=0 := by
  have h:=hv 88
  change ((((-1))/(X^2*Y^2)))*v 210 + ((1))*v 745=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_119 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)))*v 330 + ((1))*v 747=0 := by
  have h:=hv 89
  change ((((-1))/(X^2*W^2)))*v 330 + ((1))*v 747=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 480 + ((1))*v 748=0 := by
  have h:=hv 90
  change ((((-1))/(Y^2*W^2)))*v 480 + ((1))*v 748=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_121 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Y^2*W^2)))*v 150 + ((1))*v 749=0 := by
  have h:=hv 91
  change ((((-1))/(X^2*Y^2*W^2)))*v 150 + ((1))*v 749=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_122 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 16 + ((((-1))/(Y^2*W^2)))*v 540=0 := by
  have h:=hv 92
  change (((-1)*Y^2*W^2))*v 16 + ((1))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

theorem pivot_123 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 240 + ((1))*v 764=0 := by
  have h:=hv 93
  change ((((-1))/(Y^2*W^2)))*v 240 + ((1))*v 764=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_124 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 11 + ((((-1))/(X^2*W^2)))*v 670=0 := by
  have h:=hv 94
  change ((1))*v 11 + ((((-1))/(X^2*W^2)))*v 670=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_125 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 14 + ((((-1))/(Y^2*W^2)))*v 210=0 := by
  have h:=hv 95
  change ((1))*v 14 + ((((-1)*X^2)/(W^2)))*v 745=0 at h
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X^2)/(W^2)))*p118)*(1/((1)))

theorem pivot_126 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*W^2)))*v 110 + ((1))*v 769=0 := by
  have h:=hv 96
  change ((1))*v 110 + (((-1)*X^2*W^2))*v 769=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^2*W^2)))

theorem pivot_127 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 21 + ((((-1)*Y^2)/(X^2*W^2)))*v 70=0 := by
  have h:=hv 97
  change ((1))*v 21 + ((((-1)*Y^2)/(X^2*W^2)))*v 70=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_127

theorem pivot_128 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 27 + ((((-1))/(X^2*W^2)))*v 270=0 := by
  have h:=hv 98
  change ((1))*v 27 + ((((-1))/(X^2*W^2)))*v 270=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_129 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 29 + (((1)/(X^3*Z*W^2)))*v 520=0 := by
  have h:=hv 100
  change ((1))*v 29 + ((((-1))/(X^2*Y^2*W^2)))*v 90=0 at h
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^2*Y^2*W^2)))*p81)*(1/((1)))

theorem pivot_130 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*Y^2*W^2)))*v 180 + ((1))*v 721=0 := by
  have h:=hv 101
  change ((1))*v 180 + (((-1)*X^3*Y^2*W^2))*v 721=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*Y^2*W^2)))

theorem pivot_131 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)))*v 300 + ((1))*v 722=0 := by
  have h:=hv 102
  change ((1))*v 300 + (((-1)*X*Y^2*W^2))*v 722=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

theorem pivot_132 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 600 + ((1))*v 723=0 := by
  have h:=hv 103
  change ((1))*v 600 + (((-1)*X^3*W^2))*v 723=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

theorem pivot_133 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 62 + ((((-1))/(X*Y^2*W^2)))*v 240=0 := by
  have h:=hv 105
  change (((-1)*X*Y^2*W^2))*v 62 + ((1))*v 240=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

theorem pivot_134 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 63 + ((((-1))/(X^3*W^2)))*v 540=0 := by
  have h:=hv 106
  change (((-1)*X^3*W^2))*v 63 + ((1))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

theorem pivot_135 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 64 + (((1)/(Z*W^2)))*v 260=0 := by
  have h:=hv 107
  change ((((-1)*Y^2*W^2)/(X)))*v 64 + ((1))*v 690=0 at h
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p94)*(1/((((-1)*Y^2*W^2)/(X))))

theorem pivot_136 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X*Y^2)/(W^2)))*v 110 + ((1))*v 324=0 := by
  have h:=hv 108
  change ((1))*v 324 + (((-1)*X^3*Y^2))*v 769=0 at h
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3*Y^2))*p126)*(1/((1)))

theorem pivot_137 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(Z*W^2)))*v 260 + ((1))*v 372=0 := by
  have h:=hv 110
  change ((1))*v 372 + (((-1)*X^3))*v 771=0 at h
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3))*p104)*(1/((1)))

theorem pivot_138 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)))*v 120 + ((1))*v 378=0 := by
  have h:=hv 111
  change ((1))*v 378 + ((((-1)*Y^2)/(X)))*v 772=0 at h
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X)))*p105)*(1/((1)))

theorem pivot_139 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)))*v 120 + ((1))*v 394=0 := by
  have h:=hv 118
  change ((((-1))/(X*Y^2)))*v 24 + ((1))*v 394=0 at h
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2)))*p69 - (((1*X^2)/(Y^2*Z*W^2)))*p85)*(1/((1)))

theorem pivot_140 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 397 + ((((-1))/(X^3*Y^2)))*v 696=0 := by
  have h:=hv 121
  change ((1))*v 397 + ((((-1))/(X^3*Y^2)))*v 696=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_141 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)))*v 80 + ((1))*v 398=0 := by
  have h:=hv 122
  change ((1))*v 398 + ((((-1))/(X*Y^2)))*v 732=0 at h
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2)))*p116)*(1/((1)))

theorem pivot_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 180 + ((1))*v 399=0 := by
  have h:=hv 123
  change ((1))*v 399 + ((((-1))/(X^3)))*v 744=0 at h
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3)))*p103)*(1/((1)))

theorem pivot_143 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2)/(Z*W^2)))*v 195 + ((1))*v 402=0 := by
  have h:=hv 125
  change ((1))*v 402 + ((((-1))/(X)))*v 756=0 at h
  have p63:=pivot_63 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p63)*(1/((1)))

#print axioms pivot_143

theorem pivot_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 404 + ((((-1)*X)/(W^2)))*v 710=0 := by
  have h:=hv 126
  change ((1))*v 404 + ((((-1)*X^3)/(Y^2)))*v 759=0 at h
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X^3)/(Y^2)))*p110)*(1/((1)))

theorem pivot_145 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 408 + (((1*Y^2)/(Z*W^2)))*v 520=0 := by
  have h:=hv 128
  change ((1))*v 408 + (((-1)*X))*v 762=0 at h
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p64)*(1/((1)))

theorem pivot_146 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)))*v 240 + ((1))*v 414=0 := by
  have h:=hv 129
  change ((1))*v 414 + ((((-1)*Y^2)/(X)))*v 764=0 at h
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X)))*p123)*(1/((1)))

theorem pivot_147 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 432 + ((((-1)*X)/(W^2)))*v 570=0 := by
  have h:=hv 131
  change ((1))*v 432 + (((-1)*X*Y^2))*v 766=0 at h
  have p108:=pivot_108 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*Y^2))*p108)*(1/((1)))

theorem pivot_148 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(W^2)))*v 240 + ((1))*v 468=0 := by
  have h:=hv 132
  change ((1))*v 468 + (((-1)*X^3*Y^2))*v 767=0 at h
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3*Y^2))*p60)*(1/((1)))

theorem pivot_149 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 200 + ((1))*v 761=0 := by
  have h:=hv 133
  change ((1))*v 200 + (((-1)*X^3*W^2))*v 761=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

theorem pivot_150 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 300 + (((1*Y^2)/(Z)))*v 520=0 := by
  have h:=hv 134
  change ((1))*v 300 + (((-1)*X*W^2))*v 762=0 at h
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*W^2))*p64)*(1/((1)))

theorem pivot_151 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)))*v 240 + ((1))*v 350=0 := by
  have h:=hv 135
  change ((1))*v 350 + ((((-1)*W^2)/(X)))*v 764=0 at h
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X)))*p123)*(1/((1)))

theorem pivot_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 401 + ((((-1))/(X^3*W^2)))*v 560=0 := by
  have h:=hv 138
  change ((1))*v 401 + ((((-1))/(X^3*W^2)))*v 560=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_153 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)))*v 120 + ((1))*v 410=0 := by
  have h:=hv 139
  change ((1))*v 410 + ((((-1))/(X)))*v 740=0 at h
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p101)*(1/((1)))

theorem pivot_154 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 440 + ((((-1)*X)/(Y^2)))*v 630=0 := by
  have h:=hv 141
  change ((1))*v 440 + (((-1)*X^3))*v 755=0 at h
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3))*p62 - (((1*W^2)/(Y^2*Z)))*p88)*(1/((1)))

theorem pivot_155 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2)/(Z)))*v 195 + ((1))*v 450=0 := by
  have h:=hv 142
  change ((1))*v 450 + ((((-1)*W^2)/(X)))*v 756=0 at h
  have p63:=pivot_63 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X)))*p63)*(1/((1)))

theorem pivot_156 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)))*v 500 + ((1))*v 758=0 := by
  have h:=hv 143
  change ((1))*v 500 + (((-1)*X*W^2))*v 758=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*W^2)))

theorem pivot_157 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2)))*v 600 + ((1))*v 710=0 := by
  have h:=hv 144
  change ((1))*v 600 + (((-1)*X^3*W^2))*v 759=0 at h
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3*W^2))*p110)*(1/(((-1)*X*Y^2)))

theorem pivot_158 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*W^2)))*v 120 + ((1))*v 726=0 := by
  have h:=hv 146
  change ((1))*v 120 + (((-1)*X*W^2))*v 726=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*W^2)))

theorem pivot_159 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)))*v 220 + ((1))*v 729=0 := by
  have h:=hv 147
  change ((1))*v 220 + ((((-1)*X^3*W^2)/(Y^2)))*v 729=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^3*W^2)/(Y^2))))

#print axioms pivot_159

theorem pivot_160 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 80 + ((((-1)*X)/(Y^2)))*v 270=0 := by
  have h:=hv 148
  change ((1))*v 270 + ((((-1)*W^2)/(X)))*v 732=0 at h
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X)))*p116)*(1/((((-1)*Y^2)/(X))))

theorem pivot_161 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 105 + ((((-1)*Y^2)/(X^3)))*v 320=0 := by
  have h:=hv 149
  change ((1))*v 320 + ((((-1)*X*W^2)/(Y^2)))*v 738=0 at h
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X*W^2)/(Y^2)))*p117)*(1/((((-1)*X^3)/(Y^2))))

theorem pivot_162 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)))*v 120 + ((1))*v 330=0 := by
  have h:=hv 150
  change ((1))*v 330 + ((((-1)*Y^2)/(X)))*v 740=0 at h
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X)))*p101)*(1/((1)))

theorem pivot_163 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3)))*v 180 + ((1))*v 345=0 := by
  have h:=hv 151
  change ((1))*v 345 + ((((-1)*W^2)/(X^3)))*v 744=0 at h
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X^3)))*p103)*(1/((1)))

theorem pivot_164 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(W^2)))*v 210 + ((1))*v 348=0 := by
  have h:=hv 152
  change ((1))*v 348 + ((((-1)*X^3*Y^2)/(W^2)))*v 745=0 at h
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X^3*Y^2)/(W^2)))*p118)*(1/((1)))

theorem pivot_165 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2)/(Y^2*Z)))*v 195 + ((1))*v 370=0 := by
  have h:=hv 153
  change ((1))*v 370 + ((((-1)*W^2)/(X*Y^2)))*v 756=0 at h
  have p63:=pivot_63 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X*Y^2)))*p63)*(1/((1)))

theorem pivot_166 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)))*v 140 + ((1))*v 411=0 := by
  have h:=hv 154
  change ((((-1)*Y^2)/(X^3*W^2)))*v 140 + ((1))*v 411=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_167 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^3)/(Y^2*W^2)))*v 165 + ((1))*v 412=0 := by
  have h:=hv 155
  change ((((-1)*X^3)/(Y^2*W^2)))*v 165 + ((1))*v 412=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_168 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 415 + (((1)/(X^3*Z)))*v 520=0 := by
  have h:=hv 156
  change ((((-1))/(X^3*Y^2)))*v 300 + ((1))*v 415=0 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*Y^2)))*p150)*(1/((1)))

theorem pivot_169 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 417 + ((((-1))/(X^3*W^2)))*v 540=0 := by
  have h:=hv 158
  change ((1))*v 417 + ((((-1))/(X^3*W^2)))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*Y^2*W^2)))*v 180 + ((1))*v 419=0 := by
  have h:=hv 160
  change ((((-1))/(X^3*Y^2*W^2)))*v 180 + ((1))*v 419=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_171 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 421 + ((((-1))/(X^3*Y^2*W^2)))*v 480=0 := by
  have h:=hv 161
  change ((1))*v 421 + ((((-1))/(X^3*Y^2*W^2)))*v 480=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_172 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 422 + ((((-1))/(X*Y^2*W^2)))*v 600=0 := by
  have h:=hv 162
  change ((1))*v 422 + ((((-1))/(X*Y^2*W^2)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_173 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 120 + ((1))*v 423=0 := by
  have h:=hv 163
  change ((((-1))/(X^3*W^2)))*v 120 + ((1))*v 423=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(Y^2*W^2)))*v 270 + ((1))*v 424=0 := by
  have h:=hv 164
  change ((((-1)*X)/(Y^2*W^2)))*v 270 + ((1))*v 424=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_175 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 428 + ((((-1)*X^3)/(Y^2*W^2)))*v 495=0 := by
  have h:=hv 166
  change ((1))*v 428 + ((((-1)*X^3)/(Y^2*W^2)))*v 495=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_175

theorem pivot_176 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 429 + ((((-1)*Y^2)/(X^3*W^2)))*v 520=0 := by
  have h:=hv 167
  change ((1))*v 429 + ((((-1)*Y^2)/(X^3*W^2)))*v 520=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_177 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 430 + ((((-1))/(X*Y^2)))*v 540=0 := by
  have h:=hv 168
  change ((1))*v 430 + ((((-1))/(X*Y^2)))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_178 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 435 + ((((-1))/(X^3)))*v 600=0 := by
  have h:=hv 169
  change ((1))*v 435 + ((((-1))/(X^3)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_179 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 438 + ((((-1)*Y^2)/(X*W^2)))*v 620=0 := by
  have h:=hv 170
  change ((1))*v 438 + ((((-1)*Y^2)/(X*W^2)))*v 620=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_180 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 445 + ((((-1)*W^2)/(X^3*Y^2)))*v 648=0 := by
  have h:=hv 171
  change ((1))*v 445 + ((((-1)*W^2)/(X^3*Y^2)))*v 648=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_181 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 456 + ((((-1)*X*Y^2)/(W^2)))*v 670=0 := by
  have h:=hv 172
  change ((1))*v 456 + ((((-1)*X*Y^2)/(W^2)))*v 670=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_182 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3)))*v 460 + ((1))*v 675=0 := by
  have h:=hv 173
  change ((1))*v 460 + ((((-1)*X^3)/(Y^2)))*v 675=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^3)/(Y^2))))

theorem pivot_183 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 465 + ((((-1)*Y^2)/(X^3)))*v 680=0 := by
  have h:=hv 174
  change ((1))*v 465 + ((((-1)*Y^2)/(X^3)))*v 680=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_184 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X*Y^2)/(W^2)))*v 470 + ((1))*v 684=0 := by
  have h:=hv 175
  change ((1))*v 470 + ((((-1)*W^2)/(X*Y^2)))*v 684=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X*Y^2))))

theorem pivot_185 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(Z)))*v 260 + ((1))*v 480=0 := by
  have h:=hv 176
  change ((1))*v 480 + (((-1)*X))*v 690=0 at h
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p94)*(1/((1)))

theorem pivot_186 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^3)/(W^2)))*v 495 + ((1))*v 696=0 := by
  have h:=hv 177
  change ((1))*v 495 + ((((-1)*W^2)/(X^3)))*v 696=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X^3))))

theorem pivot_187 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(Y^2)))*v 510 + ((1))*v 700=0 := by
  have h:=hv 178
  change ((1))*v 510 + ((((-1)*Y^2)/(X)))*v 700=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2)/(X))))

theorem pivot_188 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 312 + (((1*Z)/(W^2)))*v 540=0 := by
  have h:=hv 179
  change ((1))*v 540 + (((-1)*X^3))*v 705=0 at h
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X^3))*p96)*(1/(((1*W^2)/(Z))))

theorem pivot_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(W^2)))*v 570 + ((1))*v 708=0 := by
  have h:=hv 180
  change ((1))*v 570 + ((((-1)*W^2)/(X)))*v 708=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X))))

theorem pivot_190 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)))*v 620 + ((1))*v 711=0 := by
  have h:=hv 181
  change ((1))*v 620 + ((((-1)*X^3*W^2)/(Y^2)))*v 711=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^3*W^2)/(Y^2))))

theorem pivot_191 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 69 + ((((-1)*Y^2)/(X^3*W^2)))*v 160=0 := by
  have h:=hv 183
  change ((((-1)*X^3*W^2)/(Y^2)))*v 69 + ((1))*v 160=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^3*W^2)/(Y^2))))

#print axioms pivot_191

theorem pivot_192 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 70 + ((((-1))/(X*Y^2)))*v 180=0 := by
  have h:=hv 184
  change (((-1)*X*Y^2))*v 70 + ((1))*v 180=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2)))

theorem pivot_193 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^2*Y^2)))*v 210 + ((1))*v 455=0 := by
  have h:=hv 185
  change ((((-1)*W^2)/(X)))*v 72 + ((1))*v 210=0 at h
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X)))*p78)*(1/(((1*X^2*Y^2)/(Z))))

theorem pivot_194 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 84 + ((((-1)*X^3)/(W^2)))*v 285=0 := by
  have h:=hv 186
  change ((((-1)*W^2)/(X^3)))*v 84 + ((1))*v 285=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X^3))))

theorem pivot_195 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 96 + ((((-1)*X*Y^2)/(W^2)))*v 310=0 := by
  have h:=hv 187
  change ((((-1)*W^2)/(X*Y^2)))*v 96 + ((1))*v 310=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X*Y^2))))

theorem pivot_196 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3)))*v 100 + ((1))*v 315=0 := by
  have h:=hv 188
  change ((((-1)*Y^2)/(X^3)))*v 100 + ((1))*v 315=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_197 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*W^2)/(X^3*Y^2)))*v 132 + ((1))*v 335=0 := by
  have h:=hv 189
  change ((((-1)*W^2)/(X^3*Y^2)))*v 132 + ((1))*v 335=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_198 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X)/(Y^2)))*v 150 + ((1))*v 340=0 := by
  have h:=hv 190
  change ((((-1)*X)/(Y^2)))*v 150 + ((1))*v 340=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_199 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*W^2)))*v 160 + ((1))*v 342=0 := by
  have h:=hv 191
  change ((((-1)*Y^2)/(X*W^2)))*v 160 + ((1))*v 342=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_200 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*W^2)))*v 260 + ((1))*v 351=0 := by
  have h:=hv 192
  change ((((-1)*Y^2)/(X^3*W^2)))*v 260 + ((1))*v 351=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_201 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^3)/(Y^2*W^2)))*v 285 + ((1))*v 352=0 := by
  have h:=hv 193
  change ((((-1)*X^3)/(Y^2*W^2)))*v 285 + ((1))*v 352=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 356 + ((((-1)*X)/(Y^2*W^2)))*v 510=0 := by
  have h:=hv 196
  change ((1))*v 356 + ((((-1)*X)/(Y^2*W^2)))*v 510=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_203 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Z*W^2)))*v 195 + ((1))*v 357=0 := by
  have h:=hv 197
  change ((1))*v 357 + ((((-1))/(X^3*W^2)))*v 660=0 at h
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*W^2)))*p90)*(1/((1)))

theorem pivot_204 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)))*v 180 + ((1))*v 358=0 := by
  have h:=hv 198
  change ((((-1))/(X*Y^2*W^2)))*v 180 + ((1))*v 358=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_205 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 359 + (((1)/(X^3*Z*W^2)))*v 520=0 := by
  have h:=hv 199
  change ((((-1))/(X^3*Y^2*W^2)))*v 300 + ((1))*v 359=0 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*Y^2*W^2)))*p150)*(1/((1)))

theorem pivot_206 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 361 + ((((-1))/(X^3*Y^2*W^2)))*v 600=0 := by
  have h:=hv 200
  change ((1))*v 361 + ((((-1))/(X^3*Y^2*W^2)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_207 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 240 + ((1))*v 363=0 := by
  have h:=hv 202
  change ((((-1))/(X^3*W^2)))*v 240 + ((1))*v 363=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_207

theorem pivot_208 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X^3*Z)))*v 260 + ((1))*v 365=0 := by
  have h:=hv 204
  change ((1))*v 365 + ((((-1))/(X^3*Y^2)))*v 480=0 at h
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X^3*Y^2)))*p185)*(1/((1)))

theorem pivot_209 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 366 + ((((-1))/(X*W^2)))*v 540=0 := by
  have h:=hv 205
  change ((1))*v 366 + ((((-1))/(X*W^2)))*v 540=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_210 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 368 + ((((-1)*X^3)/(Y^2*W^2)))*v 615=0 := by
  have h:=hv 206
  change ((1))*v 368 + ((((-1)*X^3)/(Y^2*W^2)))*v 615=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_211 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 369 + ((((-1)*Y^2)/(X^3*W^2)))*v 640=0 := by
  have h:=hv 207
  change ((1))*v 369 + ((((-1)*Y^2)/(X^3*W^2)))*v 640=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_212 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 51 + ((((-1)*Y^2)/(X^3*W^2)))*v 560=0 := by
  have h:=hv 209
  change ((((-1)*X^3*W^2)/(Y^2)))*v 51 + ((1))*v 560=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X^3*W^2)/(Y^2))))

theorem pivot_213 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 54 + (((1*X^2)/(Z*W^2)))*v 195=0 := by
  have h:=hv 210
  change (((-1)*X*W^2))*v 54 + ((1))*v 660=0 at h
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p90)*(1/(((-1)*X*W^2)))

theorem pivot_214 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 22 + ((((-1))/(X*W^2)))*v 280=0 := by
  have h:=hv 211
  change (((-1)*X*W^2))*v 22 + ((1))*v 280=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*W^2)))

theorem pivot_215 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 180 + ((1))*v 376=0 := by
  have h:=hv 212
  change ((((-1)*X)/(W^2)))*v 70 + ((1))*v 376=0 at h
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(W^2)))*p192)*(1/((1)))

theorem pivot_216 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 220 + ((1))*v 379=0 := by
  have h:=hv 213
  change ((((-1))/(X^3*W^2)))*v 220 + ((1))*v 379=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_217 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 381 + ((((-1))/(X^3*W^2)))*v 600=0 := by
  have h:=hv 214
  change ((1))*v 381 + ((((-1))/(X^3*W^2)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_218 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 382 + ((((-1))/(Y^2*W^2)))*v 510=0 := by
  have h:=hv 215
  change ((1))*v 382 + ((((-1))/(X*W^2)))*v 700=0 at h
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p187)*(1/((1)))

theorem pivot_219 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 19 + ((((-1))/(X^3*W^2)))*v 580=0 := by
  have h:=hv 216
  change (((-1)*X^3*W^2))*v 19 + ((1))*v 580=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

theorem pivot_220 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Z*W^2)))*v 520 + ((1))*v 716=0 := by
  have h:=hv 217
  change ((1))*v 90 + ((((-1)*Y^2*W^2)/(X)))*v 716=0 at h
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p81)*(1/((((-1)*Y^2*W^2)/(X))))

theorem pivot_221 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^3*W^2)))*v 240 + ((1))*v 717=0 := by
  have h:=hv 218
  change ((1))*v 240 + (((-1)*X^3*W^2))*v 717=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

theorem pivot_222 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Y^2*W^2)))*v 540 + ((1))*v 718=0 := by
  have h:=hv 219
  change ((1))*v 540 + (((-1)*X*Y^2*W^2))*v 718=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

theorem pivot_223 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 57 + ((((-1))/(X^3*W^2)))*v 180=0 := by
  have h:=hv 221
  change (((-1)*X^3*W^2))*v 57 + ((1))*v 180=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X^3*W^2)))

#print axioms pivot_223

theorem pivot_224 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 58 + (((1)/(X*Z*W^2)))*v 260=0 := by
  have h:=hv 222
  change (((-1)*X*Y^2*W^2))*v 58 + ((1))*v 480=0 at h
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p185)*(1/(((-1)*X*Y^2*W^2)))

theorem pivot_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(Y^2*Z*W^2)))*v 195 + ((1))*v 719=0 := by
  have h:=hv 223
  change ((1))*v 660 + (((-1)*X^3*Y^2*W^2))*v 719=0 at h
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p90)*(1/(((-1)*X^3*Y^2*W^2)))

theorem pivot_226 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 59 + ((((-1))/(X^3*Y^2*W^2)))*v 600=0 := by
  have h:=hv 224
  change ((1))*v 59 + ((((-1))/(X^3*Y^2*W^2)))*v 600=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_227 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 61 + ((((-1))/(X^3*Y^2*W^2)))*v 120=0 := by
  have h:=hv 225
  change ((1))*v 61 + ((((-1))/(X^3*Y^2*W^2)))*v 120=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_228 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^2*Y^2*W^2)))*v 270 + ((1))*v 403=0 := by
  have h:=hv 226
  change ((1))*v 270 + (((1*X^2*Y^2*W^2)/(Z)))*v 403=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^2*Y^2*W^2)/(Z))))

theorem pivot_229 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 165 + (((1*Y^2*W^2)/(X^2*Z)))*v 442=0 := by
  have h:=hv 227
  change ((1))*v 165 + (((1*Y^2*W^2)/(X^2*Z)))*v 442=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_230 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 273 + (((1*Y^2*Z)/(X^2*W^2)))*v 490=0 := by
  have h:=hv 228
  change ((1))*v 273 + (((1*Y^2*Z)/(X^2*W^2)))*v 490=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_231 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2*Z)/(X^2*W^2)))*v 290 + ((1))*v 507=0 := by
  have h:=hv 229
  change ((1))*v 290 + (((1*X^2*W^2)/(Y^2*Z)))*v 507=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^2*W^2)/(Y^2*Z))))

theorem pivot_232 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2*W^2)/(X^2*Z)))*v 338 + ((1))*v 615=0 := by
  have h:=hv 230
  change ((1))*v 338 + (((1*X^2*Z)/(Y^2*W^2)))*v 615=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X^2*Z)/(Y^2*W^2))))

theorem pivot_233 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 377 + (((1*Z)/(X^2*Y^2*W^2)))*v 510=0 := by
  have h:=hv 231
  change ((1))*v 377 + (((1*Z)/(X^2*Y^2*W^2)))*v 510=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_234 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2)/(Y^2*Z*W^2)))*v 195 + ((1))*v 386=0 := by
  have h:=hv 232
  change (((1*X^2)/(Y^2*Z*W^2)))*v 195 + ((1))*v 386=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_235 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Y^2*W^2)))*v 150 + ((1))*v 406=0 := by
  have h:=hv 235
  change ((((-1))/(Y^2*W^2)))*v 150 + ((1))*v 406=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_236 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 374 + ((((-1))/(Y^2*W^2)))*v 630=0 := by
  have h:=hv 236
  change (((-1)*Y^2*W^2))*v 374 + ((1))*v 630=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

theorem pivot_237 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 260 + ((1))*v 520=0 := by
  have h:=hv 237
  change ((1))*v 260 + ((1))*v 520=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_238 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 120 + ((((-1)*X^3)/(Z)))*v 195=0 := by
  have h:=hv 256
  change ((1))*v 195 + ((1))*v 585=0 at h
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p85)*(1/((((-1)*Z)/(X^3))))

theorem pivot_239 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 200 + ((1))*v 590=0 := by
  have h:=hv 257
  change (((1)/(Y^2*Z)))*v 0 + ((1))*v 200 + (((1)/(Y^2*Z)))*v 390 + ((1))*v 590=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2*Z)))*p0 - (((1)/(Y^2*Z)))*p23)*(1/((1)))

#print axioms pivot_239

theorem pivot_240 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 190 + ((1))*v 580=0 := by
  have h:=hv 258
  change (((1)/(Y^2*Z)))*v 0 + ((1))*v 190 + (((1)/(Y^2*Z)))*v 390 + ((1))*v 580=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2*Z)))*p0 - (((1)/(Y^2*Z)))*p23)*(1/((1)))

theorem pivot_241 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 208 + ((1))*v 598=0 := by
  have h:=hv 259
  change ((1))*v 208 + (((1*Z)/(Y^2*W^2)))*v 360 + ((1))*v 598 + (((1*Z)/(Y^2*W^2)))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(Y^2*W^2)))*p2 - (((1*Z)/(Y^2*W^2)))*p18)*(1/((1)))

theorem pivot_242 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 182 + ((1))*v 572=0 := by
  have h:=hv 260
  change (((1*Z)/(Y^2*W^2)))*v 30 + ((1))*v 182 + (((1*Z)/(Y^2*W^2)))*v 420 + ((1))*v 572=0 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(Y^2*W^2)))*p10 - (((1*Z)/(Y^2*W^2)))*p39)*(1/((1)))

theorem pivot_243 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 210 + ((1))*v 600=0 := by
  have h:=hv 261
  change (((1)/(Z)))*v 0 + ((1))*v 210 + (((1)/(Z)))*v 390 + ((1))*v 600=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p23)*(1/((1)))

theorem pivot_244 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 180 + ((1))*v 570=0 := by
  have h:=hv 262
  change (((1)/(Z)))*v 0 + ((1))*v 180 + (((1)/(Z)))*v 390 + ((1))*v 570=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p23)*(1/((1)))

theorem pivot_245 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 180 + ((1))*v 600=0 := by
  have h:=hv 268
  change ((1))*v 130 + ((1))*v 650=0 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p86 - ((1))*p89)*(1/((((-1)*Z)/(X*Y^2))))

theorem pivot_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 100 + ((1))*v 680=0 := by
  have h:=hv 281
  change ((1))*v 78 + ((1))*v 234 + ((1))*v 546 + ((1))*v 702=0 at h
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p80 - ((1))*p82 - ((1))*p93 - ((1))*p95 - ((((-1)*Z)/(X*W^2)))*p150 - ((((-1)*Z)/(X*W^2)))*p185 - (((1*Y^2)/(X*W^2)))*p237)*(1/((((-1)*Y^2*Z)/(X*W^2))))

theorem pivot_247 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 240 + ((1))*v 540=0 := by
  have h:=hv 288
  change ((1))*v 60 + ((1))*v 120 + ((1))*v 180 + ((1))*v 240 + ((1))*v 300 + ((1))*v 360 + ((1))*v 420 + ((1))*v 480 + ((1))*v 540 + ((1))*v 600 + ((1))*v 660 + ((1))*v 720=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18 - ((1))*p29 - ((1))*p30 - ((1))*p39 - ((1))*p90 - ((1))*p150 - ((1))*p185 - ((((-1)*Y^2)/(Z)))*p237 - ((1))*p238 - ((1))*p245)*(1/((1)))

theorem pivot_248 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 150 + ((1))*v 630=0 := by
  have h:=hv 267
  change ((1))*v 156 + ((1))*v 312 + ((1))*v 468 + ((1))*v 624=0 at h
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p87 - ((1))*p88 - ((1))*p148 - ((1))*p188 - ((((-1)*Z)/(W^2)))*p247)*(1/((((-1)*X*Z)/(W^2))))

theorem pivot_249 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 270 + ((1))*v 510=0 := by
  have h:=hv 293
  change ((((-1))/(X)))*v 0 + ((((-1))/(X)))*v 60 + ((1))*v 90 + ((((-1))/(X)))*v 120 + ((1))*v 150 + ((((-1))/(X)))*v 180 + ((1))*v 210 + ((((-1))/(X)))*v 240 + ((1))*v 270 + ((((-1))/(X)))*v 300 + ((1))*v 330 + ((((-1))/(X)))*v 360 + ((1))*v 390 + ((((-1))/(X)))*v 420 + ((1))*v 450 + ((((-1))/(X)))*v 480 + ((1))*v 510 + ((((-1))/(X)))*v 540 + ((1))*v 570 + ((((-1))/(X)))*v 600 + ((1))*v 630 + ((((-1))/(X)))*v 660 + ((1))*v 690 + ((1))*v 750=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p0 - ((1))*p2 - ((((-1))/(X)))*p18 - ((1))*p23 - ((((-1))/(X)))*p29 - ((((-1))/(X)))*p39 - ((1))*p81 - ((((-1))/(X)))*p90 - ((1))*p94 - ((((-1))/(X)))*p150 - ((1))*p155 - ((1))*p162 - ((((-1))/(X)))*p185 - ((1))*p243 - ((1))*p244 - ((((-1))/(X)) + ((-1)))*p245 - ((((-1))/(X)))*p247 - ((1))*p248)*(1/((1)))

theorem pivot_250 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2*Y^2)/(W^2)))*v 110 + ((1))*v 648=0 := by
  have h:=hv 326
  change ((1))*v 55 + (((1)/(X)))*v 110 + ((1))*v 445=0 at h
  have p51:=pivot_51 X Y Z W a b hX hY hZ hW v hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p51 - ((1))*p180)*(1/(((1*W^2)/(X^3*Y^2))))

theorem pivot_251 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 132 + (((1*X^2*Y^2)/(W^2)))*v 670=0 := by
  have h:=hv 327
  change ((1))*v 66 + (((1)/(X)))*v 132 + ((1))*v 456=0 at h
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p181:=pivot_181 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p46 - ((1))*p181)*(1/(((1)/(X))))

theorem pivot_252 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + ((1))*v 600=0 := by
  have h:=hv 321
  change ((1))*v 9 + (((1)/(X)))*v 18 + ((1))*v 399=0 at h
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v hv
  have p68:=pivot_68 X Y Z W a b hX hY hZ hW v hv
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p66 - (((1)/(X)))*p68 - ((1))*p142 - ((((-1)*Y^2)/(X^2*Z*W^2)))*p237 - (((1)/(X^3*W^2)))*p245)*(1/((((-1))/(X^3*W^2))))

theorem pivot_253 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((-1)))*v 510 + ((((-1))/(X*Z)))*v 520 + ((1))*v 530=0 := by
  have h:=hv 238
  change (((1)/(X*Z)))*v 0 + (((1)/(X*Z)))*v 260 + ((1))*v 270 + ((1))*v 530=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p0 - (((1)/(X*Z)))*p237 - ((1))*p249)*(1/((1)))

theorem pivot_254 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 250 + ((1))*v 510 + (((1)/(X*Z)))*v 520=0 := by
  have h:=hv 239
  change (((1)/(X*Z)))*v 0 + ((1))*v 250 + ((1))*v 510 + (((1)/(X*Z)))*v 520=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p0)*(1/((1)))

theorem pivot_255 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^3*W^2)))*v 320 + ((((-1)*Y^2*Z)/(X^2*W^2)))*v 490 + ((1))*v 533=0 := by
  have h:=hv 240
  change (((1*Z)/(X^3*W^2)))*v 60 + ((1))*v 273 + (((1*Z)/(X^3*W^2)))*v 320 + ((1))*v 533=0 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X^3*W^2)))*p29 - ((1))*p230)*(1/((1)))

#print axioms pivot_255

theorem pivot_256 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 247 + ((((-1)*Y^2*Z)/(X^2*W^2)))*v 290 + (((1*Z)/(X^3*W^2)))*v 460=0 := by
  have h:=hv 241
  change ((1))*v 247 + (((1*Z)/(X^3*W^2)))*v 460 + ((1))*v 507 + (((1*Z)/(X^3*W^2)))*v 720=0 at h
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X^3*W^2)))*p30 - ((1))*p231)*(1/((1)))

theorem pivot_257 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 285 + ((1))*v 545 + ((((-1))/(X^2)))*v 630=0 := by
  have h:=hv 244
  change (((1*W^2)/(X^3*Z)))*v 156 + ((1))*v 285 + (((1*W^2)/(X^3*Z)))*v 416 + ((1))*v 545=0 at h
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X^3*Z)))*p47 - (((1*W^2)/(X^3*Z)))*p88)*(1/((1)))

theorem pivot_258 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 235 + ((1))*v 495 + (((1)/(X^2)))*v 630=0 := by
  have h:=hv 245
  change ((1))*v 235 + (((1*W^2)/(X^3*Z)))*v 364 + ((1))*v 495 + (((1*W^2)/(X^3*Z)))*v 624=0 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X^3*Z)))*p55 - (((1*W^2)/(X^3*Z)))*p87 - ((((-1))/(X^2)))*p248)*(1/((1)))

theorem pivot_259 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X*W^2)))*v 160 + ((1))*v 286 + (((1*Y^2*Z)/(X*W^2)))*v 680=0 := by
  have h:=hv 246
  change (((1*Z)/(X*W^2)))*v 160 + ((1))*v 286 + (((1*Z)/(X*W^2)))*v 420 + ((1))*v 546=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X*W^2)))*p39 - ((1))*p82 - ((((-1)*Y^2*Z)/(X*W^2)))*p246)*(1/((1)))

theorem pivot_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 494 + (((1*Z)/(X*W^2)))*v 620 + ((((-1)*Y^2*Z)/(X*W^2)))*v 680=0 := by
  have h:=hv 247
  change ((1))*v 234 + (((1*Z)/(X*W^2)))*v 360 + ((1))*v 494 + (((1*Z)/(X*W^2)))*v 620=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X*W^2)))*p18 - ((1))*p93)*(1/((1)))

theorem pivot_261 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*Z)))*v 520 + (((-1)))*v 540 + ((1))*v 630=0 := by
  have h:=hv 266
  change (((1*Y^2)/(Z)))*v 130 + ((1))*v 240 + (((1*Y^2)/(Z)))*v 520 + ((1))*v 630=0 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Y^2)/(Z)))*p86 - ((1))*p247 - ((((-1))/(X)))*p252)*(1/((1)))

theorem pivot_262 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(Z*W^2)))*v 520 + ((1))*v 652 + ((((-1)*X^2*Y^2)/(W^2)))*v 670=0 := by
  have h:=hv 269
  change (((1)/(Z*W^2)))*v 0 + ((1))*v 132 + (((1)/(Z*W^2)))*v 260 + ((1))*v 652=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p251:=pivot_251 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z*W^2)))*p0 - (((1)/(Z*W^2)))*p237 - ((1))*p251)*(1/((1)))

theorem pivot_263 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^2*Y^2)/(W^2)))*v 110 + ((1))*v 128 + (((1)/(Z*W^2)))*v 520=0 := by
  have h:=hv 270
  change (((1)/(Z*W^2)))*v 0 + ((1))*v 128 + (((1)/(Z*W^2)))*v 520 + ((1))*v 648=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p250:=pivot_250 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z*W^2)))*p0 - ((1))*p250)*(1/((1)))

theorem pivot_264 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 140 + ((((-1)*X^3)/(Z)))*v 195 + (((1)/(Z)))*v 520=0 := by
  have h:=hv 271
  change (((1)/(Z)))*v 0 + ((1))*v 140 + (((1)/(Z)))*v 520 + ((1))*v 660=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - ((1))*p90)*(1/((1)))

theorem pivot_265 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Z)))*v 195 + ((((-1))/(Z)))*v 520 + ((1))*v 640=0 := by
  have h:=hv 272
  change (((1)/(Z)))*v 0 + ((1))*v 120 + (((1)/(Z)))*v 260 + ((1))*v 640=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p237 - ((1))*p238)*(1/((1)))

theorem pivot_266 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 143 + ((((-1)*Y^2*Z)/(X^3*W^2)))*v 200 + (((1*Z)/(X^2*W^2)))*v 550=0 := by
  have h:=hv 273
  change (((1*Z)/(X^2*W^2)))*v 30 + ((1))*v 143 + (((1*Z)/(X^2*W^2)))*v 550 + ((1))*v 663=0 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X^2*W^2)))*p10 - ((1))*p91)*(1/((1)))

theorem pivot_267 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Z)/(X^2*W^2)))*v 230 + ((((-1)*Y^2*Z)/(X^3*W^2)))*v 580 + ((1))*v 637=0 := by
  have h:=hv 274
  change ((1))*v 117 + (((1*Z)/(X^2*W^2)))*v 230 + ((1))*v 637 + (((1*Z)/(X^2*W^2)))*v 750=0 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v hv
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X^2*W^2)))*p2 - ((1))*p84)*(1/((1)))

theorem pivot_268 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^2)/(Z)))*v 195 + ((1))*v 460 + ((((-1))/(Z)))*v 520=0 := by
  have h:=hv 286
  change (((1)/(Z)))*v 0 + ((1))*v 70 + (((1)/(Z)))*v 260 + ((1))*v 330 + (((1)/(Z)))*v 390 + ((1))*v 460 + (((1)/(Z)))*v 650 + ((1))*v 720=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p30:=pivot_30 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p23 - ((1))*p30 - (((1)/(Z)))*p89 - ((1))*p162 - ((1))*p192 - (((1)/(Z)))*p237 - (((1)/(X)))*p238)*(1/((1)))

theorem pivot_269 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 155 + ((((-1)*Y^2)/(X*Z)))*v 195 + ((((-1)*W^2)/(X^2*Z)))*v 208=0 := by
  have h:=hv 277
  change (((1*W^2)/(X^2*Z)))*v 78 + ((1))*v 155 + (((1*W^2)/(X^2*Z)))*v 598 + ((1))*v 675=0 at h
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p182:=pivot_182 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X^2*Z)))*p80 - ((1))*p182 - ((((-1))/(X^3)))*p185 - (((1*Y^2)/(X^3*Z)))*p237 - (((1*W^2)/(X^2*Z)))*p241 - (((1*Y^2)/(X^3)))*p268)*(1/((1)))

theorem pivot_270 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^2)/(Z)))*v 195 + ((1))*v 320 + (((1)/(Z)))*v 520=0 := by
  have h:=hv 287
  change (((1)/(Z)))*v 0 + ((1))*v 60 + (((1)/(Z)))*v 130 + ((1))*v 320 + (((1)/(Z)))*v 390 + ((1))*v 450 + (((1)/(Z)))*v 520 + ((1))*v 710=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p23 - ((1))*p29 - (((1)/(Z)))*p86 - ((1))*p155 - ((1))*p157)*(1/((1)))

theorem pivot_271 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*Z)))*v 195 + ((((-1)*W^2)/(X^2*Z)))*v 572 + ((1))*v 625=0 := by
  have h:=hv 278
  change ((1))*v 105 + (((1*W^2)/(X^2*Z)))*v 182 + ((1))*v 625 + (((1*W^2)/(X^2*Z)))*v 702=0 at h
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X^2*Z)))*p95 - ((((-1))/(X^3)))*p150 - ((1))*p161 - (((1*W^2)/(X^2*Z)))*p242 - (((1*Y^2)/(X^3)))*p270)*(1/((1)))

#print axioms pivot_271

theorem pivot_272 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Z)))*v 195 + ((1))*v 510 + ((((-1))/(X)))*v 540=0 := by
  have h:=hv 320
  change ((1))*v 8 + (((1)/(X)))*v 16 + ((1))*v 398=0 at h
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v hv
  have p122:=pivot_122 X Y Z W a b hX hY hZ hW v hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p65 - (((1)/(X)))*p122 - ((1))*p141 - (((1)/(X*W^2)))*p160 - (((1)/(Y^2*W^2)))*p249)*(1/((((-1))/(Y^2*W^2))))

theorem pivot_273 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 280 + (((1)/(X)))*v 560 + ((1))*v 670=0 := by
  have h:=hv 322
  change ((1))*v 11 + (((1)/(X)))*v 22 + ((1))*v 401=0 at h
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p124 - ((1))*p152 - (((1)/(X)))*p214)*(1/(((1)/(X^2*W^2))))

theorem pivot_274 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 104 + ((((-1)*X^4)/(Y^2*W^2)))*v 195 + ((1*X))*v 442=0 := by
  have h:=hv 325
  change ((1))*v 52 + (((1)/(X)))*v 104 + ((1))*v 442=0 at h
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p77 - ((((-1)*X*Z)/(Y^2*W^2)))*p162 - ((((-1)*Z)/(Y^2*W^2)))*p238)*(1/(((1)/(X))))

theorem pivot_275 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 95 + ((1))*v 485 + ((((-1))/(X)))*v 580=0 := by
  have h:=hv 328
  change ((1))*v 95 + (((1)/(X)))*v 190 + ((1))*v 485=0 at h
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p240)*(1/((1)))

theorem pivot_276 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X)))*v 200 + ((1))*v 490 + (((-1)))*v 680=0 := by
  have h:=hv 329
  change ((1))*v 100 + (((1)/(X)))*v 200 + ((1))*v 490=0 at h
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p246)*(1/((1)))

theorem pivot_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 290 + (((1)/(X)))*v 580 + ((1))*v 680=0 := by
  have h:=hv 299
  change ((1))*v 39 + ((1))*v 117 + ((1))*v 273 + ((1))*v 351 + ((1))*v 429 + ((1))*v 507 + ((1))*v 663 + ((1))*v 741=0 at h
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v hv
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v hv
  have p176:=pivot_176 X Y Z W a b hX hY hZ hW v hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p73 - ((1))*p84 - ((1))*p91 - ((1))*p102 - ((1))*p176 - ((1))*p200 - ((1))*p230 - ((1))*p231 - (((1*Y^2)/(X^3*W^2)))*p237 - ((((-1)*Z)/(X^3*W^2)))*p245 - ((((-1)*Y^2*Z)/(X^2*W^2)))*p276)*(1/((((-1)*Y^2*Z)/(X^2*W^2))))

theorem pivot_278 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 110 + (((1)/(X)))*v 220 + ((1))*v 500=0 := by
  have h:=hv 332
  change ((1))*v 110 + (((1)/(X)))*v 220 + ((1))*v 500=0 at h
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

theorem pivot_279 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(W^2)))*v 110 + ((1))*v 162 + ((1))*v 552=0 := by
  have h:=hv 335
  change ((1))*v 162 + (((1)/(X)))*v 324 + ((1))*v 552=0 at h
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p136)*(1/((1)))

theorem pivot_280 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 185 + ((((-1)*X)/(Y^2*Z)))*v 195 + ((1))*v 575=0 := by
  have h:=hv 336
  change ((1))*v 185 + (((1)/(X)))*v 370 + ((1))*v 575=0 at h
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p165)*(1/((1)))

theorem pivot_281 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X)/(Y^2*Z)))*v 195 + ((1))*v 205 + ((1))*v 595=0 := by
  have h:=hv 337
  change ((1))*v 205 + (((1)/(X)))*v 410 + ((1))*v 595=0 at h
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p153 - (((1)/(X^2*Y^2)))*p238)*(1/((1)))

theorem pivot_282 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Y^2*W^2)))*v 195 + ((1))*v 338 + (((1)/(X)))*v 676=0 := by
  have h:=hv 338
  change ((1))*v 225 + (((1)/(X)))*v 450 + ((1))*v 615=0 at h
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p92 - (((1)/(X)))*p155 - ((1))*p232)*(1/((((-1)*Y^2*W^2)/(X^2*Z))))

theorem pivot_283 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 228 + ((1))*v 618 + (((1*Y^2)/(W^2)))*v 670=0 := by
  have h:=hv 339
  change ((1))*v 228 + (((1)/(X)))*v 456 + ((1))*v 618=0 at h
  have p181:=pivot_181 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p181)*(1/((1)))

theorem pivot_284 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X)))*v 200 + ((1))*v 295 + ((1))*v 685=0 := by
  have h:=hv 341
  change ((1))*v 295 + (((1)/(X)))*v 590 + ((1))*v 685=0 at h
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p239)*(1/((1)))

theorem pivot_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X)/(Z)))*v 520 + ((((-1))/(Y^2)) + (((-1)*X^2)/(Y^2)))*v 540 + ((1))*v 680=0 := by
  have h:=hv 265
  change (((1*Z)/(W^2)))*v 120 + ((1))*v 234 + (((1*Z)/(W^2)))*v 510 + ((1))*v 624=0 at h
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p87 - ((1))*p93 - (((1*Z)/(W^2)))*p238 - ((((-1)*X*Z)/(W^2)))*p248 - (((1*X*Z)/(W^2)))*p261 - (((1*Z)/(W^2)))*p272)*(1/((((-1)*Y^2*Z)/(X*W^2))))

theorem pivot_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 442 + (((1*Y^2)/(W^2)))*v 520 + ((((-1)*Z)/(X*Y^2*W^2)) + (((-1)*Z)/(W^2)))*v 540=0 := by
  have h:=hv 280
  change ((1))*v 104 + (((1*Z)/(W^2)))*v 180 + ((1))*v 624 + (((1*Z)/(W^2)))*v 700=0 at h
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p87 - (((1*Z)/(W^2)))*p187 - (((1*Z)/(W^2)))*p245 - ((((-1)*X*Z)/(W^2)))*p248 - ((((-1)*Z)/(W^2)))*p252 - (((1*X*Z)/(W^2)))*p261 - (((1*X*Z)/(Y^2*W^2)))*p272 - ((1))*p274)*(1/(((-1)*X)))

theorem pivot_287 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 326 + (((1)/(X*Z*W^2)) + (((-1))/(Z*W^2)))*v 520 + (((1*X*Y^2)/(W^2)))*v 670=0 := by
  have h:=hv 284
  change (((1)/(Z*W^2)))*v 0 + ((1))*v 66 + (((1)/(Z*W^2)))*v 130 + ((1))*v 326 + (((1)/(Z*W^2)))*v 390 + ((1))*v 456 + (((1)/(Z*W^2)))*v 520 + ((1))*v 716=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v hv
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v hv
  have p181:=pivot_181 X Y Z W a b hX hY hZ hW v hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z*W^2)))*p0 - (((1)/(Z*W^2)))*p23 - ((1))*p46 - (((1)/(Z*W^2)))*p86 - ((1))*p181 - ((1))*p220 - ((((-1))/(X*Y^2*W^2)))*p252)*(1/((1)))

#print axioms pivot_287

theorem pivot_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X*Y^2)/(W^2)))*v 110 + ((1))*v 454 + ((((-1))/(X*Z*W^2)) + ((1)/(Z*W^2)))*v 520=0 := by
  have h:=hv 285
  change (((1)/(Z*W^2)))*v 0 + ((1))*v 64 + (((1)/(Z*W^2)))*v 260 + ((1))*v 324 + (((1)/(Z*W^2)))*v 390 + ((1))*v 454 + (((1)/(Z*W^2)))*v 650 + ((1))*v 714=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v hv
  have p50:=pivot_50 X Y Z W a b hX hY hZ hW v hv
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z*W^2)))*p0 - (((1)/(Z*W^2)))*p23 - ((1))*p50 - (((1)/(Z*W^2)))*p89 - ((1))*p135 - ((1))*p136 - ((((-1))/(X*Y^2*W^2)))*p245 - (((1)/(X*Y^2*W^2)))*p252)*(1/((1)))

theorem pivot_289 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 7 + (((1)/(Y^2*W^2)))*v 495 + (((1)/(X*Z*W^2)) + (((-1))/(Z*W^2)))*v 520=0 := by
  have h:=hv 319
  change ((1))*v 7 + (((1)/(X)))*v 14 + ((1))*v 397=0 at h
  have p125:=pivot_125 X Y Z W a b hX hY hZ hW v hv
  have p140:=pivot_140 X Y Z W a b hX hY hZ hW v hv
  have p186:=pivot_186 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p125 - ((1))*p140 - (((1)/(X^3*Y^2)))*p186 - (((1)/(X*Y^2*W^2)))*p243 - ((((-1))/(X*Y^2*W^2)))*p252)*(1/((1)))

theorem pivot_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)))*v 195 + ((((-1)*Y^2)/(Z)))*v 520 + ((1))*v 560=0 := by
  have h:=hv 348
  change ((1))*v 40 + ((((-1)*a)/(Y)))*v 120 + ((1))*v 300 + (((1)/(Y^2)))*v 360 + ((1))*v 560=0 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2)))*p18 - ((1))*p74 - ((1))*p150 - ((((-1)*a)/(Y)))*p238)*(1/((1)))

theorem pivot_291 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)))*v 195 + ((1))*v 220 + (((1*Y^2)/(Z)))*v 520=0 := by
  have h:=hv 358
  change ((1))*v 220 + (((1)/(Y^2)))*v 420 + ((1))*v 480 + ((((-1)*a)/(Y)))*v 660 + ((1))*v 740=0 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2)))*p39 - ((((-1)*a)/(Y)))*p90 - ((1))*p101 - ((1))*p185 - ((((-1)*Y^2)/(Z)))*p237 - (((1)/(Y^2)))*p238)*(1/((1)))

theorem pivot_292 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X*Z)))*v 195 + ((1))*v 285 + (((1*Y^2)/(X^3*Z)) + (((-1)*Y^2)/(X*Z)) + ((1*Y^2)/(Z)))*v 520=0 := by
  have h:=hv 324
  change ((1))*v 42 + (((1)/(X)))*v 84 + ((1))*v 432=0 at h
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v hv
  have p147:=pivot_147 X Y Z W a b hX hY hZ hW v hv
  have p182:=pivot_182 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p114 - ((1))*p147 - (((1*X^2)/(W^2)))*p182 - (((1)/(X)))*p194 - (((1*X)/(W^2)))*p244 - ((((-1)*X)/(W^2)))*p245 - (((1*X)/(W^2)))*p252 - (((1*Y^2)/(X*W^2)))*p268)*(1/(((1*X^2)/(W^2))))

theorem pivot_293 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X*Z)))*v 195 + ((1))*v 495 + ((((-1)*Y^2)/(X^3*Z)) + ((1*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)))*v 520=0 := by
  have h:=hv 331
  change ((1))*v 105 + (((1)/(X)))*v 210 + ((1))*v 495=0 at h
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p161 - (((1)/(X)))*p243 - ((((-1))/(X)))*p252 - (((1*Y^2)/(X^3)))*p270)*(1/((1)))

theorem pivot_294 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(W^2)) + ((1*Y^2)/(W^2)))*v 520 + ((((-1)*Z*a)/(Y*W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*Z)/(W^2)))*v 540 + ((1))*v 676=0 := by
  have h:=hv 345
  change ((1))*v 25 + ((((-1)*a)/(Y)))*v 75 + (((1)/(Y^2)))*v 225 + ((1))*v 285 + ((1))*v 545=0 at h
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v hv
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p70 - ((((-1)*a)/(Y)))*p79 - ((((-1)*W^2)/(X^3*Y^2*Z)))*p87 - (((1)/(Y^2)))*p92 - (((1*W^2*a)/(X^3*Y*Z)))*p148 - ((((-1)*a)/(X^3*Y)))*p247 - (((1)/(X^2*Y^2)))*p248 - ((1))*p257 - ((((-1))/(X^2*Y^2)) + ((1)/(X^2)))*p261)*(1/((((-1)*W^2)/(X^3*Z))))

theorem pivot_295 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 195 + (((1*Y^2)/(X^4)) + (((-1)*Y^4)/(X^4)) + ((1*Y^4)/(X^3)))*v 520 + ((((-1)*Z)/(X^4)) + ((1*Y*Z*a)/(X^4)) + (((-1)*Z)/(X^3)))*v 540=0 := by
  have h:=hv 279
  change (((1*Z)/(W^2)))*v 80 + ((1))*v 156 + (((1*Z)/(W^2)))*v 600 + ((1))*v 676=0 at h
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p88 - (((1*Z)/(W^2)))*p160 - (((1*X*Z)/(Y^2*W^2)))*p249 - (((1*Z)/(W^2)))*p252 - ((((-1)*X*Z)/(W^2)))*p261 - ((((-1)*X*Z)/(Y^2*W^2)))*p272 - ((1))*p294)*(1/(((1*X^4)/(Y^2*W^2))))

theorem pivot_296 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 208 + ((1))*v 572=0 := by
  have h:=hv 298
  change ((1))*v 52 + ((1))*v 104 + ((1))*v 208 + ((1))*v 364 + ((1))*v 416 + ((1))*v 572 + ((1))*v 676 + ((1))*v 728=0 at h
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v hv
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p47 - ((1))*p55 - ((1))*p77 - ((1))*p98 - ((((-1)*X*Z)/(Y^2*W^2)))*p155 - ((((-1)*X*Z)/(Y^2*W^2)))*p162 - ((((-1)*Z)/(Y^2*W^2)))*p238 - ((1))*p274 - (((-1)*X))*p286 - ((1))*p294 - (((1*X^4)/(Y^2*W^2)))*p295)*(1/((1)))

theorem pivot_297 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 160 + ((1))*v 620=0 := by
  have h:=hv 304
  change ((1))*v 26 + ((1))*v 182 + ((1))*v 286 + ((1))*v 338 + ((1))*v 442 + ((1))*v 494 + ((1))*v 598 + ((1))*v 754=0 at h
  have p61:=pivot_61 X Y Z W a b hX hY hZ hW v hv
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p260:=pivot_260 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p296:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p61 - ((1))*p71 - ((((-1)*Z)/(X*Y^2*W^2)))*p90 - ((((-1)*Z)/(X*Y^2*W^2)))*p238 - ((1))*p241 - ((1))*p242 - ((1))*p259 - ((1))*p260 - ((1))*p282 - ((1))*p286 - ((((-1))/(X)))*p294 - ((((-1)*X^3)/(Y^2*W^2)))*p295 - (((-1)))*p296)*(1/((((-1)*Z)/(X*W^2))))

theorem pivot_298 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^3*a)/(X*Z)) + ((1*Y^3*a)/(Z)))*v 520 + ((((-1))/(X*Y^2)) + ((1*a^2)/(X)) + (((-1)*a)/(Y)))*v 540 + ((1))*v 610=0 := by
  have h:=hv 263
  change (((1*W^2)/(Y^2*Z)))*v 78 + ((1))*v 220 + (((1*W^2)/(Y^2*Z)))*v 468 + ((1))*v 610=0 at h
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(Y^2*Z)))*p80 - (((1*W^2)/(Y^2*Z)))*p148 - ((((-1))/(X*Y^2)))*p185 - (((1)/(X*Z)))*p237 - ((((-1))/(Y^2)))*p247 - ((1))*p291 - ((((-1)*X^3)/(Y^2*Z)) + (((-1)*X^3*a)/(Y*Z)))*p295)*(1/((1)))

theorem pivot_299 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 170 + ((((-1)*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + (((-1)*Y^3*a)/(Z)))*v 520 + (((1)/(X*Y^2)) + (((-1)*a^2)/(X)) + ((1*a)/(Y)))*v 540=0 := by
  have h:=hv 264
  change ((1))*v 170 + (((1*W^2)/(Y^2*Z)))*v 312 + ((1))*v 560 + (((1*W^2)/(Y^2*Z)))*v 702=0 at h
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(Y^2*Z)))*p95 - ((((-1))/(X*Y^2)))*p150 - (((1*W^2)/(Y^2*Z)))*p188 - ((1))*p290 - (((1*X^3)/(Y^2*Z)) + ((1*X^3*a)/(Y*Z)))*p295)*(1/((1)))

theorem pivot_300 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^4)/(X*Z)))*v 520 + ((((-1))/(X^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X)) + ((-1)))*v 540 + ((1))*v 670=0 := by
  have h:=hv 275
  change (((1*X^2)/(Z)))*v 65 + ((1))*v 150 + (((1*X^2)/(Z)))*v 585 + ((1))*v 670=0 at h
  have p40:=pivot_40 X Y Z W a b hX hY hZ hW v hv
  have p85:=pivot_85 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X^2)/(Z)))*p40 - (((1*X^2)/(Z)))*p85 - ((((-1))/(X)))*p238 - ((1))*p248 - (((-1)))*p261 - ((((-1)*X^2)/(Z)))*p295)*(1/((1)))

theorem pivot_301 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 110 + ((((-1)*Y^2)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^2)/(X*Z)) + (((-1)*Y^4)/(X*Z)))*v 520 + (((1)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X)) + (1))*v 540=0 := by
  have h:=hv 276
  change ((1))*v 110 + (((1*X^2)/(Z)))*v 195 + ((1))*v 630 + (((1*X^2)/(Z)))*v 715=0 at h
  have p19:=pivot_19 X Y Z W a b hX hY hZ hW v hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X^2)/(Z)))*p19 - ((1))*p261 - (((1*X^2)/(Z)))*p295)*(1/((1)))

theorem pivot_302 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 200 + ((1))*v 580=0 := by
  have h:=hv 305
  change ((1))*v 20 + ((1))*v 40 + ((1))*v 80 + ((1))*v 100 + ((1))*v 140 + ((1))*v 160 + ((1))*v 200 + ((1))*v 220 + ((1))*v 280 + ((1))*v 320 + ((1))*v 340 + ((1))*v 380 + ((1))*v 400 + ((1))*v 440 + ((1))*v 460 + ((1))*v 500 + ((1))*v 560 + ((1))*v 580 + ((1))*v 620 + ((1))*v 640 + ((1))*v 680 + ((1))*v 700 + ((1))*v 740 + ((1))*v 760=0 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v hv
  have p28:=pivot_28 X Y Z W a b hX hY hZ hW v hv
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v hv
  have p154:=pivot_154 X Y Z W a b hX hY hZ hW v hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p249:=pivot_249 X Y Z W a b hX hY hZ hW v hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p25 - ((1))*p28 - ((1))*p37 - ((1))*p43 - ((1))*p74 - ((1))*p101 - ((1))*p154 - ((1))*p160 - ((1))*p187 - ((1))*p198 - (((1)/(Y^2)))*p238 - ((1))*p246 - (((1*X)/(Y^2)))*p248 - (((1*X)/(Y^2)))*p249 - ((1))*p264 - ((1))*p265 - ((1))*p268 - ((1))*p270 - ((1))*p273 - ((1))*p278 - ((((-1))/(X)) + (1))*p290 - ((((-1))/(X)) + (1))*p291 - ((1))*p297 - (((-1)))*p300 - (((-1)))*p301)*(1/((1)))

theorem pivot_303 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*X)/(Z)))*v 520 + (((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1)*X^2)/(Y^2)))*v 540 + ((1))*v 620=0 := by
  have h:=hv 346
  change ((1))*v 26 + ((((-1)*a)/(Y)))*v 78 + (((1)/(Y^2)))*v 234 + ((1))*v 286 + ((1))*v 546=0 at h
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p71 - ((((-1)*a)/(Y)))*p80 - ((1))*p82 - ((((-1)*Z)/(X*Y^2*W^2)))*p90 - (((1)/(Y^2)))*p93 - (((1*Z*a)/(X*Y*W^2)))*p185 - ((((-1)*Y*a)/(X*W^2)))*p237 - ((((-1)*Y^2*Z)/(X*W^2)))*p246 - ((1))*p259 - ((((-1)*Z)/(X*W^2)))*p285 - (((1*X^2)/(Y^2*W^2)))*p295 - ((((-1)*Z)/(X*W^2)))*p297)*(1/(((1*Z)/(X*W^2))))

#print axioms pivot_303

theorem pivot_304 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)))*v 520 + ((((-1)*Z)/(X*Y^2*W^2)) + ((1*Z*a)/(X*Y*W^2)) + (((-1)*Z)/(W^2)) + ((1*X*Z*a)/(Y*W^2)))*v 540 + ((1))*v 572=0 := by
  have h:=hv 330
  change ((1))*v 104 + (((1)/(X)))*v 208 + ((1))*v 494=0 at h
  have p260:=pivot_260 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p296:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p260 - ((1))*p274 - (((1*Y^2*Z)/(X*W^2)))*p285 - (((-1)*X))*p286 - (((1*X^4)/(Y^2*W^2)))*p295 - (((1)/(X)))*p296 - ((((-1)*Z)/(X*W^2)))*p303)*(1/((((-1))/(X))))

theorem pivot_305 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 310 + (((1)/(X^2*Z)) + (((-1)*Y^2)/(X^2*Z)) + (((-1)*Y*a)/(X*Z)) + ((1*Y^2)/(X*Z)) + (((-1)*Y^2)/(Z)) + ((1*X*Y^2)/(Z)))*v 520 + ((((-1))/(X^2*Y^2)) + ((1*a)/(X^2*Y)) + ((1*a)/(Y)))*v 540=0 := by
  have h:=hv 250
  change (((1*W^2)/(X*Z)))*v 208 + ((1))*v 310 + (((1*W^2)/(X*Z)))*v 468 + ((1))*v 570=0 at h
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p296:=pivot_296 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X*Z)))*p148 - ((1))*p244 - (((-1)))*p245 - ((((-1))/(X)))*p247 - ((1))*p252 - (((1*W^2)/(X*Z)))*p296 - ((((-1)*W^2)/(X*Z)))*p304)*(1/((1)))

theorem pivot_306 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 470 + ((((-1))/(X^2*Z)) + ((1*Y^2)/(X^2*Z)) + ((1*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + ((1*Y^2)/(Z)) + (((-1)*X*Y^2)/(Z)))*v 520 + (((1)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + (((-1)*a)/(Y)))*v 540=0 := by
  have h:=hv 251
  change ((1))*v 210 + (((1*W^2)/(X*Z)))*v 312 + ((1))*v 470 + (((1*W^2)/(X*Z)))*v 572=0 at h
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p304:=pivot_304 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X*Z)))*p188 - ((1))*p243 - (((-1)))*p252 - (((1*W^2)/(X*Z)))*p304)*(1/((1)))

theorem pivot_307 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 230 + ((1))*v 550=0 := by
  have h:=hv 314
  change ((1))*v 10 + ((1))*v 50 + ((1))*v 70 + ((1))*v 110 + ((1))*v 170 + ((1))*v 190 + ((1))*v 230 + ((1))*v 250 + ((1))*v 290 + ((1))*v 310 + ((1))*v 350 + ((1))*v 370 + ((1))*v 410 + ((1))*v 430 + ((1))*v 470 + ((1))*v 490 + ((1))*v 530 + ((1))*v 550 + ((1))*v 590 + ((1))*v 610 + ((1))*v 670 + ((1))*v 710 + ((1))*v 730 + ((1))*v 770=0 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v hv
  have p76:=pivot_76 X Y Z W a b hX hY hZ hW v hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v hv
  have p254:=pivot_254 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p305:=pivot_305 X Y Z W a b hX hY hZ hW v hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p8 - ((1))*p11 - ((1))*p76 - ((1))*p99 - ((((-1)*W^2)/(X*Y^2*Z)))*p148 - ((1))*p151 - ((1))*p153 - ((1))*p157 - ((1))*p165 - ((1))*p177 - ((((-1)*W^2)/(X*Y^2*Z)))*p188 - ((1))*p192 - (((1)/(X*Y^2)))*p238 - ((1))*p239 - ((1))*p240 - (((1)/(X*Y^2)))*p245 - (((2)/(X*Y^2)))*p247 - ((1))*p253 - ((1))*p254 - ((1))*p276 - ((1))*p277 - ((1))*p298 - ((1))*p299 - ((1))*p300 - ((1))*p301 - ((((-1))/(X)) + ((-1)))*p302 - ((1))*p305 - ((1))*p306)*(1/((1)))

theorem pivot_308 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^2*Z)) + ((1*Y^4)/(X^2*Z)) + (((-1)*Y^4)/(X*Z)) + (((-1))/(Z)) + (((-1)*Y*a)/(Z)) + ((1*X*Y*a)/(Z)))*v 520 + (((1)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((1)/(X)) + ((1)/(Y^2)))*v 540 + ((1))*v 580=0 := by
  have h:=hv 343
  change ((1))*v 13 + ((((-1)*a)/(Y)))*v 39 + (((1)/(Y^2)))*v 117 + ((1))*v 273 + ((1))*v 533=0 at h
  have p67:=pivot_67 X Y Z W a b hX hY hZ hW v hv
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v hv
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p67 - ((((-1)*a)/(Y)))*p73 - (((1)/(Y^2)))*p84 - ((1))*p230 - (((1*Z*a)/(X^3*Y*W^2)))*p245 - ((((-1)*Z*a)/(X^3*Y*W^2)))*p252 - ((1))*p255 - ((((-1)*Z)/(X^3*W^2)))*p270 - ((((-1))/(X*W^2)))*p295)*(1/((((-1)*Z)/(X^3*W^2))))

theorem pivot_309 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^4)/(X^2*Z*W^2)) + ((1*Y^6)/(X^2*Z*W^2)) + (((-1)*Y^6)/(X*Z*W^2)) + (((-1)*Y^2)/(Z*W^2)) + (((-1)*X*Y^2)/(Z*W^2)) + ((2*X^2*Y^2)/(Z*W^2)) + (((-1)*X^3*Y^2)/(Z*W^2)))*v 520 + (((1*Y^2)/(X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1)/(W^2)) + ((-1)))*v 540 + ((1))*v 552=0 := by
  have h:=hv 282
  change (((1)/(Z)))*v 0 + ((1))*v 84 + (((1)/(Z)))*v 156 + ((1))*v 240 + (((1)/(Z)))*v 468 + ((1))*v 552 + (((1)/(Z)))*v 624 + ((1))*v 708=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p292:=pivot_292 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - (((1)/(Z)))*p87 - (((1)/(Z)))*p88 - (((1)/(Z)))*p148 - ((1))*p189 - ((1))*p194 - (((1*X)/(W^2)))*p244 - ((((-1)*X)/(W^2)))*p245 - ((((-1))/(W^2)) + (1))*p247 - ((((-1)*X)/(W^2)))*p248 - (((1*X)/(W^2)))*p252 - (((1*X^3)/(W^2)))*p292 - (((1*X^2*Y^2)/(Z*W^2)))*p295)*(1/((1)))

theorem pivot_310 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 228 + (((1*Y^4)/(X^2*Z*W^2)) + (((-1)*Y^6)/(X^2*Z*W^2)) + ((1*Y^6)/(X*Z*W^2)) + ((1*Y^2)/(Z*W^2)) + ((1*X*Y^2)/(Z*W^2)) + (((-2)*X^2*Y^2)/(Z*W^2)) + ((1*X^3*Y^2)/(Z*W^2)))*v 520 + ((((-1)*Y^2)/(X^2*W^2)) + ((1*Y^3*a)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + (1))*v 540=0 := by
  have h:=hv 283
  change (((1)/(Z)))*v 0 + ((1))*v 72 + (((1)/(Z)))*v 156 + ((1))*v 228 + (((1)/(Z)))*v 312 + ((1))*v 540 + (((1)/(Z)))*v 624 + ((1))*v 696=0 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v hv
  have p186:=pivot_186 X Y Z W a b hX hY hZ hW v hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v hv
  have p248:=pivot_248 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p0 - ((1))*p78 - (((1)/(Z)))*p87 - (((1)/(Z)))*p88 - ((1))*p186 - (((1)/(Z)))*p188 - ((((-1)*X^3*Y^2)/(Z*W^2)))*p193 - (((1*X)/(W^2)))*p243 - ((((-1)*X)/(W^2)))*p248 - ((((-1)*X)/(W^2)))*p252 - (((1*X^3)/(W^2)))*p293 - ((((-1)*X^2*Y^2)/(Z*W^2)))*p295)*(1/((1)))

theorem pivot_311 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^3*a)/(X^5*Z)) + ((1*Y^5*a)/(X^5*Z)) + (((-1)*Y^5*a)/(X^4*Z)) + (((-1)*Y*a)/(X^3*Z)) + ((1*Y^4)/(X^2*Z)) + ((1*Y*a)/(X*Z)) + (((-1)*Y*a)/(Z)))*v 520 + (((1*Y*a)/(X^5)) + (((-1)*Y^2*a^2)/(X^5)) + ((1*Y*a)/(X^4)) + ((1)/(X^3*Y^2)) + (((-1))/(X^3)) + (((-1)*Y^2)/(X^2)))*v 540 + ((1))*v 685=0 := by
  have h:=hv 347
  change ((1))*v 35 + ((((-1)*a)/(Y)))*v 105 + ((1))*v 295 + (((1)/(Y^2)))*v 315 + ((1))*v 555=0 at h
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p83 - ((1))*p113 - ((((-1)*a)/(Y)))*p161 - (((1)/(Y^2)))*p196 - (((1)/(X^2*Y^2)))*p244 - ((((-1))/(X^2*Y^2)))*p245 - (((1)/(X^3)))*p246 - (((1)/(X^2*Y^2)))*p252 - ((((-1)*Y*a)/(X^3)))*p270 - ((((-1)*Y^2*W^2)/(X^3*Z)))*p274 - ((1))*p284 - ((((-1))/(X^3)))*p285 - (((1*Y^2*W^2)/(X^2*Z)))*p286 - ((((-1)*Y*a)/(X*Z)) + (((-1)*X)/(Z)))*p295 - (((1)/(X)))*p302 - ((((-1))/(X)))*p308)*(1/(((-1))))

theorem pivot_312 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1)*Y^2)/(X^3*Z)) + ((1*Y^4)/(X^3*Z)) + (((-1)*Y^4)/(X^2*Z)) + (((-2))/(X*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y*a)/(Z)) + (((-1)*Y^2)/(Z)) + ((1*X)/(Z)))*v 520 + (((1)/(X^3)) + (((-1)*Y*a)/(X^3)) + ((1)/(X^2)) + ((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1)*X^2)/(Y^2)))*v 540 + ((1))*v 550=0 := by
  have h:=hv 334
  change ((1))*v 143 + (((1)/(X)))*v 286 + ((1))*v 533=0 at h
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v hv
  have p266:=pivot_266 X Y Z W a b hX hY hZ hW v hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p255 - (((1)/(X)))*p259 - ((1))*p266 - ((((-1)*Z)/(X^3*W^2)))*p270 - (((1*Y^2*Z)/(X^2*W^2)))*p276 - ((((-1))/(X*W^2)))*p295 - ((((-1)*Z)/(X^2*W^2)))*p297 - (((1*Z)/(X^2*W^2)))*p303)*(1/((((-1)*Z)/(X^2*W^2))))

theorem pivot_313 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^5*Z)) + (((-1)*Y^4)/(X^5*Z)) + ((1*Y^4)/(X^4*Z)) + ((1)/(X^3*Z)) + ((1*Y^2)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1))/(X*Z)) + ((1)/(Z)))*v 520 + ((((-1))/(X^5)) + ((1*Y*a)/(X^5)) + (((-1))/(X^4)) + ((1*a)/(X^3*Y)) + (((-1))/(X^3)) + ((1*Y*a)/(X^2)) + (((-1))/(X)))*v 540 + ((1))*v 575=0 := by
  have h:=hv 349
  change ((1))*v 55 + ((((-1)*a)/(Y)))*v 165 + ((1))*v 315 + (((1)/(Y^2)))*v 495 + ((1))*v 575=0 at h
  have p51:=pivot_51 X Y Z W a b hX hY hZ hW v hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v hv
  have p229:=pivot_229 X Y Z W a b hX hY hZ hW v hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p293:=pivot_293 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p51 - ((1))*p196 - ((((-1)*a)/(Y)))*p229 - (((1*Y^2)/(X^3)))*p246 - ((((-1)*Y^2)/(X^3)))*p285 - (((1*Y*W^2*a)/(X^2*Z)))*p286 - (((1)/(Y^2)))*p293 - ((((-1))/(X*Z)))*p295)*(1/((1)))

theorem pivot_314 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 485 + ((((-1)*Y^3*a)/(X^5*Z)) + ((1*Y^5*a)/(X^5*Z)) + (((-1)*Y^5*a)/(X^4*Z)) + (((-1)*Y*a)/(X^3*Z)) + (((-1)*Y^2)/(X^3*Z)) + ((1*Y^4)/(X^3*Z)) + (((-1))/(X*Z)))*v 520 + (((1*Y*a)/(X^5)) + (((-1)*Y^2*a^2)/(X^5)) + ((1*Y*a)/(X^4)) + ((1)/(X^3*Y^2)) + (((-1)*Y*a)/(X^3)) + ((1)/(X^2)) + (((-1)*Y^2)/(X^2)) + ((1)/(X*Y^2)))*v 540=0 := by
  have h:=hv 352
  change (((1)/(Y^2)))*v 75 + ((1))*v 95 + ((((-1)*a)/(Y)))*v 285 + ((1))*v 355 + ((1))*v 615=0 at h
  have p53:=pivot_53 X Y Z W a b hX hY hZ hW v hv
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v hv
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p292:=pivot_292 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p308:=pivot_308 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p53 - (((1)/(Y^2)))*p79 - ((((-1)*W^2)/(X^3*Y^2*Z)))*p148 - ((1))*p232 - (((1)/(X^3*Y^2)))*p247 - ((1))*p275 - ((((-1)*Y^2*W^2)/(X^2*Z)))*p282 - ((((-1)*a)/(Y)))*p292 - (((1*Y^2*W^2)/(X^3*Z)))*p294 - ((((-1)*Y*a)/(X*Z)) + ((1*X)/(Z)))*p295 - (((1)/(X)))*p308)*(1/(((-1))))

theorem pivot_315 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    (((1*Y^2)/(X^5*Z)) + (((-1)*Y^4)/(X^5*Z)) + ((1*Y^4)/(X^4*Z)) + ((1*Y^2)/(X^3*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1))/(X*Z)) + ((1)/(Z)))*v 520 + ((((-1))/(X^5)) + ((1*Y*a)/(X^5)) + (((-1))/(X^4)) + ((1)/(X^3*Y^2)) + (((-1))/(X^3)) + ((1)/(X^2*Y^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X)))*v 540 + ((1))*v 595=0 := by
  have h:=hv 357
  change ((1))*v 205 + (((1)/(Y^2)))*v 285 + ((1))*v 465 + ((((-1)*a)/(Y)))*v 615 + ((1))*v 725=0 at h
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v hv
  have p183:=pivot_183 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p285:=pivot_285 X Y Z W a b hX hY hZ hW v hv
  have p292:=pivot_292 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p45 - ((1))*p183 - ((((-1)*a)/(Y)))*p232 - ((1))*p281 - (((1*Y*W^2*a)/(X^2*Z)))*p282 - (((1*Y^2)/(X^3)))*p285 - (((1)/(Y^2)))*p292 - ((((-1)*Y*W^2*a)/(X^3*Z)))*p294 - (((1)/(X*Z)) + (((-1)*X)/(Y^2*Z)) + (((-1)*X*a)/(Y*Z)))*p295)*(1/(((-1))))

theorem pivot_316 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((1))*v 44 + (((1)/(X^2*Z*W^2)) + ((1*Y*a)/(X^2*Z*W^2)) + (((-1)*Y^3*a)/(X^2*Z*W^2)) + (((-1)*Y^4)/(X^2*Z*W^2)) + ((1*Y^2)/(X*Z*W^2)) + ((1*Y^3*a)/(X*Z*W^2)) + ((1*Y^4)/(X*Z*W^2)) + ((1*X^2*Y^2)/(Z*W^2)))*v 520 + ((((-1))/(X^2*Y^2*W^2)) + (((-1))/(X^2*W^2)) + ((1*a^2)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1))/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + (((-1))/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 540=0 := by
  have h:=hv 323
  change ((1))*v 22 + (((1)/(X)))*v 44 + ((1))*v 412=0 at h
  have p167:=pivot_167 X Y Z W a b hX hY hZ hW v hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v hv
  have p229:=pivot_229 X Y Z W a b hX hY hZ hW v hv
  have p273:=pivot_273 X Y Z W a b hX hY hZ hW v hv
  have p286:=pivot_286 X Y Z W a b hX hY hZ hW v hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p167 - ((1))*p214 - (((1*X^3)/(Y^2*W^2)))*p229 - (((1)/(X*W^2)))*p273 - ((((-1)*X)/(Z)))*p286 - ((((-1))/(X^2*W^2)))*p290 - ((((-1)*X)/(Y^2*Z*W^2)) + (((-1)*X*a)/(Y*Z*W^2)))*p295 - ((((-1))/(X*W^2)))*p300)*(1/(((1)/(X))))

theorem pivot_317 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 780→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    ((((-1))/(X^2*Z*W^2)) + (((-1)*Y*a)/(X^2*Z*W^2)) + ((1*Y^3*a)/(X^2*Z*W^2)) + ((1*Y^4)/(X^2*Z*W^2)) + (((-1)*Y^2)/(X*Z*W^2)) + (((-1)*Y^3*a)/(X*Z*W^2)) + (((-1)*Y^4)/(X*Z*W^2)) + (((-1)*X^2*Y^2)/(Z*W^2)))*v 520 + (((1)/(X^2*Y^2*W^2)) + ((1)/(X^2*W^2)) + (((-1)*a^2)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + ((1)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 540 + ((1))*v 736=0 := by
  have h:=hv 342
  change ((1))*v 368 + (((1)/(X)))*v 736 + ((1))*v 758=0 at h
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v hv
  have p210:=pivot_210 X Y Z W a b hX hY hZ hW v hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v hv
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v hv
  have p295:=pivot_295 X Y Z W a b hX hY hZ hW v hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v hv
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p156 - ((1))*p210 - (((1*X^3)/(Y^2*W^2)))*p232 - (((1)/(X*W^2)))*p278 - ((((-1)*X)/(Z)))*p282 - ((((-1))/(X^2*W^2)))*p291 - (((1)/(Z)))*p294 - (((1*X)/(Y^2*Z*W^2)) + ((1*X*a)/(Y*Z*W^2)) + ((1*X^4)/(Y^2*Z*W^2)))*p295 - ((((-1))/(X*W^2)))*p301)*(1/(((1)/(X))))

#print axioms pivot_317

end SmallLevelTwentySixUnitMMP
