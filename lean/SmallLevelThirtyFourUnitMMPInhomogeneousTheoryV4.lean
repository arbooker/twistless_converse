module
public meta import SmallLevelTriangularCertificateCommandsV4

public import SmallLevelThirtyFourUnitMMPRowsV1

set_option Elab.async false
set_option linter.unusedTactic false
set_option stderrAsMessages false

/-! Consolidated chapter: SmallLevelThirtyFourUnitMMPInhomogeneous. Original declarations and local scopes are retained. -/

/-! ## SmallLevelThirtyFourUnitMMPInhomogeneousBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex SmallLevelThirtyFourUnitMMP

def rhsPivot0 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 19)/((1))

compact_elimination_proof
theorem pivot_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 84=rhsPivot0 X Y Z W a b r := by
  have h:=hv 19
  change ((1))*v 84=r 19 at h
  unfold rhsPivot0
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot1 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 47)/((1))

compact_elimination_proof
theorem pivot_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 500=rhsPivot1 X Y Z W a b r := by
  have h:=hv 47
  change ((1))*v 500=r 47 at h
  unfold rhsPivot1
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot2 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 59 - ((1))*rhsPivot0 X Y Z W a b r)/((((-1)*X)/(W^2)))

compact_elimination_proof
theorem pivot_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 495=rhsPivot2 X Y Z W a b r := by
  have h:=hv 59
  change ((1))*v 84 + ((((-1)*X)/(W^2)))*v 495=r 59 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot2
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p0)*(1/((((-1)*X)/(W^2))))

def rhsPivot3 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 10 - (((-1)*X))*rhsPivot2 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 90=rhsPivot3 X Y Z W a b r := by
  have h:=hv 10
  change ((1))*v 90 + (((-1)*X))*v 495=r 10 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot3
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p2)*(1/((1)))

def rhsPivot4 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 4 - ((1))*rhsPivot3 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 420=rhsPivot4 X Y Z W a b r := by
  have h:=hv 4
  change ((1))*v 90 + (((-1)))*v 420=r 4 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot4
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p3)*(1/(((-1))))

def rhsPivot5 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 22 - ((1))*rhsPivot3 X Y Z W a b r)/(((-1)*X))

compact_elimination_proof
theorem pivot_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 15=rhsPivot5 X Y Z W a b r := by
  have h:=hv 22
  change (((-1)*X))*v 15 + ((1))*v 90=r 22 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot5
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p3)*(1/(((-1)*X)))

def rhsPivot6 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 26 - ((1*Z))*rhsPivot2 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 255=rhsPivot6 X Y Z W a b r := by
  have h:=hv 26
  change ((1))*v 255 + ((1*Z))*v 495=r 26 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot6
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1*Z))*p2)*(1/((1)))

def rhsPivot7 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 28 - (((1)/(Y^2*Z*W^2)))*rhsPivot6 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 271=rhsPivot7 X Y Z W a b r := by
  have h:=hv 28
  change (((1)/(Y^2*Z*W^2)))*v 255 + ((1))*v 271=r 28 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot7
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2*Z*W^2)))*p6)*(1/((1)))

def rhsPivot8 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 40 - ((1))*rhsPivot3 X Y Z W a b r)/(((-1)*W^2))

compact_elimination_proof
theorem pivot_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 18=rhsPivot8 X Y Z W a b r := by
  have h:=hv 40
  change (((-1)*W^2))*v 18 + ((1))*v 90=r 40 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot8
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p3)*(1/(((-1)*W^2)))

def rhsPivot9 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 44 - ((1))*rhsPivot2 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 270=rhsPivot9 X Y Z W a b r := by
  have h:=hv 44
  change ((((-1))/(X)))*v 270 + ((1))*v 495=r 44 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot9
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p2)*(1/((((-1))/(X))))

def rhsPivot10 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 27 - ((1))*rhsPivot9 X Y Z W a b r)/(((1)/(Z)))

compact_elimination_proof
theorem pivot_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 0=rhsPivot10 X Y Z W a b r := by
  have h:=hv 27
  change (((1)/(Z)))*v 0 + ((1))*v 270=r 27 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot10
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p9)*(1/(((1)/(Z))))

def rhsPivot11 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 7 - ((((-1))/(X*Y^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 85=rhsPivot11 X Y Z W a b r := by
  have h:=hv 7
  change ((((-1))/(X*Y^2)))*v 0 + ((1))*v 85=r 7 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot11
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2)))*p10)*(1/((1)))

def rhsPivot12 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 1 - ((1))*rhsPivot11 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 425=rhsPivot12 X Y Z W a b r := by
  have h:=hv 1
  change ((1))*v 85 + (((-1)))*v 425=r 1 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot12
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p11)*(1/(((-1))))

def rhsPivot13 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 25 - ((1))*rhsPivot10 X Y Z W a b r)/((1*Z))

compact_elimination_proof
theorem pivot_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 480=rhsPivot13 X Y Z W a b r := by
  have h:=hv 25
  change ((1))*v 0 + ((1*Z))*v 480=r 25 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot13
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p10)*(1/((1*Z)))

def rhsPivot14 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 29 - (((1*Z)/(Y^2*W^2)))*rhsPivot13 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 272=rhsPivot14 X Y Z W a b r := by
  have h:=hv 29
  change ((1))*v 272 + (((1*Z)/(Y^2*W^2)))*v 480=r 29 at h
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot14
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(Y^2*W^2)))*p13)*(1/((1)))

def rhsPivot15 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 33 - ((1))*rhsPivot9 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 30=rhsPivot15 X Y Z W a b r := by
  have h:=hv 33
  change (((-1)))*v 30 + ((1))*v 270=r 33 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot15
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p9)*(1/(((-1))))

#print axioms pivot_15

def rhsPivot16 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 51 - ((1))*rhsPivot5 X Y Z W a b r)/((((-1)*W^2)/(X)))

compact_elimination_proof
theorem pivot_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 426=rhsPivot16 X Y Z W a b r := by
  have h:=hv 51
  change ((1))*v 15 + ((((-1)*W^2)/(X)))*v 426=r 51 at h
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot16
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p5)*(1/((((-1)*W^2)/(X))))

def rhsPivot17 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 60 - ((((-1))/(X*Y^2*W^2)))*rhsPivot13 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 91=rhsPivot17 X Y Z W a b r := by
  have h:=hv 60
  change ((1))*v 91 + ((((-1))/(X*Y^2*W^2)))*v 480=r 60 at h
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot17
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p13)*(1/((1)))

def rhsPivot18 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 62 - ((((-1))/(X*W^2)))*rhsPivot9 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 93=rhsPivot18 X Y Z W a b r := by
  have h:=hv 62
  change ((1))*v 93 + ((((-1))/(X*W^2)))*v 270=r 62 at h
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot18
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p9)*(1/((1)))

def rhsPivot19 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 23 - ((1))*rhsPivot18 X Y Z W a b r)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 16=rhsPivot19 X Y Z W a b r := by
  have h:=hv 23
  change ((((-1)*Y^2)/(X)))*v 16 + ((1))*v 93=r 23 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot19
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18)*(1/((((-1)*Y^2)/(X))))

def rhsPivot20 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 76 - ((((-1))/(X*Y^2*W^2)))*rhsPivot15 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 419=rhsPivot20 X Y Z W a b r := by
  have h:=hv 76
  change ((((-1))/(X*Y^2*W^2)))*v 30 + ((1))*v 419=r 76 at h
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot20
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p15)*(1/((1)))

def rhsPivot21 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 79 - ((((-1)*W^2)/(Y^2)))*rhsPivot16 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 260=rhsPivot21 X Y Z W a b r := by
  have h:=hv 79
  change ((1))*v 260 + ((((-1)*W^2)/(Y^2)))*v 426=r 79 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot21
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(Y^2)))*p16)*(1/((1)))

def rhsPivot22 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 31 - ((1))*rhsPivot21 X Y Z W a b r)/(((-1)*W^2))

compact_elimination_proof
theorem pivot_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 32=rhsPivot22 X Y Z W a b r := by
  have h:=hv 31
  change (((-1)*W^2))*v 32 + ((1))*v 260=r 31 at h
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot22
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p21)*(1/(((-1)*W^2)))

def rhsPivot23 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 81 - ((((-1))/(Y^2*W^2)))*rhsPivot13 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 266=rhsPivot23 X Y Z W a b r := by
  have h:=hv 81
  change ((1))*v 266 + ((((-1))/(Y^2*W^2)))*v 480=r 81 at h
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot23
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(Y^2*W^2)))*p13)*(1/((1)))

def rhsPivot24 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 88)/((1))

compact_elimination_proof
theorem pivot_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 278=rhsPivot24 X Y Z W a b r := by
  have h:=hv 88
  change ((1))*v 278=r 88 at h
  unfold rhsPivot24
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot25 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 101 - ((((-1)*X)/(Y^2*W^2)))*rhsPivot2 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 494=rhsPivot25 X Y Z W a b r := by
  have h:=hv 101
  change ((1))*v 494 + ((((-1)*X)/(Y^2*W^2)))*v 495=r 101 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot25
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2*W^2)))*p2)*(1/((1)))

def rhsPivot26 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 95 - ((((-1)*Y^2)/(X)))*rhsPivot25 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 417=rhsPivot26 X Y Z W a b r := by
  have h:=hv 95
  change ((1))*v 417 + ((((-1)*Y^2)/(X)))*v 494=r 95 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot26
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X)))*p25)*(1/((1)))

def rhsPivot27 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 74 - (((-1)*X*W^2))*rhsPivot26 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 240=rhsPivot27 X Y Z W a b r := by
  have h:=hv 74
  change ((1))*v 240 + (((-1)*X*W^2))*v 417=r 74 at h
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot27
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*W^2))*p26)*(1/((1)))

def rhsPivot28 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 100 - ((1))*rhsPivot27 X Y Z W a b r)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 478=rhsPivot28 X Y Z W a b r := by
  have h:=hv 100
  change ((1))*v 240 + (((-1)*Y^2*W^2))*v 478=r 100 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot28
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p27)*(1/(((-1)*Y^2*W^2)))

def rhsPivot29 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 104 - ((1))*rhsPivot15 X Y Z W a b r)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 232=rhsPivot29 X Y Z W a b r := by
  have h:=hv 104
  change ((1))*v 30 + (((-1)*Y^2*W^2))*v 232=r 104 at h
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot29
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p15)*(1/(((-1)*Y^2*W^2)))

def rhsPivot30 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 105 - ((1))*rhsPivot8 X Y Z W a b r)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 269=rhsPivot30 X Y Z W a b r := by
  have h:=hv 105
  change ((1))*v 18 + (((-1)*X*Y^2))*v 269=r 105 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot30
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p8)*(1/(((-1)*X*Y^2)))

def rhsPivot31 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 110 - ((1))*rhsPivot6 X Y Z W a b r)/(((1*Y^2*Z)/(X)))

compact_elimination_proof
theorem pivot_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 10=rhsPivot31 X Y Z W a b r := by
  have h:=hv 110
  change (((1*Y^2*Z)/(X)))*v 10 + ((1))*v 255=r 110 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot31
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p6)*(1/(((1*Y^2*Z)/(X))))

#print axioms pivot_31

def rhsPivot32 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 111 - (((1)/(X*Y^2*Z*W^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 1=rhsPivot32 X Y Z W a b r := by
  have h:=hv 111
  change (((1)/(X*Y^2*Z*W^2)))*v 0 + ((1))*v 1=r 111 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot32
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z*W^2)))*p10)*(1/((1)))

def rhsPivot33 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 112 - (((1*X)/(Y^2*Z*W^2)))*rhsPivot6 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 2=rhsPivot33 X Y Z W a b r := by
  have h:=hv 112
  change ((1))*v 2 + (((1*X)/(Y^2*Z*W^2)))*v 255=r 112 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot33
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Y^2*Z*W^2)))*p6)*(1/((1)))

def rhsPivot34 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 113 - (((1)/(X*Z*W^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 3=rhsPivot34 X Y Z W a b r := by
  have h:=hv 113
  change (((1)/(X*Z*W^2)))*v 0 + ((1))*v 3=r 113 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot34
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z*W^2)))*p10)*(1/((1)))

def rhsPivot35 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 114 - (((1)/(X*Y^2*Z)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 5=rhsPivot35 X Y Z W a b r := by
  have h:=hv 114
  change (((1)/(X*Y^2*Z)))*v 0 + ((1))*v 5=r 114 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot35
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z)))*p10)*(1/((1)))

def rhsPivot36 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 115 - (((1*X)/(Z*W^2)))*rhsPivot6 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 6=rhsPivot36 X Y Z W a b r := by
  have h:=hv 115
  change ((1))*v 6 + (((1*X)/(Z*W^2)))*v 255=r 115 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot36
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z*W^2)))*p6)*(1/((1)))

def rhsPivot37 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 123 - ((1))*rhsPivot12 X Y Z W a b r)/(((1*Z*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 492=rhsPivot37 X Y Z W a b r := by
  have h:=hv 123
  change ((1))*v 425 + (((1*Z*W^2)/(X*Y^2)))*v 492=r 123 at h
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot37
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p12)*(1/(((1*Z*W^2)/(X*Y^2))))

def rhsPivot38 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 127 - (((1*Y^2)/(Z*W^2)))*rhsPivot12 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 33=rhsPivot38 X Y Z W a b r := by
  have h:=hv 127
  change ((1))*v 33 + (((1*Y^2)/(Z*W^2)))*v 425=r 127 at h
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot38
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Y^2)/(Z*W^2)))*p12)*(1/((1)))

def rhsPivot39 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 129 - ((1))*rhsPivot11 X Y Z W a b r)/(((1*Z*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 477=rhsPivot39 X Y Z W a b r := by
  have h:=hv 129
  change ((1))*v 85 + (((1*Z*W^2)/(Y^2)))*v 477=r 129 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot39
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p11)*(1/(((1*Z*W^2)/(Y^2))))

def rhsPivot40 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 148 - ((((-1)*X)/(Y^2*W^2)))*rhsPivot6 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 238=rhsPivot40 X Y Z W a b r := by
  have h:=hv 148
  change ((1))*v 238 + ((((-1)*X)/(Y^2*W^2)))*v 255=r 148 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot40
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2*W^2)))*p6)*(1/((1)))

def rhsPivot41 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 149 - ((((-1))/(X*Y^2*W^2)))*rhsPivot13 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 239=rhsPivot41 X Y Z W a b r := by
  have h:=hv 149
  change ((1))*v 239 + ((((-1))/(X*Y^2*W^2)))*v 480=r 149 at h
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot41
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p13)*(1/((1)))

def rhsPivot42 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 150 - ((((-1))/(X*Y^2*W^2)))*rhsPivot3 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 241=rhsPivot42 X Y Z W a b r := by
  have h:=hv 150
  change ((((-1))/(X*Y^2*W^2)))*v 90 + ((1))*v 241=r 150 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot42
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p3)*(1/((1)))

def rhsPivot43 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 155 - ((((-1)*X)/(Y^2)))*rhsPivot2 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 250=rhsPivot43 X Y Z W a b r := by
  have h:=hv 155
  change ((1))*v 250 + ((((-1)*X)/(Y^2)))*v 495=r 155 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot43
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2)))*p2)*(1/((1)))

def rhsPivot44 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 50 - ((((-1))/(X)))*rhsPivot43 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 505=rhsPivot44 X Y Z W a b r := by
  have h:=hv 50
  change ((((-1))/(X)))*v 250 + ((1))*v 505=r 50 at h
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot44
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p43)*(1/((1)))

def rhsPivot45 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 133 - ((((-1)*X*Y^2)/(W^2)))*rhsPivot44 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 252=rhsPivot45 X Y Z W a b r := by
  have h:=hv 133
  change ((1))*v 252 + ((((-1)*X*Y^2)/(W^2)))*v 505=r 133 at h
  have p44:=pivot_44 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot45
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X*Y^2)/(W^2)))*p44)*(1/((1)))

def rhsPivot46 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 156 - ((((-1)*X*Y^2)/(W^2)))*rhsPivot35 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 258=rhsPivot46 X Y Z W a b r := by
  have h:=hv 156
  change ((((-1)*X*Y^2)/(W^2)))*v 5 + ((1))*v 258=r 156 at h
  have p35:=pivot_35 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot46
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X*Y^2)/(W^2)))*p35)*(1/((1)))

def rhsPivot47 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 172 - ((1))*rhsPivot1 X Y Z W a b r)/((((-1)*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 504=rhsPivot47 X Y Z W a b r := by
  have h:=hv 172
  change ((1))*v 500 + ((((-1)*W^2)/(Y^2)))*v 504=r 172 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot47
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p1)*(1/((((-1)*W^2)/(Y^2))))

#print axioms pivot_47

def rhsPivot48 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 176 - ((1))*rhsPivot15 X Y Z W a b r)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 244=rhsPivot48 X Y Z W a b r := by
  have h:=hv 176
  change ((1))*v 30 + (((-1)*Y^2*W^2))*v 244=r 176 at h
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot48
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p15)*(1/(((-1)*Y^2*W^2)))

def rhsPivot49 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 179 - ((1))*rhsPivot44 X Y Z W a b r)/((((-1)*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 507=rhsPivot49 X Y Z W a b r := by
  have h:=hv 179
  change ((1))*v 505 + ((((-1)*W^2)/(Y^2)))*v 507=r 179 at h
  have p44:=pivot_44 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot49
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p44)*(1/((((-1)*W^2)/(Y^2))))

def rhsPivot50 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 180 - (((1)/(Y^2*Z*W^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 254=rhsPivot50 X Y Z W a b r := by
  have h:=hv 180
  change (((1)/(Y^2*Z*W^2)))*v 0 + ((1))*v 254=r 180 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot50
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2*Z*W^2)))*p10)*(1/((1)))

def rhsPivot51 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 181 - (((1)/(Y^2*Z*W^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 256=rhsPivot51 X Y Z W a b r := by
  have h:=hv 181
  change (((1)/(Y^2*Z*W^2)))*v 0 + ((1))*v 256=r 181 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot51
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2*Z*W^2)))*p10)*(1/((1)))

def rhsPivot52 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 184 - (((1*X)/(Y^2*Z*W^2)))*rhsPivot6 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 508=rhsPivot52 X Y Z W a b r := by
  have h:=hv 184
  change (((1*X)/(Y^2*Z*W^2)))*v 255 + ((1))*v 508=r 184 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot52
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Y^2*Z*W^2)))*p6)*(1/((1)))

def rhsPivot53 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 185 - (((1)/(X*Y^2*Z*W^2)))*rhsPivot10 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 509=rhsPivot53 X Y Z W a b r := by
  have h:=hv 185
  change (((1)/(X*Y^2*Z*W^2)))*v 0 + ((1))*v 509=r 185 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot53
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Y^2*Z*W^2)))*p10)*(1/((1)))

def rhsPivot54 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 0)/(((-1)*W^2))

compact_elimination_proof
theorem pivot_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)))*v 75 + ((1))*v 423=rhsPivot54 X Y Z W a b r := by
  have h:=hv 0
  change ((1))*v 75 + (((-1)*W^2))*v 423=r 0 at h
  unfold rhsPivot54
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*W^2)))

def rhsPivot55 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 2)/((1))

compact_elimination_proof
theorem pivot_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 87 + ((((-1))/(W^2)))*v 435=rhsPivot55 X Y Z W a b r := by
  have h:=hv 2
  change ((1))*v 87 + ((((-1))/(W^2)))*v 435=r 2 at h
  unfold rhsPivot55
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot56 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 3)/((1))

compact_elimination_proof
theorem pivot_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 88 + ((((-1))/(W^2)))*v 410=rhsPivot56 X Y Z W a b r := by
  have h:=hv 3
  change ((1))*v 88 + ((((-1))/(W^2)))*v 410=r 3 at h
  unfold rhsPivot56
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot57 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 5)/(((-1)*W^2))

compact_elimination_proof
theorem pivot_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)))*v 100 + ((1))*v 422=rhsPivot57 X Y Z W a b r := by
  have h:=hv 5
  change ((1))*v 100 + (((-1)*W^2))*v 422=r 5 at h
  unfold rhsPivot57
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*W^2)))

def rhsPivot58 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 6)/((((-1)*W^2)/(X)))

compact_elimination_proof
theorem pivot_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(W^2)))*v 75 + ((1))*v 498=rhsPivot58 X Y Z W a b r := by
  have h:=hv 6
  change ((1))*v 75 + ((((-1)*W^2)/(X)))*v 498=r 6 at h
  unfold rhsPivot58
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X))))

def rhsPivot59 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 8)/((1))

compact_elimination_proof
theorem pivot_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 86 + ((((-1)*X)/(Y^2*W^2)))*v 465=rhsPivot59 X Y Z W a b r := by
  have h:=hv 8
  change ((1))*v 86 + ((((-1)*X)/(Y^2*W^2)))*v 465=r 8 at h
  unfold rhsPivot59
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot60 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 9 - ((1))*rhsPivot55 X Y Z W a b r)/((((-1)*Y^2)/(X*W^2)))

compact_elimination_proof
theorem pivot_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 435 + ((1))*v 490=rhsPivot60 X Y Z W a b r := by
  have h:=hv 9
  change ((1))*v 87 + ((((-1)*Y^2)/(X*W^2)))*v 490=r 9 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot60
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p55)*(1/((((-1)*Y^2)/(X*W^2))))

def rhsPivot61 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 11)/(((-1)*X*Y^2*W^2))

compact_elimination_proof
theorem pivot_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2*W^2)))*v 150 + ((1))*v 497=rhsPivot61 X Y Z W a b r := by
  have h:=hv 11
  change ((1))*v 150 + (((-1)*X*Y^2*W^2))*v 497=r 11 at h
  unfold rhsPivot61
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

def rhsPivot62 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 12 - ((((-1)*X*W^2)/(Y^2)))*rhsPivot55 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 280 + ((((-1)*X)/(Y^2)))*v 435=rhsPivot62 X Y Z W a b r := by
  have h:=hv 12
  change ((((-1)*X*W^2)/(Y^2)))*v 87 + ((1))*v 280=r 12 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot62
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X*W^2)/(Y^2)))*p55)*(1/((1)))

def rhsPivot63 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 13)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 19 + ((((-1))/(X*Y^2)))*v 66=rhsPivot63 X Y Z W a b r := by
  have h:=hv 13
  change (((-1)*X*Y^2))*v 19 + ((1))*v 66=r 13 at h
  unfold rhsPivot63
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2)))

#print axioms pivot_63

def rhsPivot64 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 14)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 20 + ((((-1)*X)/(Y^2)))*v 75=rhsPivot64 X Y Z W a b r := by
  have h:=hv 14
  change ((((-1)*Y^2)/(X)))*v 20 + ((1))*v 75=r 14 at h
  unfold rhsPivot64
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2)/(X))))

def rhsPivot65 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 15)/(((-1)*X))

compact_elimination_proof
theorem pivot_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 21 + ((((-1))/(X)))*v 78=rhsPivot65 X Y Z W a b r := by
  have h:=hv 15
  change (((-1)*X))*v 21 + ((1))*v 78=r 15 at h
  unfold rhsPivot65
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X)))

def rhsPivot66 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 16)/((1))

compact_elimination_proof
theorem pivot_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 24 + ((1))*v 81=rhsPivot66 X Y Z W a b r := by
  have h:=hv 16
  change ((((-1))/(X)))*v 24 + ((1))*v 81=r 16 at h
  unfold rhsPivot66
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot67 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 17)/((1))

compact_elimination_proof
theorem pivot_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 27 + ((1))*v 82=rhsPivot67 X Y Z W a b r := by
  have h:=hv 17
  change ((((-1)*X)/(Y^2)))*v 27 + ((1))*v 82=r 17 at h
  unfold rhsPivot67
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot68 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 18)/((1))

compact_elimination_proof
theorem pivot_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2)))*v 36 + ((1))*v 83=rhsPivot68 X Y Z W a b r := by
  have h:=hv 18
  change ((((-1))/(X*Y^2)))*v 36 + ((1))*v 83=r 18 at h
  unfold rhsPivot68
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot69 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 20 - ((1))*rhsPivot59 X Y Z W a b r)/((((-1)*X)/(Y^2)))

compact_elimination_proof
theorem pivot_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 9 + ((((-1))/(W^2)))*v 465=rhsPivot69 X Y Z W a b r := by
  have h:=hv 20
  change ((((-1)*X)/(Y^2)))*v 9 + ((1))*v 86=r 20 at h
  have p59:=pivot_59 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot69
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p59)*(1/((((-1)*X)/(Y^2))))

def rhsPivot70 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 21 - ((1))*rhsPivot55 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 12 + ((((-1)*X)/(W^2)))*v 435=rhsPivot70 X Y Z W a b r := by
  have h:=hv 21
  change ((((-1))/(X)))*v 12 + ((1))*v 87=r 21 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot70
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p55)*(1/((((-1))/(X))))

def rhsPivot71 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 24)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 17 + ((((-1))/(X*Y^2)))*v 102=rhsPivot71 X Y Z W a b r := by
  have h:=hv 24
  change (((-1)*X*Y^2))*v 17 + ((1))*v 102=r 24 at h
  unfold rhsPivot71
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2)))

def rhsPivot72 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 30)/(((1*Y^2*W^2)/(Z)))

compact_elimination_proof
theorem pivot_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Z)/(Y^2*W^2)))*v 285 + ((1))*v 493=rhsPivot72 X Y Z W a b r := by
  have h:=hv 30
  change ((1))*v 285 + (((1*Y^2*W^2)/(Z)))*v 493=r 30 at h
  unfold rhsPivot72
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*Y^2*W^2)/(Z))))

def rhsPivot73 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 32)/((1))

compact_elimination_proof
theorem pivot_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)))*v 40 + ((1))*v 268=rhsPivot73 X Y Z W a b r := by
  have h:=hv 32
  change ((((-1))/(W^2)))*v 40 + ((1))*v 268=r 32 at h
  unfold rhsPivot73
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot74 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 34)/(((-1)*X))

compact_elimination_proof
theorem pivot_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 276 + ((1))*v 483=rhsPivot74 X Y Z W a b r := by
  have h:=hv 34
  change ((1))*v 276 + (((-1)*X))*v 483=r 34 at h
  unfold rhsPivot74
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X)))

def rhsPivot75 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 35)/((1))

compact_elimination_proof
theorem pivot_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 277 + ((((-1))/(X*Y^2)))*v 486=rhsPivot75 X Y Z W a b r := by
  have h:=hv 35
  change ((1))*v 277 + ((((-1))/(X*Y^2)))*v 486=r 35 at h
  unfold rhsPivot75
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot76 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 36)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 279 + ((1))*v 482=rhsPivot76 X Y Z W a b r := by
  have h:=hv 36
  change ((1))*v 279 + ((((-1)*Y^2)/(X)))*v 482=r 36 at h
  unfold rhsPivot76
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2)/(X))))

def rhsPivot77 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 37 - (((-1)*X*W^2))*rhsPivot55 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 60 + (((-1)*X))*v 435=rhsPivot77 X Y Z W a b r := by
  have h:=hv 37
  change ((1))*v 60 + (((-1)*X*W^2))*v 87=r 37 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot77
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*W^2))*p55)*(1/((1)))

def rhsPivot78 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 38 - ((((-1)*Y^2*W^2)/(X)))*rhsPivot56 X Y Z W a b r)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 135 + ((1))*v 410=rhsPivot78 X Y Z W a b r := by
  have h:=hv 38
  change ((((-1)*Y^2*W^2)/(X)))*v 88 + ((1))*v 135=r 38 at h
  have p56:=pivot_56 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot78
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2*W^2)/(X)))*p56)*(1/((((-1)*Y^2)/(X))))

def rhsPivot79 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 39)/(((-1)*X*Y^2*W^2))

compact_elimination_proof
theorem pivot_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 89 + ((((-1))/(X*Y^2*W^2)))*v 360=rhsPivot79 X Y Z W a b r := by
  have h:=hv 39
  change (((-1)*X*Y^2*W^2))*v 89 + ((1))*v 360=r 39 at h
  unfold rhsPivot79
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

#print axioms pivot_79

def rhsPivot80 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 41)/(((-1)*X*W^2))

compact_elimination_proof
theorem pivot_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 261 + ((((-1))/(X*W^2)))*v 450=rhsPivot80 X Y Z W a b r := by
  have h:=hv 41
  change (((-1)*X*W^2))*v 261 + ((1))*v 450=r 41 at h
  unfold rhsPivot80
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*W^2)))

def rhsPivot81 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 42)/((((-1)*W^2)/(X)))

compact_elimination_proof
theorem pivot_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 262 + ((((-1)*X)/(W^2)))*v 475=rhsPivot81 X Y Z W a b r := by
  have h:=hv 42
  change ((((-1)*W^2)/(X)))*v 262 + ((1))*v 475=r 42 at h
  unfold rhsPivot81
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X))))

def rhsPivot82 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 43 - ((1))*rhsPivot60 X Y Z W a b r)/(((-1)*X))

compact_elimination_proof
theorem pivot_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 265 + ((((-1))/(Y^2)))*v 435=rhsPivot82 X Y Z W a b r := by
  have h:=hv 43
  change (((-1)*X))*v 265 + ((1))*v 490=r 43 at h
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot82
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p60)*(1/(((-1)*X)))

def rhsPivot83 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 45 - ((1))*rhsPivot58 X Y Z W a b r)/((((-1)*X)/(W^2)))

compact_elimination_proof
theorem pivot_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)))*v 75 + ((1))*v 285=rhsPivot83 X Y Z W a b r := by
  have h:=hv 45
  change ((((-1)*X)/(W^2)))*v 285 + ((1))*v 498=r 45 at h
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot83
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p58)*(1/((((-1)*X)/(W^2))))

def rhsPivot84 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 46)/((1))

compact_elimination_proof
theorem pivot_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 310 + ((1))*v 499=rhsPivot84 X Y Z W a b r := by
  have h:=hv 46
  change ((((-1))/(X*W^2)))*v 310 + ((1))*v 499=r 46 at h
  unfold rhsPivot84
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot85 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 48)/((1))

compact_elimination_proof
theorem pivot_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 210 + ((1))*v 501=rhsPivot85 X Y Z W a b r := by
  have h:=hv 48
  change ((((-1))/(X*W^2)))*v 210 + ((1))*v 501=r 48 at h
  unfold rhsPivot85
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot86 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 49)/((1))

compact_elimination_proof
theorem pivot_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(W^2)))*v 235 + ((1))*v 502=rhsPivot86 X Y Z W a b r := by
  have h:=hv 49
  change ((((-1)*X)/(W^2)))*v 235 + ((1))*v 502=r 49 at h
  unfold rhsPivot86
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot87 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 52)/((((-1)*X*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)))*v 40 + ((1))*v 429=rhsPivot87 X Y Z W a b r := by
  have h:=hv 52
  change ((1))*v 40 + ((((-1)*X*W^2)/(Y^2)))*v 429=r 52 at h
  unfold rhsPivot87
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*W^2)/(Y^2))))

def rhsPivot88 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 53)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 45 + ((1))*v 430=rhsPivot88 X Y Z W a b r := by
  have h:=hv 53
  change ((1))*v 45 + ((((-1)*Y^2)/(X)))*v 430=r 53 at h
  unfold rhsPivot88
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2)/(X))))

def rhsPivot89 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 54)/((1))

compact_elimination_proof
theorem pivot_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 65 + ((((-1)*W^2)/(X*Y^2)))*v 438=rhsPivot89 X Y Z W a b r := by
  have h:=hv 54
  change ((1))*v 65 + ((((-1)*W^2)/(X*Y^2)))*v 438=r 54 at h
  unfold rhsPivot89
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot90 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 55)/((((-1)*X*Y^2)/(W^2)))

compact_elimination_proof
theorem pivot_90 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(X*Y^2)))*v 72 + ((1))*v 445=rhsPivot90 X Y Z W a b r := by
  have h:=hv 55
  change ((1))*v 72 + ((((-1)*X*Y^2)/(W^2)))*v 445=r 55 at h
  unfold rhsPivot90
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*Y^2)/(W^2))))

def rhsPivot91 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 56)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_91 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)*X))*v 75 + ((1))*v 450=rhsPivot91 X Y Z W a b r := by
  have h:=hv 56
  change ((1))*v 75 + ((((-1))/(X)))*v 450=r 56 at h
  unfold rhsPivot91
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1))/(X))))

def rhsPivot92 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 57)/((1))

compact_elimination_proof
theorem pivot_92 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 80 + ((((-1)*X)/(Y^2)))*v 465=rhsPivot92 X Y Z W a b r := by
  have h:=hv 57
  change ((1))*v 80 + ((((-1)*X)/(Y^2)))*v 465=r 57 at h
  unfold rhsPivot92
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot93 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 58 - ((1))*rhsPivot66 X Y Z W a b r)/((((-1)*Y^2)/(X*W^2)))

compact_elimination_proof
theorem pivot_93 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(Y^2)))*v 24 + ((1))*v 470=rhsPivot93 X Y Z W a b r := by
  have h:=hv 58
  change ((1))*v 81 + ((((-1)*Y^2)/(X*W^2)))*v 470=r 58 at h
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot93
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p66)*(1/((((-1)*Y^2)/(X*W^2))))

def rhsPivot94 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 61)/((1))

compact_elimination_proof
theorem pivot_94 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 92 + ((((-1)*X)/(Y^2*W^2)))*v 195=rhsPivot94 X Y Z W a b r := by
  have h:=hv 61
  change ((1))*v 92 + ((((-1)*X)/(Y^2*W^2)))*v 195=r 61 at h
  unfold rhsPivot94
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot95 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 63)/((1))

compact_elimination_proof
theorem pivot_95 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 95 + ((((-1))/(X*Y^2)))*v 330=rhsPivot95 X Y Z W a b r := by
  have h:=hv 63
  change ((1))*v 95 + ((((-1))/(X*Y^2)))*v 330=r 63 at h
  unfold rhsPivot95
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_95

def rhsPivot96 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 64)/((1))

compact_elimination_proof
theorem pivot_96 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 96 + ((((-1)*X)/(W^2)))*v 345=rhsPivot96 X Y Z W a b r := by
  have h:=hv 64
  change ((1))*v 96 + ((((-1)*X)/(W^2)))*v 345=r 64 at h
  unfold rhsPivot96
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot97 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 65)/((1))

compact_elimination_proof
theorem pivot_97 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 99 + ((((-1)*Y^2)/(X*W^2)))*v 370=rhsPivot97 X Y Z W a b r := by
  have h:=hv 65
  change ((1))*v 99 + ((((-1)*Y^2)/(X*W^2)))*v 370=r 65 at h
  unfold rhsPivot97
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot98 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 66)/((1))

compact_elimination_proof
theorem pivot_98 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 100 + ((((-1)*X)/(Y^2)))*v 375=rhsPivot98 X Y Z W a b r := by
  have h:=hv 66
  change ((1))*v 100 + ((((-1)*X)/(Y^2)))*v 375=r 66 at h
  unfold rhsPivot98
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot99 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 67)/((1))

compact_elimination_proof
theorem pivot_99 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 105 + ((((-1))/(X)))*v 390=rhsPivot99 X Y Z W a b r := by
  have h:=hv 67
  change ((1))*v 105 + ((((-1))/(X)))*v 390=r 67 at h
  unfold rhsPivot99
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot100 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 68)/((((-1)*X*Y^2)/(W^2)))

compact_elimination_proof
theorem pivot_100 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(X*Y^2)))*v 108 + ((1))*v 395=rhsPivot100 X Y Z W a b r := by
  have h:=hv 68
  change ((1))*v 108 + ((((-1)*X*Y^2)/(W^2)))*v 395=r 68 at h
  unfold rhsPivot100
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*Y^2)/(W^2))))

def rhsPivot101 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 69)/((1))

compact_elimination_proof
theorem pivot_101 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 115 + ((((-1)*W^2)/(X*Y^2)))*v 402=rhsPivot101 X Y Z W a b r := by
  have h:=hv 69
  change ((1))*v 115 + ((((-1)*W^2)/(X*Y^2)))*v 402=r 69 at h
  unfold rhsPivot101
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot102 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 70)/(((-1)*X))

compact_elimination_proof
theorem pivot_102 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 120 + ((1))*v 405=rhsPivot102 X Y Z W a b r := by
  have h:=hv 70
  change ((1))*v 120 + (((-1)*X))*v 405=r 70 at h
  unfold rhsPivot102
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X)))

def rhsPivot103 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 71)/((((-1)*X*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_103 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)))*v 140 + ((1))*v 411=rhsPivot103 X Y Z W a b r := by
  have h:=hv 71
  change ((1))*v 140 + ((((-1)*X*W^2)/(Y^2)))*v 411=r 71 at h
  unfold rhsPivot103
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*W^2)/(Y^2))))

def rhsPivot104 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 72)/((((-1)*W^2)/(X)))

compact_elimination_proof
theorem pivot_104 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(W^2)))*v 165 + ((1))*v 414=rhsPivot104 X Y Z W a b r := by
  have h:=hv 72
  change ((1))*v 165 + ((((-1)*W^2)/(X)))*v 414=r 72 at h
  unfold rhsPivot104
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X))))

def rhsPivot105 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 73)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_105 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2)))*v 180 + ((1))*v 415=rhsPivot105 X Y Z W a b r := by
  have h:=hv 73
  change ((1))*v 180 + (((-1)*X*Y^2))*v 415=r 73 at h
  unfold rhsPivot105
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2)))

def rhsPivot106 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 75)/((((-1)*Y^2*W^2)/(X)))

compact_elimination_proof
theorem pivot_106 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2*W^2)))*v 315 + ((1))*v 418=rhsPivot106 X Y Z W a b r := by
  have h:=hv 75
  change ((1))*v 315 + ((((-1)*Y^2*W^2)/(X)))*v 418=r 75 at h
  unfold rhsPivot106
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2*W^2)/(X))))

def rhsPivot107 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 77)/((1))

compact_elimination_proof
theorem pivot_107 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2*W^2)))*v 150 + ((1))*v 421=rhsPivot107 X Y Z W a b r := by
  have h:=hv 77
  change ((((-1))/(X*Y^2*W^2)))*v 150 + ((1))*v 421=r 77 at h
  unfold rhsPivot107
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot108 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 78)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_108 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2*W^2)))*v 210 + ((1))*v 424=rhsPivot108 X Y Z W a b r := by
  have h:=hv 78
  change ((1))*v 210 + (((-1)*Y^2*W^2))*v 424=r 78 at h
  unfold rhsPivot108
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

def rhsPivot109 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 80 - ((((-1)*Y^2)/(W^2)))*rhsPivot88 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_109 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(W^2)))*v 45 + ((1))*v 264=rhsPivot109 X Y Z W a b r := by
  have h:=hv 80
  change ((1))*v 264 + ((((-1)*Y^2)/(W^2)))*v 430=r 80 at h
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot109
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(W^2)))*p88)*(1/((1)))

def rhsPivot110 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 82 - ((((-1))/(W^2)))*rhsPivot102 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_110 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 120 + ((1))*v 267=rhsPivot110 X Y Z W a b r := by
  have h:=hv 82
  change ((1))*v 267 + ((((-1))/(W^2)))*v 405=r 82 at h
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot110
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(W^2)))*p102)*(1/((1)))

def rhsPivot111 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 83 - (((-1)*W^2))*rhsPivot79 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_111 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2)))*v 360 + ((1))*v 475=rhsPivot111 X Y Z W a b r := by
  have h:=hv 83
  change (((-1)*W^2))*v 89 + ((1))*v 475=r 83 at h
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot111
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*W^2))*p79)*(1/((1)))

#print axioms pivot_111

def rhsPivot112 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 84 - ((((-1))/(W^2)))*rhsPivot95 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_112 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2*W^2)))*v 330 + ((1))*v 481=rhsPivot112 X Y Z W a b r := by
  have h:=hv 84
  change ((((-1))/(W^2)))*v 95 + ((1))*v 481=r 84 at h
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot112
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(W^2)))*p95)*(1/((1)))

def rhsPivot113 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 85 - (((1*X*Y^2*Z)/(W^2)))*rhsPivot82 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_113 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 102 + (((1*X*Z)/(W^2)))*v 435=rhsPivot113 X Y Z W a b r := by
  have h:=hv 85
  change ((1))*v 102 + (((1*X*Y^2*Z)/(W^2)))*v 265=r 85 at h
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot113
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X*Y^2*Z)/(W^2)))*p82)*(1/((1)))

def rhsPivot114 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 86 - (((-1)*X))*rhsPivot110 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_114 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)))*v 120 + ((1))*v 276=rhsPivot114 X Y Z W a b r := by
  have h:=hv 86
  change (((-1)*X))*v 267 + ((1))*v 276=r 86 at h
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot114
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X))*p110)*(1/((1)))

def rhsPivot115 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 87 - ((((-1))/(X)))*rhsPivot73 X Y Z W a b r - ((1))*rhsPivot75 X Y Z W a b r)/(((1)/(X*Y^2)))

compact_elimination_proof
theorem pivot_115 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(W^2)))*v 40 + ((1))*v 486=rhsPivot115 X Y Z W a b r := by
  have h:=hv 87
  change ((((-1))/(X)))*v 268 + ((1))*v 277=r 87 at h
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v r hv
  have p75:=pivot_75 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot115
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p73 - ((1))*p75)*(1/(((1)/(X*Y^2))))

def rhsPivot116 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 89 - ((((-1))/(X)))*rhsPivot109 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_116 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)))*v 45 + ((1))*v 279=rhsPivot116 X Y Z W a b r := by
  have h:=hv 89
  change ((((-1))/(X)))*v 264 + ((1))*v 279=r 89 at h
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot116
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X)))*p109)*(1/((1)))

def rhsPivot117 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 90 - ((1*Z*W^2))*rhsPivot59 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_117 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 170 + (((1*X*Z)/(Y^2)))*v 465=rhsPivot117 X Y Z W a b r := by
  have h:=hv 90
  change ((1*Z*W^2))*v 86 + ((1))*v 170=r 90 at h
  have p59:=pivot_59 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot117
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1*Z*W^2))*p59)*(1/((1)))

def rhsPivot118 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 91 - ((1*Z))*rhsPivot88 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_118 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X*Z)/(Y^2)))*v 45 + ((1))*v 340=rhsPivot118 X Y Z W a b r := by
  have h:=hv 91
  change ((1))*v 340 + ((1*Z))*v 430=r 91 at h
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot118
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1*Z))*p88)*(1/((1)))

def rhsPivot119 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 92)/(((1*W^2)/(Z)))

compact_elimination_proof
theorem pivot_119 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Z)/(W^2)))*v 400 + ((1))*v 442=rhsPivot119 X Y Z W a b r := by
  have h:=hv 92
  change ((1))*v 400 + (((1*W^2)/(Z)))*v 442=r 92 at h
  unfold rhsPivot119
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*W^2)/(Z))))

def rhsPivot120 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 93 - (((1*Z)/(W^2)))*rhsPivot91 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_120 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X*Z)/(W^2)))*v 75 + ((1))*v 408=rhsPivot120 X Y Z W a b r := by
  have h:=hv 93
  change ((1))*v 408 + (((1*Z)/(W^2)))*v 450=r 93 at h
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot120
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(W^2)))*p91)*(1/((1)))

def rhsPivot121 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 94 - ((1))*rhsPivot108 X Y Z W a b r - (((1)/(Z*W^2)))*rhsPivot118 X Y Z W a b r)/(((1)/(Y^2*W^2)))

compact_elimination_proof
theorem pivot_121 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)*X))*v 45 + ((1))*v 210=rhsPivot121 X Y Z W a b r := by
  have h:=hv 94
  change (((1)/(Z*W^2)))*v 340 + ((1))*v 424=r 94 at h
  have p108:=pivot_108 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot121
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p108 - (((1)/(Z*W^2)))*p118)*(1/(((1)/(Y^2*W^2))))

def rhsPivot122 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 96)/((1))

compact_elimination_proof
theorem pivot_122 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 427 + ((((-1))/(X*Y^2)))*v 474=rhsPivot122 X Y Z W a b r := by
  have h:=hv 96
  change ((1))*v 427 + ((((-1))/(X*Y^2)))*v 474=r 96 at h
  unfold rhsPivot122
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot123 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 97 - ((((-1)*X)/(Y^2)))*rhsPivot74 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot114 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_123 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2*W^2)))*v 120 + ((1))*v 428=rhsPivot123 X Y Z W a b r := by
  have h:=hv 97
  change ((1))*v 428 + ((((-1)*X)/(Y^2)))*v 483=r 97 at h
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot123
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2)))*p74 - ((((-1))/(Y^2)))*p114)*(1/((1)))

def rhsPivot124 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 98)/((1))

compact_elimination_proof
theorem pivot_124 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 432 + (((-1)*X))*v 489=rhsPivot124 X Y Z W a b r := by
  have h:=hv 98
  change ((1))*v 432 + (((-1)*X))*v 489=r 98 at h
  unfold rhsPivot124
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot125 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 99)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_125 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2)))*v 444 + ((1))*v 491=rhsPivot125 X Y Z W a b r := by
  have h:=hv 99
  change ((1))*v 444 + (((-1)*X*Y^2))*v 491=r 99 at h
  unfold rhsPivot125
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2)))

def rhsPivot126 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 102 - ((1))*rhsPivot66 X Y Z W a b r - ((((-1)*Y^2)/(X)))*rhsPivot106 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_126 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 24 + ((((-1)*X)/(W^2)))*v 315=rhsPivot126 X Y Z W a b r := by
  have h:=hv 102
  change ((1))*v 81 + ((((-1)*Y^2)/(X)))*v 418=r 102 at h
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v r hv
  have p106:=pivot_106 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot126
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p66 - ((((-1)*Y^2)/(X)))*p106)*(1/(((1)/(X))))

def rhsPivot127 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 103 - ((1))*rhsPivot68 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot104 X Y Z W a b r)/(((1)/(X*Y^2)))

compact_elimination_proof
theorem pivot_127 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 36 + ((((-1)*X)/(W^2)))*v 165=rhsPivot127 X Y Z W a b r := by
  have h:=hv 103
  change ((1))*v 83 + ((((-1))/(X*Y^2)))*v 414=r 103 at h
  have p68:=pivot_68 X Y Z W a b hX hY hZ hW v r hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot127
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p68 - ((((-1))/(X*Y^2)))*p104)*(1/(((1)/(X*Y^2))))

#print axioms pivot_127

def rhsPivot128 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 106 - (((1*Z)/(W^2)))*rhsPivot60 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_128 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X*Z)/(Y^2*W^2)))*v 435 + ((1))*v 476=rhsPivot128 X Y Z W a b r := by
  have h:=hv 106
  change ((1))*v 476 + (((1*Z)/(W^2)))*v 490=r 106 at h
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot128
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(W^2)))*p60)*(1/((1)))

def rhsPivot129 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 107)/((1*Y^2*Z))

compact_elimination_proof
theorem pivot_129 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 13 + (((1)/(Y^2*Z)))*v 51=rhsPivot129 X Y Z W a b r := by
  have h:=hv 107
  change ((1*Y^2*Z))*v 13 + ((1))*v 51=r 107 at h
  unfold rhsPivot129
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1*Y^2*Z)))

def rhsPivot130 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 108 - ((1))*rhsPivot79 X Y Z W a b r)/(((1)/(Y^2*Z)))

compact_elimination_proof
theorem pivot_130 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 51 + (((1*Z)/(X*W^2)))*v 360=rhsPivot130 X Y Z W a b r := by
  have h:=hv 108
  change (((1)/(Y^2*Z)))*v 51 + ((1))*v 89=r 108 at h
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot130
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p79)*(1/(((1)/(Y^2*Z))))

def rhsPivot131 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 109 - ((((-1)*Y^2*W^2)/(X)))*rhsPivot73 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_131 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X)))*v 40 + ((1))*v 195=rhsPivot131 X Y Z W a b r := by
  have h:=hv 109
  change ((1))*v 195 + ((((-1)*Y^2*W^2)/(X)))*v 268=r 109 at h
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot131
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2*W^2)/(X)))*p73)*(1/((1)))

def rhsPivot132 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 116)/((1))

compact_elimination_proof
theorem pivot_132 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 25 + (((1*W^2)/(X*Y^2*Z)))*v 204=rhsPivot132 X Y Z W a b r := by
  have h:=hv 116
  change ((1))*v 25 + (((1*W^2)/(X*Y^2*Z)))*v 204=r 116 at h
  unfold rhsPivot132
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot133 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 117 - (((1*X*Z)/(Y^2*W^2)))*rhsPivot83 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_133 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 34 + (((1*X*Z)/(Y^2*W^2)))*v 75=rhsPivot133 X Y Z W a b r := by
  have h:=hv 117
  change ((1))*v 34 + (((1*X*Z)/(Y^2*W^2)))*v 285=r 117 at h
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot133
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X*Z)/(Y^2*W^2)))*p83)*(1/((1)))

def rhsPivot134 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 118)/((1))

compact_elimination_proof
theorem pivot_134 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 50 + (((1*X*W^2)/(Y^2*Z)))*v 357=rhsPivot134 X Y Z W a b r := by
  have h:=hv 118
  change ((1))*v 50 + (((1*X*W^2)/(Y^2*Z)))*v 357=r 118 at h
  unfold rhsPivot134
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot135 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 119)/(((1*X*W^2)/(Z)))

compact_elimination_proof
theorem pivot_135 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Z)/(X*W^2)))*v 150 + ((1))*v 459=rhsPivot135 X Y Z W a b r := by
  have h:=hv 119
  change ((1))*v 150 + (((1*X*W^2)/(Z)))*v 459=r 119 at h
  unfold rhsPivot135
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*W^2)/(Z))))

def rhsPivot136 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 120)/(((1*Y^2*Z)/(X*W^2)))

compact_elimination_proof
theorem pivot_136 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X*W^2)/(Y^2*Z)))*v 153 + ((1))*v 460=rhsPivot136 X Y Z W a b r := by
  have h:=hv 120
  change ((1))*v 153 + (((1*Y^2*Z)/(X*W^2)))*v 460=r 120 at h
  unfold rhsPivot136
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*Y^2*Z)/(X*W^2))))

def rhsPivot137 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 121 - (((1*Y^2*W^2)/(X*Z)))*rhsPivot128 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_137 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 225 + (((-1)))*v 435=rhsPivot137 X Y Z W a b r := by
  have h:=hv 121
  change ((1))*v 225 + (((1*Y^2*W^2)/(X*Z)))*v 476=r 121 at h
  have p128:=pivot_128 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot137
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Y^2*W^2)/(X*Z)))*p128)*(1/((1)))

def rhsPivot138 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 122)/(((1*X*Y^2*Z)/(W^2)))

compact_elimination_proof
theorem pivot_138 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*W^2)/(X*Y^2*Z)))*v 306 + ((1))*v 485=rhsPivot138 X Y Z W a b r := by
  have h:=hv 122
  change ((1))*v 306 + (((1*X*Y^2*Z)/(W^2)))*v 485=r 122 at h
  unfold rhsPivot138
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((1*X*Y^2*Z)/(W^2))))

def rhsPivot139 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 124 - ((((-1))/(Y^2*W^2)))*rhsPivot99 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_139 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 7 + ((((-1))/(X*Y^2*W^2)))*v 390=rhsPivot139 X Y Z W a b r := by
  have h:=hv 124
  change ((1))*v 7 + ((((-1))/(Y^2*W^2)))*v 105=r 124 at h
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot139
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(Y^2*W^2)))*p99)*(1/((1)))

def rhsPivot140 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 125)/((1))

compact_elimination_proof
theorem pivot_140 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 8 + ((((-1))/(Y^2*W^2)))*v 390=rhsPivot140 X Y Z W a b r := by
  have h:=hv 125
  change ((1))*v 8 + ((((-1))/(Y^2*W^2)))*v 390=r 125 at h
  unfold rhsPivot140
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot141 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 126 - (((-1)*Y^2*W^2))*rhsPivot86 X Y Z W a b r)/(((-1)*X*Y^2))

compact_elimination_proof
theorem pivot_141 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2)))*v 120 + ((1))*v 235=rhsPivot141 X Y Z W a b r := by
  have h:=hv 126
  change ((1))*v 120 + (((-1)*Y^2*W^2))*v 502=r 126 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot141
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*Y^2*W^2))*p86)*(1/(((-1)*X*Y^2)))

def rhsPivot142 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 128 - (((1*W^2)/(Y^2*Z)))*rhsPivot135 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_142 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 35 + ((((-1))/(X*Y^2)))*v 150=rhsPivot142 X Y Z W a b r := by
  have h:=hv 128
  change ((1))*v 35 + (((1*W^2)/(Y^2*Z)))*v 459=r 128 at h
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot142
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(Y^2*Z)))*p135)*(1/((1)))

def rhsPivot143 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 130 - (((-1)*X*Y^2))*rhsPivot138 X Y Z W a b r)/(((1*W^2)/(Z)))

compact_elimination_proof
theorem pivot_143 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Z)/(W^2)))*v 180 + ((1))*v 306=rhsPivot143 X Y Z W a b r := by
  have h:=hv 130
  change ((1))*v 180 + (((-1)*X*Y^2))*v 485=r 130 at h
  have p138:=pivot_138 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot143
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*Y^2))*p138)*(1/(((1*W^2)/(Z))))

#print axioms pivot_143

def rhsPivot144 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 131)/((1))

compact_elimination_proof
theorem pivot_144 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 220 + ((((-1)*X*W^2)/(Y^2)))*v 489=rhsPivot144 X Y Z W a b r := by
  have h:=hv 131
  change ((1))*v 220 + ((((-1)*X*W^2)/(Y^2)))*v 489=r 131 at h
  unfold rhsPivot144
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot145 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 132 - ((((-1)*W^2)/(X*Y^2)))*rhsPivot58 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_145 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2)))*v 75 + ((1))*v 245=rhsPivot145 X Y Z W a b r := by
  have h:=hv 132
  change ((1))*v 245 + ((((-1)*W^2)/(X*Y^2)))*v 498=r 132 at h
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot145
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*W^2)/(X*Y^2)))*p58)*(1/((1)))

def rhsPivot146 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 134)/((1))

compact_elimination_proof
theorem pivot_146 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 273 + ((((-1))/(X*W^2)))*v 330=rhsPivot146 X Y Z W a b r := by
  have h:=hv 134
  change ((1))*v 273 + ((((-1))/(X*W^2)))*v 330=r 134 at h
  unfold rhsPivot146
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot147 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 135)/((1))

compact_elimination_proof
theorem pivot_147 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 275 + ((((-1))/(X*Y^2)))*v 390=rhsPivot147 X Y Z W a b r := by
  have h:=hv 135
  change ((1))*v 275 + ((((-1))/(X*Y^2)))*v 390=r 135 at h
  unfold rhsPivot147
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot148 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 136)/((((-1)*X*Y^2)/(W^2)))

compact_elimination_proof
theorem pivot_148 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(X*Y^2)))*v 288 + ((1))*v 455=rhsPivot148 X Y Z W a b r := by
  have h:=hv 136
  change ((1))*v 288 + ((((-1)*X*Y^2)/(W^2)))*v 455=r 136 at h
  unfold rhsPivot148
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*Y^2)/(W^2))))

def rhsPivot149 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 137)/((1))

compact_elimination_proof
theorem pivot_149 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 295 + ((((-1)*W^2)/(X*Y^2)))*v 462=rhsPivot149 X Y Z W a b r := by
  have h:=hv 137
  change ((1))*v 295 + ((((-1)*W^2)/(X*Y^2)))*v 462=r 137 at h
  unfold rhsPivot149
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot150 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 138)/((1))

compact_elimination_proof
theorem pivot_150 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 300 + (((-1)*X))*v 465=rhsPivot150 X Y Z W a b r := by
  have h:=hv 138
  change ((1))*v 300 + (((-1)*X))*v 465=r 138 at h
  unfold rhsPivot150
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot151 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 139)/((((-1)*X*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_151 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)))*v 320 + ((1))*v 471=rhsPivot151 X Y Z W a b r := by
  have h:=hv 139
  change ((1))*v 320 + ((((-1)*X*W^2)/(Y^2)))*v 471=r 139 at h
  unfold rhsPivot151
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*W^2)/(Y^2))))

def rhsPivot152 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 140)/((((-1)*W^2)/(X)))

compact_elimination_proof
theorem pivot_152 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(W^2)))*v 345 + ((1))*v 474=rhsPivot152 X Y Z W a b r := by
  have h:=hv 140
  change ((1))*v 345 + ((((-1)*W^2)/(X)))*v 474=r 140 at h
  unfold rhsPivot152
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(X))))

def rhsPivot153 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 141)/((((-1)*X*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_153 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 39 + ((((-1)*Y^2)/(X*W^2)))*v 190=rhsPivot153 X Y Z W a b r := by
  have h:=hv 141
  change ((((-1)*X*W^2)/(Y^2)))*v 39 + ((1))*v 190=r 141 at h
  unfold rhsPivot153
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*W^2)/(Y^2))))

def rhsPivot154 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 142)/((1))

compact_elimination_proof
theorem pivot_154 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(X*Y^2)))*v 48 + ((1))*v 215=rhsPivot154 X Y Z W a b r := by
  have h:=hv 142
  change ((((-1)*W^2)/(X*Y^2)))*v 48 + ((1))*v 215=r 142 at h
  unfold rhsPivot154
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot155 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 143)/((((-1)*X*Y^2)/(W^2)))

compact_elimination_proof
theorem pivot_155 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 55 + ((((-1)*W^2)/(X*Y^2)))*v 222=rhsPivot155 X Y Z W a b r := by
  have h:=hv 143
  change ((((-1)*X*Y^2)/(W^2)))*v 55 + ((1))*v 222=r 143 at h
  unfold rhsPivot155
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*X*Y^2)/(W^2))))

def rhsPivot156 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 144)/((1))

compact_elimination_proof
theorem pivot_156 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2)))*v 75 + ((1))*v 230=rhsPivot156 X Y Z W a b r := by
  have h:=hv 144
  change ((((-1)*X)/(Y^2)))*v 75 + ((1))*v 230=r 144 at h
  unfold rhsPivot156
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot157 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 145 - ((((-1)*Y^2)/(X*W^2)))*rhsPivot92 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_157 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 231 + ((((-1))/(W^2)))*v 465=rhsPivot157 X Y Z W a b r := by
  have h:=hv 145
  change ((((-1)*Y^2)/(X*W^2)))*v 80 + ((1))*v 231=r 145 at h
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot157
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X*W^2)))*p92)*(1/((1)))

def rhsPivot158 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 146 - ((((-1)*X)/(W^2)))*rhsPivot99 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_158 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 234 + ((((-1))/(W^2)))*v 390=rhsPivot158 X Y Z W a b r := by
  have h:=hv 146
  change ((((-1)*X)/(W^2)))*v 105 + ((1))*v 234=r 146 at h
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot158
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(W^2)))*p99)*(1/((1)))

def rhsPivot159 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 147)/((1))

compact_elimination_proof
theorem pivot_159 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 180 + ((1))*v 237=rhsPivot159 X Y Z W a b r := by
  have h:=hv 147
  change ((((-1))/(X*W^2)))*v 180 + ((1))*v 237=r 147 at h
  unfold rhsPivot159
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_159

def rhsPivot160 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 151)/((1))

compact_elimination_proof
theorem pivot_160 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 242 + ((((-1)*X)/(Y^2*W^2)))*v 315=rhsPivot160 X Y Z W a b r := by
  have h:=hv 151
  change ((1))*v 242 + ((((-1)*X)/(Y^2*W^2)))*v 315=r 151 at h
  unfold rhsPivot160
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot161 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 152)/((1))

compact_elimination_proof
theorem pivot_161 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 243 + ((((-1))/(X*W^2)))*v 390=rhsPivot161 X Y Z W a b r := by
  have h:=hv 152
  change ((1))*v 243 + ((((-1))/(X*W^2)))*v 390=r 152 at h
  unfold rhsPivot161
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot162 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 153)/((1))

compact_elimination_proof
theorem pivot_162 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 246 + ((((-1)*X)/(W^2)))*v 465=rhsPivot162 X Y Z W a b r := by
  have h:=hv 153
  change ((1))*v 246 + ((((-1)*X)/(W^2)))*v 465=r 153 at h
  unfold rhsPivot162
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot163 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 154 - ((((-1)*Y^2)/(X*W^2)))*rhsPivot60 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_163 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 249 + ((((-1))/(W^2)))*v 435=rhsPivot163 X Y Z W a b r := by
  have h:=hv 154
  change ((1))*v 249 + ((((-1)*Y^2)/(X*W^2)))*v 490=r 154 at h
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot163
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X*W^2)))*p60)*(1/((1)))

def rhsPivot164 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 157 - ((((-1)*X*W^2)/(Y^2)))*rhsPivot65 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_164 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(Y^2)))*v 78 + ((1))*v 290=rhsPivot164 X Y Z W a b r := by
  have h:=hv 157
  change ((((-1)*X*W^2)/(Y^2)))*v 21 + ((1))*v 290=r 157 at h
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot164
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X*W^2)/(Y^2)))*p65)*(1/((1)))

def rhsPivot165 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 158 - (((-1)*X*Y^2))*rhsPivot132 X Y Z W a b r)/(((1*W^2)/(Z)))

compact_elimination_proof
theorem pivot_165 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 204 + (((1*Z)/(W^2)))*v 330=rhsPivot165 X Y Z W a b r := by
  have h:=hv 158
  change (((-1)*X*Y^2))*v 25 + ((1))*v 330=r 158 at h
  have p132:=pivot_132 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot165
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((-1)*X*Y^2))*p132)*(1/(((1*W^2)/(Z))))

def rhsPivot166 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 159)/(((-1)*X*W^2))

compact_elimination_proof
theorem pivot_166 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 27 + ((((-1))/(X*W^2)))*v 390=rhsPivot166 X Y Z W a b r := by
  have h:=hv 159
  change (((-1)*X*W^2))*v 27 + ((1))*v 390=r 159 at h
  unfold rhsPivot166
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*W^2)))

def rhsPivot167 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 160)/((((-1)*Y^2*W^2)/(X)))

compact_elimination_proof
theorem pivot_167 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 28 + ((((-1)*X)/(Y^2*W^2)))*v 465=rhsPivot167 X Y Z W a b r := by
  have h:=hv 160
  change ((((-1)*Y^2*W^2)/(X)))*v 28 + ((1))*v 465=r 160 at h
  unfold rhsPivot167
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*Y^2*W^2)/(X))))

def rhsPivot168 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 161)/(((-1)*X))

compact_elimination_proof
theorem pivot_168 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 14 + ((1))*v 479=rhsPivot168 X Y Z W a b r := by
  have h:=hv 161
  change ((1))*v 14 + (((-1)*X))*v 479=r 161 at h
  unfold rhsPivot168
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X)))

def rhsPivot169 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 162)/((1))

compact_elimination_proof
theorem pivot_169 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 68 + (((1*Z)/(W^2)))*v 110=rhsPivot169 X Y Z W a b r := by
  have h:=hv 162
  change ((1))*v 68 + (((1*Z)/(W^2)))*v 110=r 162 at h
  unfold rhsPivot169
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot170 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 163)/((((-1)*W^2)/(Y^2)))

compact_elimination_proof
theorem pivot_170 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(W^2)))*v 70 + ((1))*v 282=rhsPivot170 X Y Z W a b r := by
  have h:=hv 163
  change ((1))*v 70 + ((((-1)*W^2)/(Y^2)))*v 282=r 163 at h
  unfold rhsPivot170
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((((-1)*W^2)/(Y^2))))

def rhsPivot171 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 164 - ((((-1))/(X*Y^2*W^2)))*rhsPivot121 X Y Z W a b r - ((1))*rhsPivot168 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_171 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 14 + ((((-1)*X)/(Y^2*W^2)))*v 45=rhsPivot171 X Y Z W a b r := by
  have h:=hv 164
  change ((((-1))/(X*Y^2*W^2)))*v 210 + ((1))*v 479=r 164 at h
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p168:=pivot_168 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot171
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p121 - ((1))*p168)*(1/(((1)/(X))))

def rhsPivot172 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 165)/((1))

compact_elimination_proof
theorem pivot_172 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 29 + ((((-1))/(X*Y^2*W^2)))*v 180=rhsPivot172 X Y Z W a b r := by
  have h:=hv 165
  change ((1))*v 29 + ((((-1))/(X*Y^2*W^2)))*v 180=r 165 at h
  unfold rhsPivot172
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot173 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 166 - ((((-1))/(X*Y^2*W^2)))*rhsPivot150 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_173 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 31 + ((((-1))/(Y^2*W^2)))*v 465=rhsPivot173 X Y Z W a b r := by
  have h:=hv 166
  change ((1))*v 31 + ((((-1))/(X*Y^2*W^2)))*v 300=r 166 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot173
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2*W^2)))*p150)*(1/((1)))

def rhsPivot174 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 167)/((1))

compact_elimination_proof
theorem pivot_174 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 40 + ((1))*v 259=rhsPivot174 X Y Z W a b r := by
  have h:=hv 167
  change ((((-1))/(X*W^2)))*v 40 + ((1))*v 259=r 167 at h
  unfold rhsPivot174
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot175 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 168)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_175 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2*W^2)))*v 135 + ((1))*v 263=rhsPivot175 X Y Z W a b r := by
  have h:=hv 168
  change ((1))*v 135 + (((-1)*Y^2*W^2))*v 263=r 168 at h
  unfold rhsPivot175
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2*W^2)))

#print axioms pivot_175

def rhsPivot176 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 169)/((1))

compact_elimination_proof
theorem pivot_176 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 247 + ((((-1))/(Y^2*W^2)))*v 375=rhsPivot176 X Y Z W a b r := by
  have h:=hv 169
  change ((1))*v 247 + ((((-1))/(Y^2*W^2)))*v 375=r 169 at h
  unfold rhsPivot176
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot177 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 170)/((1))

compact_elimination_proof
theorem pivot_177 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2*W^2)))*v 150 + ((1))*v 248=rhsPivot177 X Y Z W a b r := by
  have h:=hv 170
  change ((((-1))/(Y^2*W^2)))*v 150 + ((1))*v 248=r 170 at h
  unfold rhsPivot177
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot178 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 171 - ((1))*rhsPivot150 X Y Z W a b r)/(((-1)*Y^2*W^2))

compact_elimination_proof
theorem pivot_178 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2*W^2)))*v 465 + ((1))*v 496=rhsPivot178 X Y Z W a b r := by
  have h:=hv 171
  change ((1))*v 300 + (((-1)*Y^2*W^2))*v 496=r 171 at h
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot178
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p150)*(1/(((-1)*Y^2*W^2)))

def rhsPivot179 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 173)/(((-1)*X*Y^2*W^2))

compact_elimination_proof
theorem pivot_179 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*Y^2*W^2)))*v 120 + ((1))*v 503=rhsPivot179 X Y Z W a b r := by
  have h:=hv 173
  change ((1))*v 120 + (((-1)*X*Y^2*W^2))*v 503=r 173 at h
  unfold rhsPivot179
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*X*Y^2*W^2)))

def rhsPivot180 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 174)/((1))

compact_elimination_proof
theorem pivot_180 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 228 + ((((-1)*Y^2)/(W^2)))*v 440=rhsPivot180 X Y Z W a b r := by
  have h:=hv 174
  change ((1))*v 228 + ((((-1)*Y^2)/(W^2)))*v 440=r 174 at h
  unfold rhsPivot180
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot181 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 175)/((1))

compact_elimination_proof
theorem pivot_181 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 233 + ((((-1))/(Y^2*W^2)))*v 315=rhsPivot181 X Y Z W a b r := by
  have h:=hv 175
  change ((1))*v 233 + ((((-1))/(Y^2*W^2)))*v 315=r 175 at h
  unfold rhsPivot181
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot182 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 177)/((1))

compact_elimination_proof
theorem pivot_182 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 94 + ((((-1))/(Y^2)))*v 468=rhsPivot182 X Y Z W a b r := by
  have h:=hv 177
  change ((1))*v 94 + ((((-1))/(Y^2)))*v 468=r 177 at h
  unfold rhsPivot182
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot183 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 178)/((1))

compact_elimination_proof
theorem pivot_183 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 11 + ((((-1))/(X*W^2)))*v 200=rhsPivot183 X Y Z W a b r := by
  have h:=hv 178
  change ((1))*v 11 + ((((-1))/(X*W^2)))*v 200=r 178 at h
  unfold rhsPivot183
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot184 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 182 - ((1))*rhsPivot163 X Y Z W a b r)/((((-1)*Y^2)/(X)))

compact_elimination_proof
theorem pivot_184 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X)/(Y^2*W^2)))*v 435 + ((1))*v 506=rhsPivot184 X Y Z W a b r := by
  have h:=hv 182
  change ((1))*v 249 + ((((-1)*Y^2)/(X)))*v 506=r 182 at h
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot184
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p163)*(1/((((-1)*Y^2)/(X))))

def rhsPivot185 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 183 - ((((-1))/(X*Y^2)))*rhsPivot70 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_185 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 257 + ((((-1))/(Y^2*W^2)))*v 435=rhsPivot185 X Y Z W a b r := by
  have h:=hv 183
  change ((((-1))/(X*Y^2)))*v 12 + ((1))*v 257=r 183 at h
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot185
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2)))*p70)*(1/((1)))

def rhsPivot186 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 186 - ((((-1))/(X*W^2)))*rhsPivot93 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot126 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_186 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 251 + ((((-1))/(Y^2*W^2)))*v 315=rhsPivot186 X Y Z W a b r := by
  have h:=hv 186
  change ((1))*v 251 + ((((-1))/(X*W^2)))*v 470=r 186 at h
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot186
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p93 - ((((-1))/(X*Y^2)))*p126)*(1/((1)))

def rhsPivot187 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 187 - ((((-1))/(W^2)))*rhsPivot64 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_187 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 4 + ((((-1)*X)/(Y^2*W^2)))*v 75=rhsPivot187 X Y Z W a b r := by
  have h:=hv 187
  change ((1))*v 4 + ((((-1))/(W^2)))*v 20=r 187 at h
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot187
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(W^2)))*p64)*(1/((1)))

def rhsPivot188 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 188)/(((-1)*Y^2))

compact_elimination_proof
theorem pivot_188 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2)))*v 42 + ((1))*v 416=rhsPivot188 X Y Z W a b r := by
  have h:=hv 188
  change ((1))*v 42 + (((-1)*Y^2))*v 416=r 188 at h
  unfold rhsPivot188
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/(((-1)*Y^2)))

def rhsPivot189 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 189 - ((1))*rhsPivot117 X Y Z W a b r - ((1))*rhsPivot118 X Y Z W a b r)/((((-1)*X*Z)/(Y^2)))

compact_elimination_proof
theorem pivot_189 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 45 + ((1))*v 465=rhsPivot189 X Y Z W a b r := by
  have h:=hv 189
  change ((1))*v 170 + ((1))*v 340=r 189 at h
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot189
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p117 - ((1))*p118)*(1/((((-1)*X*Z)/(Y^2))))

def rhsPivot190 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 192 - (((1*X)/(Z*W^2)))*rhsPivot6 X Y Z W a b r - (((1*X)/(Z*W^2)))*rhsPivot12 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_190 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 172 + ((1))*v 342=rhsPivot190 X Y Z W a b r := by
  have h:=hv 192
  change ((1))*v 172 + (((1*X)/(Z*W^2)))*v 255 + ((1))*v 342 + (((1*X)/(Z*W^2)))*v 425=r 192 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot190
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z*W^2)))*p6 - (((1*X)/(Z*W^2)))*p12)*(1/((1)))

def rhsPivot191 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 193 - (((1*X)/(Z*W^2)))*rhsPivot6 X Y Z W a b r - (((1*X)/(Z*W^2)))*rhsPivot11 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_191 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 168 + ((1))*v 338=rhsPivot191 X Y Z W a b r := by
  have h:=hv 193
  change (((1*X)/(Z*W^2)))*v 85 + ((1))*v 168 + (((1*X)/(Z*W^2)))*v 255 + ((1))*v 338=r 193 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot191
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z*W^2)))*p6 - (((1*X)/(Z*W^2)))*p11)*(1/((1)))

#print axioms pivot_191

def rhsPivot192 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 196 - (((1*X)/(Z)))*rhsPivot6 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot11 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_192 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 180 + ((1))*v 350=rhsPivot192 X Y Z W a b r := by
  have h:=hv 196
  change (((1*X)/(Z)))*v 85 + ((1))*v 180 + (((1*X)/(Z)))*v 255 + ((1))*v 350=r 196 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot192
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z)))*p6 - (((1*X)/(Z)))*p11)*(1/((1)))

def rhsPivot193 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 197 - (((1*X)/(Z)))*rhsPivot6 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot12 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_193 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 160 + ((1))*v 330=rhsPivot193 X Y Z W a b r := by
  have h:=hv 197
  change ((1))*v 160 + (((1*X)/(Z)))*v 255 + ((1))*v 330 + (((1*X)/(Z)))*v 425=r 197 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot193
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z)))*p6 - (((1*X)/(Z)))*p12)*(1/((1)))

def rhsPivot194 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 259 - ((1))*rhsPivot33 X Y Z W a b r - ((1))*rhsPivot185 X Y Z W a b r - (((1)/(X)))*rhsPivot187 X Y Z W a b r)/(((1)/(Y^2*W^2)))

compact_elimination_proof
theorem pivot_194 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 75 + ((1))*v 435=rhsPivot194 X Y Z W a b r := by
  have h:=hv 259
  change ((1))*v 2 + (((1)/(X)))*v 4 + ((1))*v 257=r 259 at h
  have p33:=pivot_33 X Y Z W a b hX hY hZ hW v r hv
  have p185:=pivot_185 X Y Z W a b hX hY hZ hW v r hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot194
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p33 - ((1))*p185 - (((1)/(X)))*p187)*(1/(((1)/(Y^2*W^2))))

def rhsPivot195 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 202 - ((1))*rhsPivot113 X Y Z W a b r - ((1))*rhsPivot120 X Y Z W a b r - ((1))*rhsPivot143 X Y Z W a b r - ((1))*rhsPivot165 X Y Z W a b r - ((((-1)*X*Z)/(W^2)))*rhsPivot194 X Y Z W a b r)/((((-1)*Z)/(W^2)))

compact_elimination_proof
theorem pivot_195 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 180 + ((1))*v 330=rhsPivot195 X Y Z W a b r := by
  have h:=hv 202
  change ((1))*v 102 + ((1))*v 204 + ((1))*v 306 + ((1))*v 408=r 202 at h
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot195
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p113 - ((1))*p120 - ((1))*p143 - ((1))*p165 - ((((-1)*X*Z)/(W^2)))*p194)*(1/((((-1)*Z)/(W^2))))

def rhsPivot196 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 262 - (((1)/(X)))*rhsPivot19 X Y Z W a b r - ((1))*rhsPivot140 X Y Z W a b r - ((1))*rhsPivot175 X Y Z W a b r)/(((1)/(Y^2*W^2)))

compact_elimination_proof
theorem pivot_196 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 135 + ((1))*v 390=rhsPivot196 X Y Z W a b r := by
  have h:=hv 262
  change ((1))*v 8 + (((1)/(X)))*v 16 + ((1))*v 263=r 262 at h
  have p19:=pivot_19 X Y Z W a b hX hY hZ hW v r hv
  have p140:=pivot_140 X Y Z W a b hX hY hZ hW v r hv
  have p175:=pivot_175 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot196
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p19 - ((1))*p140 - ((1))*p175)*(1/(((1)/(Y^2*W^2))))

def rhsPivot197 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 264 - ((1))*rhsPivot23 X Y Z W a b r - ((1))*rhsPivot183 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_197 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 22 + (((1)/(W^2)))*v 200=rhsPivot197 X Y Z W a b r := by
  have h:=hv 264
  change ((1))*v 11 + (((1)/(X)))*v 22 + ((1))*v 266=r 264 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v r hv
  have p183:=pivot_183 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot197
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p23 - ((1))*p183)*(1/(((1)/(X))))

def rhsPivot198 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 268 - ((1))*rhsPivot8 X Y Z W a b r - (((1)/(X)))*rhsPivot127 X Y Z W a b r - ((1))*rhsPivot146 X Y Z W a b r)/(((1)/(W^2)))

compact_elimination_proof
theorem pivot_198 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 165 + (((1)/(X)))*v 330=rhsPivot198 X Y Z W a b r := by
  have h:=hv 268
  change ((1))*v 18 + (((1)/(X)))*v 36 + ((1))*v 273=r 268 at h
  have p8:=pivot_8 X Y Z W a b hX hY hZ hW v r hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v r hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot198
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p8 - (((1)/(X)))*p127 - ((1))*p146)*(1/(((1)/(W^2))))

def rhsPivot199 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 275 - ((1))*rhsPivot38 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_199 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 66 + ((1*X))*v 288=rhsPivot199 X Y Z W a b r := by
  have h:=hv 275
  change ((1))*v 33 + (((1)/(X)))*v 66 + ((1))*v 288=r 275 at h
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot199
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p38)*(1/(((1)/(X))))

def rhsPivot200 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 283 - (((1)/(X)))*rhsPivot0 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_200 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 42 + ((1))*v 297=rhsPivot200 X Y Z W a b r := by
  have h:=hv 283
  change ((1))*v 42 + (((1)/(X)))*v 84 + ((1))*v 297=r 283 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot200
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p0)*(1/((1)))

def rhsPivot201 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 310 - ((1))*rhsPivot0 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_201 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 168 + ((1))*v 339=rhsPivot201 X Y Z W a b r := by
  have h:=hv 310
  change ((1))*v 84 + (((1)/(X)))*v 168 + ((1))*v 339=r 310 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot201
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p0)*(1/((1)))

def rhsPivot202 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 316 - ((1))*rhsPivot3 X Y Z W a b r - (((1)/(X)))*rhsPivot195 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_202 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 330 + ((1))*v 345=rhsPivot202 X Y Z W a b r := by
  have h:=hv 316
  change ((1))*v 90 + (((1)/(X)))*v 180 + ((1))*v 345=r 316 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot202
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p3 - (((1)/(X)))*p195)*(1/((1)))

def rhsPivot203 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 317 - ((1))*rhsPivot17 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_203 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 182 + ((1*X))*v 346=rhsPivot203 X Y Z W a b r := by
  have h:=hv 317
  change ((1))*v 91 + (((1)/(X)))*v 182 + ((1))*v 346=r 317 at h
  have p17:=pivot_17 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot203
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p17)*(1/(((1)/(X))))

def rhsPivot204 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 319 - ((1))*rhsPivot18 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_204 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 186 + ((1*X))*v 348=rhsPivot204 X Y Z W a b r := by
  have h:=hv 319
  change ((1))*v 93 + (((1)/(X)))*v 186 + ((1))*v 348=r 319 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot204
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18)*(1/(((1)/(X))))

def rhsPivot205 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 320 - ((1))*rhsPivot95 X Y Z W a b r - ((1))*rhsPivot192 X Y Z W a b r - (((-1)))*rhsPivot195 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_205 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 190 + (((1)/(Y^2)) + (1*X))*v 330=rhsPivot205 X Y Z W a b r := by
  have h:=hv 320
  change ((1))*v 95 + (((1)/(X)))*v 190 + ((1))*v 350=r 320 at h
  have p95:=pivot_95 X Y Z W a b hX hY hZ hW v r hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot205
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p95 - ((1))*p192 - (((-1)))*p195)*(1/(((1)/(X))))

def rhsPivot206 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 331 - (((1)/(X)))*rhsPivot29 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_206 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 116 + ((1))*v 371=rhsPivot206 X Y Z W a b r := by
  have h:=hv 331
  change ((1))*v 116 + (((1)/(X)))*v 232 + ((1))*v 371=r 331 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot206
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p29)*(1/((1)))

def rhsPivot207 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 333 - (((1)/(X)))*rhsPivot40 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_207 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 119 + ((1))*v 374=rhsPivot207 X Y Z W a b r := by
  have h:=hv 333
  change ((1))*v 119 + (((1)/(X)))*v 238 + ((1))*v 374=r 333 at h
  have p40:=pivot_40 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot207
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p40)*(1/((1)))

#print axioms pivot_207

def rhsPivot208 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 334 - (((1)/(X)))*rhsPivot27 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_208 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 120 + ((1))*v 375=rhsPivot208 X Y Z W a b r := by
  have h:=hv 334
  change ((1))*v 120 + (((1)/(X)))*v 240 + ((1))*v 375=r 334 at h
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot208
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p27)*(1/((1)))

def rhsPivot209 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 335 - (((1)/(X)))*rhsPivot48 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_209 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 122 + ((1))*v 377=rhsPivot209 X Y Z W a b r := by
  have h:=hv 335
  change ((1))*v 122 + (((1)/(X)))*v 244 + ((1))*v 377=r 335 at h
  have p48:=pivot_48 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot209
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p48)*(1/((1)))

def rhsPivot210 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 337 - (((1)/(X)))*rhsPivot43 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_210 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 125 + ((1))*v 380=rhsPivot210 X Y Z W a b r := by
  have h:=hv 337
  change ((1))*v 125 + (((1)/(X)))*v 250 + ((1))*v 380=r 337 at h
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot210
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p43)*(1/((1)))

def rhsPivot211 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 338 - (((1)/(X)))*rhsPivot45 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_211 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 126 + ((1))*v 381=rhsPivot211 X Y Z W a b r := by
  have h:=hv 338
  change ((1))*v 126 + (((1)/(X)))*v 252 + ((1))*v 381=r 338 at h
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot211
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p45)*(1/((1)))

def rhsPivot212 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 339 - (((1)/(X)))*rhsPivot50 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_212 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 127 + ((1))*v 382=rhsPivot212 X Y Z W a b r := by
  have h:=hv 339
  change ((1))*v 127 + (((1)/(X)))*v 254 + ((1))*v 382=r 339 at h
  have p50:=pivot_50 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot212
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p50)*(1/((1)))

def rhsPivot213 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 340 - (((1)/(X)))*rhsPivot51 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_213 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 128 + ((1))*v 383=rhsPivot213 X Y Z W a b r := by
  have h:=hv 340
  change ((1))*v 128 + (((1)/(X)))*v 256 + ((1))*v 383=r 340 at h
  have p51:=pivot_51 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot213
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p51)*(1/((1)))

def rhsPivot214 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 341 - (((1)/(X)))*rhsPivot46 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_214 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 129 + ((1))*v 384=rhsPivot214 X Y Z W a b r := by
  have h:=hv 341
  change ((1))*v 129 + (((1)/(X)))*v 258 + ((1))*v 384=r 341 at h
  have p46:=pivot_46 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot214
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p46)*(1/((1)))

def rhsPivot215 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 342 - (((1)/(X)))*rhsPivot21 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_215 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 130 + ((1))*v 385=rhsPivot215 X Y Z W a b r := by
  have h:=hv 342
  change ((1))*v 130 + (((1)/(X)))*v 260 + ((1))*v 385=r 342 at h
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot215
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p21)*(1/((1)))

def rhsPivot216 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 344 - (((1)/(X)))*rhsPivot23 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_216 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 133 + ((1))*v 388=rhsPivot216 X Y Z W a b r := by
  have h:=hv 344
  change ((1))*v 133 + (((1)/(X)))*v 266 + ((1))*v 388=r 344 at h
  have p23:=pivot_23 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot216
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p23)*(1/((1)))

def rhsPivot217 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 345 - (((1)/(X)))*rhsPivot14 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_217 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 136 + ((1))*v 391=rhsPivot217 X Y Z W a b r := by
  have h:=hv 345
  change ((1))*v 136 + (((1)/(X)))*v 272 + ((1))*v 391=r 345 at h
  have p14:=pivot_14 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot217
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p14)*(1/((1)))

def rhsPivot218 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 347 - (((1)/(X)))*rhsPivot24 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_218 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 139 + ((1))*v 394=rhsPivot218 X Y Z W a b r := by
  have h:=hv 347
  change ((1))*v 139 + (((1)/(X)))*v 278 + ((1))*v 394=r 347 at h
  have p24:=pivot_24 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot218
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p24)*(1/((1)))

def rhsPivot219 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 360 - ((1))*rhsPivot105 X Y Z W a b r - ((1))*rhsPivot193 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot195 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_219 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 320 + ((((-1))/(Y^2)) + ((-1)*X))*v 330=rhsPivot219 X Y Z W a b r := by
  have h:=hv 360
  change ((1))*v 160 + (((1)/(X)))*v 320 + ((1))*v 415=r 360 at h
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v r hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot219
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p105 - ((1))*p193 - (((1)/(X*Y^2)))*p195)*(1/(((1)/(X))))

def rhsPivot220 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 361 - ((1))*rhsPivot26 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_220 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X))*v 162 + ((1))*v 324=rhsPivot220 X Y Z W a b r := by
  have h:=hv 361
  change ((1))*v 162 + (((1)/(X)))*v 324 + ((1))*v 417=r 361 at h
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot220
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p26)*(1/(((1)/(X))))

def rhsPivot221 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 363 - ((1))*rhsPivot20 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_221 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X))*v 164 + ((1))*v 328=rhsPivot221 X Y Z W a b r := by
  have h:=hv 363
  change ((1))*v 164 + (((1)/(X)))*v 328 + ((1))*v 419=r 363 at h
  have p20:=pivot_20 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot221
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p20)*(1/(((1)/(X))))

def rhsPivot222 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 369 - ((1))*rhsPivot16 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_222 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 171 + (((1)/(X)))*v 342=rhsPivot222 X Y Z W a b r := by
  have h:=hv 369
  change ((1))*v 171 + (((1)/(X)))*v 342 + ((1))*v 426=r 369 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot222
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p16)*(1/((1)))

def rhsPivot223 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 394 - (((1)/(X)))*rhsPivot16 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_223 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 213 + ((1))*v 468=rhsPivot223 X Y Z W a b r := by
  have h:=hv 394
  change ((1))*v 213 + (((1)/(X)))*v 426 + ((1))*v 468=r 394 at h
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot223
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p16)*(1/((1)))

#print axioms pivot_223

def rhsPivot224 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 401 - ((1))*rhsPivot39 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_224 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X))*v 222 + ((1))*v 444=rhsPivot224 X Y Z W a b r := by
  have h:=hv 401
  change ((1))*v 222 + (((1)/(X)))*v 444 + ((1))*v 477=r 401 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot224
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p39)*(1/(((1)/(X))))

def rhsPivot225 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 409 - ((1))*rhsPivot48 X Y Z W a b r - ((1))*rhsPivot84 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_225 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(W^2)))*v 310 + ((1))*v 488=rhsPivot225 X Y Z W a b r := by
  have h:=hv 409
  change ((1))*v 244 + (((1)/(X)))*v 488 + ((1))*v 499=r 409 at h
  have p48:=pivot_48 X Y Z W a b hX hY hZ hW v r hv
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot225
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p48 - ((1))*p84)*(1/(((1)/(X))))

def rhsPivot226 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 413 - ((1))*rhsPivot52 X Y Z W a b r - (((1)/(X)))*rhsPivot184 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_226 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 253 + (((1)/(Y^2*W^2)))*v 435=rhsPivot226 X Y Z W a b r := by
  have h:=hv 413
  change ((1))*v 253 + (((1)/(X)))*v 506 + ((1))*v 508=r 413 at h
  have p52:=pivot_52 X Y Z W a b hX hY hZ hW v r hv
  have p184:=pivot_184 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot226
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p52 - (((1)/(X)))*p184)*(1/((1)))

def rhsPivot227 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 430 - ((((-1)*a)/(Y)))*rhsPivot3 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot9 X Y Z W a b r - ((1))*rhsPivot15 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_227 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 200 + ((1))*v 370=rhsPivot227 X Y Z W a b r := by
  have h:=hv 430
  change ((1))*v 30 + ((((-1)*a)/(Y)))*v 90 + ((1))*v 200 + (((1)/(Y^2)))*v 270 + ((1))*v 370=r 430 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot227
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p3 - (((1)/(Y^2)))*p9 - ((1))*p15)*(1/((1)))

def rhsPivot228 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 418 - ((((-1)*a)/(Y)))*rhsPivot38 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot97 X Y Z W a b r - ((1))*rhsPivot183 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot227 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_228 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 181 + ((1))*v 351=rhsPivot228 X Y Z W a b r := by
  have h:=hv 418
  change ((1))*v 11 + ((((-1)*a)/(Y)))*v 33 + (((1)/(Y^2)))*v 99 + ((1))*v 181 + ((1))*v 351=r 418 at h
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v r hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v r hv
  have p183:=pivot_183 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot228
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p38 - (((1)/(Y^2)))*p97 - ((1))*p183 - (((1)/(X*W^2)))*p227)*(1/((1)))

def rhsPivot229 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 431 - ((((-1)*a)/(Y)))*rhsPivot18 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot116 X Y Z W a b r - ((1))*rhsPivot173 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_229 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 201 + ((1))*v 371=rhsPivot229 X Y Z W a b r := by
  have h:=hv 431
  change ((1))*v 31 + ((((-1)*a)/(Y)))*v 93 + ((1))*v 201 + (((1)/(Y^2)))*v 279 + ((1))*v 371=r 431 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v r hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v r hv
  have p173:=pivot_173 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot229
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p18 - (((1)/(Y^2)))*p116 - ((1))*p173 - (((1)/(Y^2*W^2)))*p189)*(1/((1)))

def rhsPivot230 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 453 - ((1))*rhsPivot105 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot137 X Y Z W a b r - ((1))*rhsPivot145 X Y Z W a b r - (((1)/(Y^2)) + (1))*rhsPivot194 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot195 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot198 X Y Z W a b r)/((((-2))/(X*Y^2)))

compact_elimination_proof
theorem pivot_230 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 330 + (((1*X)/(2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2)/(2)))*v 435=rhsPivot230 X Y Z W a b r := by
  have h:=hv 453
  change ((1))*v 75 + (((1)/(Y^2)))*v 165 + ((((-1)*a)/(Y)))*v 225 + ((1))*v 245 + ((1))*v 415=r 453 at h
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v r hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v r hv
  have p145:=pivot_145 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot230
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p105 - ((((-1)*a)/(Y)))*p137 - ((1))*p145 - (((1)/(Y^2)) + (1))*p194 - (((1)/(X*Y^2)))*p195 - (((1)/(Y^2)))*p198)*(1/((((-2))/(X*Y^2))))

def rhsPivot231 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 272 - ((1))*rhsPivot62 X Y Z W a b r - ((1))*rhsPivot132 X Y Z W a b r - (((1)/(X)))*rhsPivot134 X Y Z W a b r - ((((-1)*W^2)/(X*Y^2*Z)))*rhsPivot165 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot230 X Y Z W a b r)/((((-1)*W^2)/(Y^2*Z)))

compact_elimination_proof
theorem pivot_231 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 357 + (((1*Z)/(2*W^2)) + ((1*Y*Z*a)/(2*W^2)) + ((1*Y^2*Z)/(2*W^2)) + (((-1)*X*Z)/(W^2)))*v 435=rhsPivot231 X Y Z W a b r := by
  have h:=hv 272
  change ((1))*v 25 + (((1)/(X)))*v 50 + ((1))*v 280=r 272 at h
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v r hv
  have p132:=pivot_132 X Y Z W a b hX hY hZ hW v r hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot231
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p62 - ((1))*p132 - (((1)/(X)))*p134 - ((((-1)*W^2)/(X*Y^2*Z)))*p165 - (((1)/(X*Y^2)))*p230)*(1/((((-1)*W^2)/(Y^2*Z))))

def rhsPivot232 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 289 - (((1)/(X)))*rhsPivot113 X Y Z W a b r - ((1))*rhsPivot130 X Y Z W a b r - ((1))*rhsPivot143 X Y Z W a b r - ((((-1)*Z)/(W^2)))*rhsPivot195 X Y Z W a b r - (((1*Z)/(W^2)))*rhsPivot230 X Y Z W a b r)/((((-1)*Z)/(X*W^2)))

compact_elimination_proof
theorem pivot_232 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 360 + ((1*X) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)))*v 435=rhsPivot232 X Y Z W a b r := by
  have h:=hv 289
  change ((1))*v 51 + (((1)/(X)))*v 102 + ((1))*v 306=r 289 at h
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot232
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p113 - ((1))*p130 - ((1))*p143 - ((((-1)*Z)/(W^2)))*p195 - (((1*Z)/(W^2)))*p230)*(1/((((-1)*Z)/(X*W^2))))

def rhsPivot233 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 302 - ((1))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot230 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_233 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 150 + (((-1)*X) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)))*v 435=rhsPivot233 X Y Z W a b r := by
  have h:=hv 302
  change ((1))*v 75 + (((1)/(X)))*v 150 + ((1))*v 330=r 302 at h
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot233
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p194 - ((1))*p230)*(1/(((1)/(X))))

def rhsPivot234 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 211 - ((1))*rhsPivot130 X Y Z W a b r - ((1))*rhsPivot135 X Y Z W a b r - ((1))*rhsPivot231 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot233 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_234 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 153 + ((((-1)*Z)/(2*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((1*X*Z)/(W^2)))*v 435=rhsPivot234 X Y Z W a b r := by
  have h:=hv 211
  change ((1))*v 51 + ((1))*v 153 + ((1))*v 357 + ((1))*v 459=r 211 at h
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot234
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p130 - ((1))*p135 - ((1))*p231 - ((((-1)*Z)/(X*W^2)))*p232 - ((((-1)*Z)/(X*W^2)))*p233)*(1/((1)))

def rhsPivot235 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 218 - ((1))*rhsPivot3 X Y Z W a b r - ((1))*rhsPivot4 X Y Z W a b r - ((1))*rhsPivot9 X Y Z W a b r - ((1))*rhsPivot13 X Y Z W a b r - ((1))*rhsPivot15 X Y Z W a b r - ((1))*rhsPivot27 X Y Z W a b r - ((1))*rhsPivot77 X Y Z W a b r - ((1))*rhsPivot91 X Y Z W a b r - ((1))*rhsPivot121 X Y Z W a b r - ((1))*rhsPivot150 X Y Z W a b r - ((1*X))*rhsPivot189 X Y Z W a b r - ((1*X))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot232 X Y Z W a b r - ((1))*rhsPivot233 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_235 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 120 + ((1))*v 390=rhsPivot235 X Y Z W a b r := by
  have h:=hv 218
  change ((1))*v 30 + ((1))*v 60 + ((1))*v 90 + ((1))*v 120 + ((1))*v 150 + ((1))*v 180 + ((1))*v 210 + ((1))*v 240 + ((1))*v 270 + ((1))*v 300 + ((1))*v 330 + ((1))*v 360 + ((1))*v 390 + ((1))*v 420 + ((1))*v 450 + ((1))*v 480=r 218 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot235
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p3 - ((1))*p4 - ((1))*p9 - ((1))*p13 - ((1))*p15 - ((1))*p27 - ((1))*p77 - ((1))*p91 - ((1))*p121 - ((1))*p150 - ((1*X))*p189 - ((1*X))*p194 - ((1))*p195 - ((1))*p232 - ((1))*p233)*(1/((1)))

def rhsPivot236 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 228 - ((1))*rhsPivot2 X Y Z W a b r - ((((-1))/(X)))*rhsPivot3 X Y Z W a b r - ((((-1))/(X)))*rhsPivot4 X Y Z W a b r - ((1))*rhsPivot6 X Y Z W a b r - ((((-1))/(X)))*rhsPivot9 X Y Z W a b r - ((((-1))/(X)))*rhsPivot10 X Y Z W a b r - ((((-1))/(X)))*rhsPivot15 X Y Z W a b r - ((((-1))/(X)))*rhsPivot27 X Y Z W a b r - ((((-1))/(X)))*rhsPivot77 X Y Z W a b r - ((1))*rhsPivot83 X Y Z W a b r - ((((-1))/(X)))*rhsPivot91 X Y Z W a b r - ((1))*rhsPivot99 X Y Z W a b r - ((1))*rhsPivot102 X Y Z W a b r - ((((-1))/(X)))*rhsPivot121 X Y Z W a b r - ((1))*rhsPivot131 X Y Z W a b r - ((1))*rhsPivot137 X Y Z W a b r - ((((-1))/(X)))*rhsPivot150 X Y Z W a b r - ((1))*rhsPivot194 X Y Z W a b r - ((((-1))/(X)))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot196 X Y Z W a b r - ((1))*rhsPivot198 X Y Z W a b r - ((1))*rhsPivot202 X Y Z W a b r - ((1))*rhsPivot208 X Y Z W a b r - ((((-1))/(X)))*rhsPivot232 X Y Z W a b r - ((((-1))/(X)))*rhsPivot233 X Y Z W a b r - (((-1)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_236 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(X)))*v 40 + ((1))*v 315=rhsPivot236 X Y Z W a b r := by
  have h:=hv 228
  change ((((-1))/(X)))*v 0 + ((((-1))/(X)))*v 30 + ((1))*v 45 + ((((-1))/(X)))*v 60 + ((1))*v 75 + ((((-1))/(X)))*v 90 + ((1))*v 105 + ((((-1))/(X)))*v 120 + ((1))*v 135 + ((((-1))/(X)))*v 150 + ((1))*v 165 + ((((-1))/(X)))*v 180 + ((1))*v 195 + ((((-1))/(X)))*v 210 + ((1))*v 225 + ((((-1))/(X)))*v 240 + ((1))*v 255 + ((((-1))/(X)))*v 270 + ((1))*v 285 + ((((-1))/(X)))*v 300 + ((1))*v 315 + ((((-1))/(X)))*v 330 + ((1))*v 345 + ((((-1))/(X)))*v 360 + ((1))*v 375 + ((((-1))/(X)))*v 390 + ((1))*v 405 + ((((-1))/(X)))*v 420 + ((1))*v 435 + ((((-1))/(X)))*v 450 + ((1))*v 465 + ((1))*v 495=r 228 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot236
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p2 - ((((-1))/(X)))*p3 - ((((-1))/(X)))*p4 - ((1))*p6 - ((((-1))/(X)))*p9 - ((((-1))/(X)))*p10 - ((((-1))/(X)))*p15 - ((((-1))/(X)))*p27 - ((((-1))/(X)))*p77 - ((1))*p83 - ((((-1))/(X)))*p91 - ((1))*p99 - ((1))*p102 - ((((-1))/(X)))*p121 - ((1))*p131 - ((1))*p137 - ((((-1))/(X)))*p150 - ((1))*p194 - ((((-1))/(X)))*p195 - ((1))*p196 - ((1))*p198 - ((1))*p202 - ((1))*p208 - ((((-1))/(X)))*p232 - ((((-1))/(X)))*p233 - (((-1)))*p235)*(1/((1)))

def rhsPivot237 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 424 - ((1))*rhsPivot71 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot113 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot130 X Y Z W a b r - ((1))*rhsPivot231 X Y Z W a b r - (((1*Z*a)/(X*Y*W^2)))*rhsPivot232 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot234 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_237 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 187 + ((((-1)*Z)/(2*Y^2*W^2)) + (((-1)*Z*a)/(2*Y*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*Z*a)/(2*Y*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)))*v 435=rhsPivot237 X Y Z W a b r := by
  have h:=hv 424
  change ((1))*v 17 + ((((-1)*a)/(Y)))*v 51 + (((1)/(Y^2)))*v 153 + ((1))*v 187 + ((1))*v 357=r 424 at h
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v r hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot237
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p71 - (((1)/(X*Y^2)))*p113 - ((((-1)*a)/(Y)))*p130 - ((1))*p231 - (((1*Z*a)/(X*Y*W^2)))*p232 - (((1)/(Y^2)))*p234)*(1/((1)))

def rhsPivot238 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 433 - ((((-1)*a)/(Y)))*rhsPivot113 X Y Z W a b r - ((1))*rhsPivot133 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot143 X Y Z W a b r - ((1))*rhsPivot165 X Y Z W a b r - ((((-1)*X*Z)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*Z)/(Y^2*W^2)))*rhsPivot195 X Y Z W a b r - (((1*Z)/(Y^2*W^2)) + (((-1)*Z)/(W^2)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_238 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 374 + (((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z*a)/(2*Y*W^2)) + ((1*X*Y*Z*a)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)))*v 435=rhsPivot238 X Y Z W a b r := by
  have h:=hv 433
  change ((1))*v 34 + ((((-1)*a)/(Y)))*v 102 + ((1))*v 204 + (((1)/(Y^2)))*v 306 + ((1))*v 374=r 433 at h
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p133:=pivot_133 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot238
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p113 - ((1))*p133 - (((1)/(Y^2)))*p143 - ((1))*p165 - ((((-1)*X*Z)/(Y^2*W^2)))*p194 - ((((-1)*Z)/(Y^2*W^2)))*p195 - (((1*Z)/(Y^2*W^2)) + (((-1)*Z)/(W^2)))*p230)*(1/((1)))

def rhsPivot239 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 382 - ((1))*rhsPivot119 X Y Z W a b r - ((1))*rhsPivot237 X Y Z W a b r - (((1)/(X)))*rhsPivot238 X Y Z W a b r)/((((-1)*Z)/(W^2)))

compact_elimination_proof
theorem pivot_239 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 400 + ((((-1)*X)/(Y^2)) + (((-1)*X*a)/(2*Y)) + (1*X) + (((-1)*X*a^2)/(2)) + (((-1)*X*Y*a)/(2)))*v 435=rhsPivot239 X Y Z W a b r := by
  have h:=hv 382
  change ((1))*v 187 + (((1)/(X)))*v 374 + ((1))*v 442=r 382 at h
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v r hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot239
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p119 - ((1))*p237 - (((1)/(X)))*p238)*(1/((((-1)*Z)/(W^2))))

#print axioms pivot_239

def rhsPivot240 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 400 - (((1)/(X)))*rhsPivot119 X Y Z W a b r - ((1))*rhsPivot128 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot239 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_240 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 221 + ((((-1)*Z)/(Y^2*W^2)) + (((-1)*Z*a)/(2*Y*W^2)) + ((1*Z)/(W^2)) + (((-1)*Z*a^2)/(2*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)))*v 435=rhsPivot240 X Y Z W a b r := by
  have h:=hv 400
  change ((1))*v 221 + (((1)/(X)))*v 442 + ((1))*v 476=r 400 at h
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v r hv
  have p128:=pivot_128 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot240
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p119 - ((1))*p128 - ((((-1)*Z)/(X*W^2)))*p239)*(1/((1)))

def rhsPivot241 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 443 - ((1))*rhsPivot130 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot135 X Y Z W a b r - ((1))*rhsPivot217 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*Z)/(X*Y^2*W^2)))*rhsPivot233 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot234 X Y Z W a b r - ((1))*rhsPivot240 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_241 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 136 + ((((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z*a)/(2*Y*W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)))*v 435=rhsPivot241 X Y Z W a b r := by
  have h:=hv 443
  change ((1))*v 51 + ((((-1)*a)/(Y)))*v 153 + ((1))*v 221 + ((1))*v 391 + (((1)/(Y^2)))*v 459=r 443 at h
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v r hv
  have p217:=pivot_217 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot241
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p130 - (((1)/(Y^2)))*p135 - ((1))*p217 - ((((-1)*Z)/(X*W^2)))*p232 - ((((-1)*Z)/(X*Y^2*W^2)))*p233 - ((((-1)*a)/(Y)))*p234 - ((1))*p240)*(1/(((-1))))

def rhsPivot242 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 217 - ((1))*rhsPivot14 X Y Z W a b r - ((1))*rhsPivot40 X Y Z W a b r - ((1))*rhsPivot119 X Y Z W a b r - ((1))*rhsPivot128 X Y Z W a b r - ((1))*rhsPivot133 X Y Z W a b r - ((1))*rhsPivot169 X Y Z W a b r - ((((-1)*X*Z)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot238 X Y Z W a b r - ((((-1)*Z)/(W^2)))*rhsPivot239 X Y Z W a b r - ((1))*rhsPivot241 X Y Z W a b r)/((((-1)*Z)/(W^2)))

compact_elimination_proof
theorem pivot_242 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 110 + (((1*X)/(Y^2)) + ((1*X*a)/(2*Y)) + ((-1)*X) + ((1*X*a^2)/(2)) + ((1*X*Y*a)/(2)))*v 435=rhsPivot242 X Y Z W a b r := by
  have h:=hv 217
  change ((1))*v 34 + ((1))*v 68 + ((1))*v 136 + ((1))*v 238 + ((1))*v 272 + ((1))*v 374 + ((1))*v 442 + ((1))*v 476=r 217 at h
  have p14:=pivot_14 X Y Z W a b hX hY hZ hW v r hv
  have p40:=pivot_40 X Y Z W a b hX hY hZ hW v r hv
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v r hv
  have p128:=pivot_128 X Y Z W a b hX hY hZ hW v r hv
  have p133:=pivot_133 X Y Z W a b hX hY hZ hW v r hv
  have p169:=pivot_169 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot242
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p14 - ((1))*p40 - ((1))*p119 - ((1))*p128 - ((1))*p133 - ((1))*p169 - ((((-1)*X*Z)/(Y^2*W^2)))*p194 - ((1))*p238 - ((((-1)*Z)/(W^2)))*p239 - ((1))*p241)*(1/((((-1)*Z)/(W^2))))

def rhsPivot243 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 276 - ((1))*rhsPivot133 X Y Z W a b r - (((1)/(X)))*rhsPivot169 X Y Z W a b r - ((((-1)*X*Z)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot242 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_243 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 289 + (((1*Z)/(Y^2*W^2)) + ((1*Z*a)/(2*Y*W^2)) + (((-1)*Z)/(W^2)) + ((1*Z*a^2)/(2*W^2)) + ((1*Y*Z*a)/(2*W^2)) + ((1*X*Z)/(Y^2*W^2)))*v 435=rhsPivot243 X Y Z W a b r := by
  have h:=hv 276
  change ((1))*v 34 + (((1)/(X)))*v 68 + ((1))*v 289=r 276 at h
  have p133:=pivot_133 X Y Z W a b hX hY hZ hW v r hv
  have p169:=pivot_169 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot243
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p133 - (((1)/(X)))*p169 - ((((-1)*X*Z)/(Y^2*W^2)))*p194 - ((((-1)*Z)/(X*W^2)))*p242)*(1/((1)))

def rhsPivot244 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 238 - ((1))*rhsPivot71 X Y Z W a b r - ((1))*rhsPivot72 X Y Z W a b r - ((((-1)*Z)/(Y^2*W^2)))*rhsPivot83 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot113 X Y Z W a b r - ((((-1)*Z)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot207 X Y Z W a b r - ((1))*rhsPivot217 X Y Z W a b r - ((1))*rhsPivot237 X Y Z W a b r - (((-1)))*rhsPivot238 X Y Z W a b r - ((1))*rhsPivot240 X Y Z W a b r - (((-1)))*rhsPivot241 X Y Z W a b r - ((1))*rhsPivot243 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_244 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 323 + (((1*Z)/(2*Y^2*W^2)) + ((1*Z*a)/(2*Y*W^2)) + ((1*Y*Z*a)/(2*W^2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*Z*a)/(2*Y*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + ((1*X*Y*Z*a)/(2*W^2)))*v 435=rhsPivot244 X Y Z W a b r := by
  have h:=hv 238
  change ((1))*v 17 + ((1))*v 119 + ((1))*v 187 + ((1))*v 221 + ((1))*v 289 + ((1))*v 323 + ((1))*v 391 + ((1))*v 493=r 238 at h
  have p71:=pivot_71 X Y Z W a b hX hY hZ hW v r hv
  have p72:=pivot_72 X Y Z W a b hX hY hZ hW v r hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v r hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p207:=pivot_207 X Y Z W a b hX hY hZ hW v r hv
  have p217:=pivot_217 X Y Z W a b hX hY hZ hW v r hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot244
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p71 - ((1))*p72 - ((((-1)*Z)/(Y^2*W^2)))*p83 - (((1)/(X*Y^2)))*p113 - ((((-1)*Z)/(Y^2*W^2)))*p194 - ((1))*p207 - ((1))*p217 - ((1))*p237 - (((-1)))*p238 - ((1))*p240 - (((-1)))*p241 - ((1))*p243)*(1/((1)))

def rhsPivot245 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 478 - ((((-1)*a)/(Y)))*rhsPivot26 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot157 X Y Z W a b r - ((1))*rhsPivot168 X Y Z W a b r - (((1)/(X)))*rhsPivot171 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot218 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_245 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)))*v 309 + ((1))*v 394=rhsPivot245 X Y Z W a b r := by
  have h:=hv 478
  change ((1))*v 139 + (((1)/(Y^2)))*v 231 + ((1))*v 309 + ((((-1)*a)/(Y)))*v 417 + ((1))*v 479=r 478 at h
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v r hv
  have p168:=pivot_168 X Y Z W a b hX hY hZ hW v r hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p218:=pivot_218 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot245
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p26 - (((1)/(Y^2)))*p157 - ((1))*p168 - (((1)/(X)))*p171 - (((1)/(Y^2*W^2)))*p189 - ((1))*p218)*(1/(((-1))))

def rhsPivot246 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 479 - ((((-1)*a)/(Y)))*rhsPivot4 X Y Z W a b r - ((1))*rhsPivot13 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot27 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_246 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 140 + ((1))*v 310=rhsPivot246 X Y Z W a b r := by
  have h:=hv 479
  change ((1))*v 140 + (((1)/(Y^2)))*v 240 + ((1))*v 310 + ((((-1)*a)/(Y)))*v 420 + ((1))*v 480=r 479 at h
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot246
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p4 - ((1))*p13 - (((1)/(Y^2)))*p27)*(1/((1)))

def rhsPivot247 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 489 - ((((-1)*a)/(Y)))*rhsPivot39 X Y Z W a b r - ((1))*rhsPivot84 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot103 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot246 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_247 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 159 + ((1))*v 329=rhsPivot247 X Y Z W a b r := by
  have h:=hv 489
  change ((1))*v 159 + ((1))*v 329 + (((1)/(Y^2)))*v 411 + ((((-1)*a)/(Y)))*v 477 + ((1))*v 499=r 489 at h
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v r hv
  have p84:=pivot_84 X Y Z W a b hX hY hZ hW v r hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot247
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p39 - ((1))*p84 - (((1)/(Y^2)))*p103 - (((1)/(X*W^2)))*p246)*(1/((1)))

def rhsPivot248 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 190 - (((1)/(X*Z*W^2)))*rhsPivot10 X Y Z W a b r - (((1)/(X*Z*W^2)))*rhsPivot118 X Y Z W a b r - ((1))*rhsPivot222 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_248 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2*W^2)))*v 45 + ((1))*v 341 + ((((-1))/(X)))*v 342=rhsPivot248 X Y Z W a b r := by
  have h:=hv 190
  change (((1)/(X*Z*W^2)))*v 0 + ((1))*v 171 + (((1)/(X*Z*W^2)))*v 340 + ((1))*v 341=r 190 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot248
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z*W^2)))*p10 - (((1)/(X*Z*W^2)))*p118 - ((1))*p222)*(1/((1)))

def rhsPivot249 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 191 - (((1)/(X*Z*W^2)))*rhsPivot10 X Y Z W a b r - (((1)/(X*Z*W^2)))*rhsPivot117 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot201 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_249 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(Y^2*W^2)))*v 45 + ((((-1))/(X)))*v 168 + ((1))*v 169=rhsPivot249 X Y Z W a b r := by
  have h:=hv 191
  change (((1)/(X*Z*W^2)))*v 0 + ((1))*v 169 + (((1)/(X*Z*W^2)))*v 170 + ((1))*v 339=r 191 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot249
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z*W^2)))*p10 - (((1)/(X*Z*W^2)))*p117 - ((((-1))/(Y^2*W^2)))*p189 - ((1))*p201)*(1/((1)))

def rhsPivot250 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 194 - (((1)/(X*Z)))*rhsPivot10 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot117 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot202 X Y Z W a b r - (((1)/(X)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_250 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(Y^2)))*v 45 + ((1))*v 175 + ((((-1))/(2)) + (((-1)*Y*a)/(2)) + (((-1)*Y^2)/(2)))*v 435=rhsPivot250 X Y Z W a b r := by
  have h:=hv 194
  change (((1)/(X*Z)))*v 0 + (((1)/(X*Z)))*v 170 + ((1))*v 175 + ((1))*v 345=r 194 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot250
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p10 - (((1)/(X*Z)))*p117 - ((((-1))/(Y^2)))*p189 - ((1))*p202 - (((1)/(X)))*p230)*(1/((1)))

def rhsPivot251 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 195 - (((1)/(X*Z)))*rhsPivot10 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot118 X Y Z W a b r - ((1))*rhsPivot198 X Y Z W a b r - ((((-1))/(X)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_251 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(Y^2)))*v 45 + ((1))*v 335 + (((1)/(2)) + ((1*Y*a)/(2)) + ((1*Y^2)/(2)))*v 435=rhsPivot251 X Y Z W a b r := by
  have h:=hv 195
  change (((1)/(X*Z)))*v 0 + ((1))*v 165 + ((1))*v 335 + (((1)/(X*Z)))*v 340=r 195 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot251
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p10 - (((1)/(X*Z)))*p118 - ((1))*p198 - ((((-1))/(X)))*p230)*(1/((1)))

def rhsPivot252 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 198 - (((1*Z)/(X*W^2)))*rhsPivot164 X Y Z W a b r - ((1))*rhsPivot231 X Y Z W a b r - (((1*Z)/(X*W^2)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot237 X Y Z W a b r)/(((1*Z)/(X*Y^2)))

compact_elimination_proof
theorem pivot_252 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 78 + ((((-1)*Y^2)/(W^2)))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)))*v 435=rhsPivot252 X Y Z W a b r := by
  have h:=hv 198
  change (((1*Z)/(X*W^2)))*v 120 + ((1))*v 187 + (((1*Z)/(X*W^2)))*v 290 + ((1))*v 357=r 198 at h
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot252
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X*W^2)))*p164 - ((1))*p231 - (((1*Z)/(X*W^2)))*p235 - ((1))*p237)*(1/(((1*Z)/(X*Y^2))))

def rhsPivot253 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 199 - (((1*Z)/(X*W^2)))*rhsPivot144 X Y Z W a b r - ((1))*rhsPivot234 X Y Z W a b r - ((1))*rhsPivot244 X Y Z W a b r)/(((1*Z)/(Y^2)))

compact_elimination_proof
theorem pivot_253 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(X*W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)))*v 435 + ((1))*v 489=rhsPivot253 X Y Z W a b r := by
  have h:=hv 199
  change ((1))*v 153 + (((1*Z)/(X*W^2)))*v 220 + ((1))*v 323 + (((1*Z)/(X*W^2)))*v 390=r 199 at h
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot253
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X*W^2)))*p144 - ((1))*p234 - ((1))*p244)*(1/(((1*Z)/(Y^2))))

def rhsPivot254 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 200 - ((1))*rhsPivot131 X Y Z W a b r - (((1*W^2)/(X*Z)))*rhsPivot143 X Y Z W a b r - ((((-1))/(X)))*rhsPivot195 X Y Z W a b r - (((1)/(X)))*rhsPivot230 X Y Z W a b r - (((1*W^2)/(X*Z)))*rhsPivot241 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_254 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(X)))*v 40 + ((1))*v 365 + (((1)/(2*Y^2)) + ((1*a)/(2*Y)) + (((-1))/(2)))*v 435=rhsPivot254 X Y Z W a b r := by
  have h:=hv 200
  change (((1*W^2)/(X*Z)))*v 136 + ((1))*v 195 + (((1*W^2)/(X*Z)))*v 306 + ((1))*v 365=r 200 at h
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot254
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p131 - (((1*W^2)/(X*Z)))*p143 - ((((-1))/(X)))*p195 - (((1)/(X)))*p230 - (((1*W^2)/(X*Z)))*p241)*(1/((1)))

def rhsPivot255 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 201 - (((1*W^2)/(X*Z)))*rhsPivot165 X Y Z W a b r - ((((-1))/(X)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot236 X Y Z W a b r - (((1*W^2)/(X*Z)))*rhsPivot238 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_255 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X)))*v 40 + ((1))*v 145 + ((((-1))/(2*Y^2)) + (((-1)*a)/(2*Y)) + ((1)/(2)))*v 435=rhsPivot255 X Y Z W a b r := by
  have h:=hv 201
  change ((1))*v 145 + (((1*W^2)/(X*Z)))*v 204 + ((1))*v 315 + (((1*W^2)/(X*Z)))*v 374=r 201 at h
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot255
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*W^2)/(X*Z)))*p165 - ((((-1))/(X)))*p230 - ((1))*p236 - (((1*W^2)/(X*Z)))*p238)*(1/((1)))

#print axioms pivot_255

def rhsPivot256 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 260 - (((1)/(X)))*rhsPivot140 X Y Z W a b r - ((1))*rhsPivot174 X Y Z W a b r - ((1))*rhsPivot187 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r)/(((1)/(X*W^2)))

compact_elimination_proof
theorem pivot_256 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 40 + (((1)/(Y^2)))*v 390 + ((((-1)*X^2)/(Y^2)))*v 435=rhsPivot256 X Y Z W a b r := by
  have h:=hv 260
  change ((1))*v 4 + (((1)/(X)))*v 8 + ((1))*v 259=r 260 at h
  have p140:=pivot_140 X Y Z W a b hX hY hZ hW v r hv
  have p174:=pivot_174 X Y Z W a b hX hY hZ hW v r hv
  have p187:=pivot_187 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot256
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p140 - ((1))*p174 - ((1))*p187 - (((1*X)/(Y^2*W^2)))*p194)*(1/(((1)/(X*W^2))))

def rhsPivot257 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 261 - ((1))*rhsPivot81 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot111 X Y Z W a b r - ((1))*rhsPivot139 X Y Z W a b r - (((1)/(X)))*rhsPivot171 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot232 X Y Z W a b r)/(((1)/(Y^2*W^2)))

compact_elimination_proof
theorem pivot_257 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 45 + (((1)/(X)))*v 390 + (((-1)*X) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)))*v 435=rhsPivot257 X Y Z W a b r := by
  have h:=hv 261
  change ((1))*v 7 + (((1)/(X)))*v 14 + ((1))*v 262=r 261 at h
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v r hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v r hv
  have p139:=pivot_139 X Y Z W a b hX hY hZ hW v r hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot257
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p81 - (((1*X)/(W^2)))*p111 - ((1))*p139 - (((1)/(X)))*p171 - (((1)/(Y^2*W^2)))*p232)*(1/(((1)/(Y^2*W^2))))

def rhsPivot258 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 207 - (((1*Y^2)/(X*Z)))*rhsPivot14 X Y Z W a b r - ((1))*rhsPivot26 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot117 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot169 X Y Z W a b r - (((-1)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot223 X Y Z W a b r - ((1))*rhsPivot236 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot238 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot242 X Y Z W a b r - ((((-1)*Y^2)/(X)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_258 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 111 + (((1)/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)))*v 435 + (((-1)))*v 468=rhsPivot258 X Y Z W a b r := by
  have h:=hv 207
  change (((1*Y^2)/(X*Z)))*v 68 + ((1))*v 111 + (((1*Y^2)/(X*Z)))*v 170 + ((1))*v 213 + (((1*Y^2)/(X*Z)))*v 272 + ((1))*v 315 + (((1*Y^2)/(X*Z)))*v 374 + ((1))*v 417=r 207 at h
  have p14:=pivot_14 X Y Z W a b hX hY hZ hW v r hv
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p169:=pivot_169 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot258
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Y^2)/(X*Z)))*p14 - ((1))*p26 - (((1*Y^2)/(X*Z)))*p117 - (((1*Y^2)/(X*Z)))*p169 - (((-1)))*p189 - ((1))*p223 - ((1))*p236 - (((1*Y^2)/(X*Z)))*p238 - ((((-1)*Y^2)/(X*W^2)))*p242 - ((((-1)*Y^2)/(X)))*p256 - ((1))*p257)*(1/((1)))

def rhsPivot259 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 208 - ((1))*rhsPivot18 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot40 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot118 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot119 X Y Z W a b r - ((1))*rhsPivot131 X Y Z W a b r - ((1))*rhsPivot200 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot239 X Y Z W a b r - (((1*Y^2)/(X*Z)))*rhsPivot241 X Y Z W a b r - (((1*Y^2)/(X)))*rhsPivot256 X Y Z W a b r - (((-1)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_259 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)))*v 42 + ((1))*v 399 + ((((-1))/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)))*v 435=rhsPivot259 X Y Z W a b r := by
  have h:=hv 208
  change ((1))*v 93 + (((1*Y^2)/(X*Z)))*v 136 + ((1))*v 195 + (((1*Y^2)/(X*Z)))*v 238 + ((1))*v 297 + (((1*Y^2)/(X*Z)))*v 340 + ((1))*v 399 + (((1*Y^2)/(X*Z)))*v 442=r 208 at h
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v r hv
  have p40:=pivot_40 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot259
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p18 - (((1*Y^2)/(X*Z)))*p40 - (((1*Y^2)/(X*Z)))*p118 - (((1*Y^2)/(X*Z)))*p119 - ((1))*p131 - ((1))*p200 - ((((-1)*Y^2)/(X*W^2)))*p239 - (((1*Y^2)/(X*Z)))*p241 - (((1*Y^2)/(X)))*p256 - (((-1)))*p257)*(1/((1)))

def rhsPivot260 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 266 - ((1))*rhsPivot73 X Y Z W a b r - ((1))*rhsPivot129 X Y Z W a b r - ((((-1))/(Y^2*Z)))*rhsPivot130 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot232 X Y Z W a b r - (((1)/(W^2)))*rhsPivot256 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_260 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 26 + ((((-1)*X)/(Y^2*W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)))*v 435=rhsPivot260 X Y Z W a b r := by
  have h:=hv 266
  change ((1))*v 13 + (((1)/(X)))*v 26 + ((1))*v 268=r 266 at h
  have p73:=pivot_73 X Y Z W a b hX hY hZ hW v r hv
  have p129:=pivot_129 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot260
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p73 - ((1))*p129 - ((((-1))/(Y^2*Z)))*p130 - (((1)/(X*Y^2*W^2)))*p232 - (((1)/(W^2)))*p256)*(1/(((1)/(X))))

def rhsPivot261 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 269 - ((1))*rhsPivot65 X Y Z W a b r - ((1))*rhsPivot114 X Y Z W a b r - (((1)/(W^2)))*rhsPivot235 X Y Z W a b r - (((1)/(X)))*rhsPivot252 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_261 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 42 + (((1*Y^2)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)))*v 435=rhsPivot261 X Y Z W a b r := by
  have h:=hv 269
  change ((1))*v 21 + (((1)/(X)))*v 42 + ((1))*v 276=r 269 at h
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot261
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p65 - ((1))*p114 - (((1)/(W^2)))*p235 - (((1)/(X)))*p252)*(1/(((1)/(X))))

def rhsPivot262 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 271 - ((1))*rhsPivot116 X Y Z W a b r - ((1))*rhsPivot126 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot236 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(W^2)))*rhsPivot257 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_262 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 48 + ((((-1))/(W^2)) + ((1*X)/(W^2)))*v 390 + (((1*X^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot262 X Y Z W a b r := by
  have h:=hv 271
  change ((1))*v 24 + (((1)/(X)))*v 48 + ((1))*v 279=r 271 at h
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot262
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p116 - ((1))*p126 - (((1*X)/(W^2)))*p236 - ((((-1)*Y^2)/(W^2)))*p256 - (((1)/(W^2)))*p257)*(1/(((1)/(X))))

def rhsPivot263 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 273 - ((1))*rhsPivot166 X Y Z W a b r - ((1))*rhsPivot170 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_263 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 54 + (((1*X*Y^2)/(W^2)))*v 70 + (((1)/(W^2)))*v 390=rhsPivot263 X Y Z W a b r := by
  have h:=hv 273
  change ((1))*v 27 + (((1)/(X)))*v 54 + ((1))*v 282=r 273 at h
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot263
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p166 - ((1))*p170)*(1/(((1)/(X))))

def rhsPivot264 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 277 - ((1))*rhsPivot142 X Y Z W a b r - ((1))*rhsPivot164 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot233 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot252 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_264 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 70 + ((1*X))*v 390 + (((1*X)/(Y^2)) + (1*X^2) + (((-1)*X^3)/(Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 435=rhsPivot264 X Y Z W a b r := by
  have h:=hv 277
  change ((1))*v 35 + (((1)/(X)))*v 70 + ((1))*v 290=r 277 at h
  have p142:=pivot_142 X Y Z W a b hX hY hZ hW v r hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot264
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p142 - ((1))*p164 - (((1)/(X*Y^2)))*p233 - (((1*W^2)/(Y^2)))*p252)*(1/(((1)/(X))))

def rhsPivot265 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 278 - ((1))*rhsPivot127 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_265 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 72 + ((1))*v 291 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)))*v 435=rhsPivot265 X Y Z W a b r := by
  have h:=hv 278
  change ((1))*v 36 + (((1)/(X)))*v 72 + ((1))*v 291=r 278 at h
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot265
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p127 - (((1*X)/(W^2)))*p198 - ((((-1))/(W^2)))*p230)*(1/((1)))

def rhsPivot266 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 279)/((1))

compact_elimination_proof
theorem pivot_266 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 37 + (((1)/(X)))*v 74 + ((1))*v 292=rhsPivot266 X Y Z W a b r := by
  have h:=hv 279
  change ((1))*v 37 + (((1)/(X)))*v 74 + ((1))*v 292=r 279 at h
  unfold rhsPivot266
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot267 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 280 - ((1))*rhsPivot153 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot205 X Y Z W a b r - ((((-1))/(X*W^2)) + (((-1)*Y^2)/(W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(X)))*rhsPivot252 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_267 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 294 + (((1*Y^2)/(X*W^2)))*v 390 + (((1*Y^2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)))*v 435=rhsPivot267 X Y Z W a b r := by
  have h:=hv 280
  change ((1))*v 39 + (((1)/(X)))*v 78 + ((1))*v 294=r 280 at h
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot267
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p153 - (((1*Y^2)/(X*W^2)))*p205 - ((((-1))/(X*W^2)) + (((-1)*Y^2)/(W^2)))*p230 - (((1)/(X)))*p252)*(1/((1)))

def rhsPivot268 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 281 - (((1)/(X)))*rhsPivot92 X Y Z W a b r - ((1))*rhsPivot149 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot256 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot257 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_268 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-1)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435 + ((1))*v 462=rhsPivot268 X Y Z W a b r := by
  have h:=hv 281
  change ((1))*v 40 + (((1)/(X)))*v 80 + ((1))*v 295=r 281 at h
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v r hv
  have p149:=pivot_149 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot268
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p92 - ((1))*p149 - (((1)/(Y^2)))*p189 - ((1))*p256 - ((((-1))/(Y^2)))*p257)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot269 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 212 - (((1)/(Z)))*rhsPivot10 X Y Z W a b r - (((1)/(Z)))*rhsPivot113 X Y Z W a b r - (((1)/(Z)))*rhsPivot120 X Y Z W a b r - (((1)/(Z)))*rhsPivot143 X Y Z W a b r - ((((-1)*X)/(W^2)))*rhsPivot194 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot195 X Y Z W a b r - (((1)/(W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot232 X Y Z W a b r - ((1))*rhsPivot263 X Y Z W a b r - ((((-1)*X*Y^2)/(W^2)))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot268 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_269 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 156 + ((((-2))/(W^2)) + ((1*X)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1)*X)/(2*W^2)) + ((-1)*X) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((2*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=rhsPivot269 X Y Z W a b r := by
  have h:=hv 212
  change (((1)/(Z)))*v 0 + ((1))*v 54 + (((1)/(Z)))*v 102 + ((1))*v 156 + (((1)/(Z)))*v 306 + ((1))*v 360 + (((1)/(Z)))*v 408 + ((1))*v 462=r 212 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot269
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Z)))*p10 - (((1)/(Z)))*p113 - (((1)/(Z)))*p120 - (((1)/(Z)))*p143 - ((((-1)*X)/(W^2)))*p194 - ((((-1))/(W^2)))*p195 - (((1)/(W^2)))*p230 - ((1))*p232 - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p268)*(1/((1)))

def rhsPivot270 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 282 - (((1)/(X)))*rhsPivot67 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot166 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_270 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 41 + ((1))*v 296 + (((1)/(X*Y^2*W^2)))*v 390=rhsPivot270 X Y Z W a b r := by
  have h:=hv 282
  change ((1))*v 41 + (((1)/(X)))*v 82 + ((1))*v 296=r 282 at h
  have p67:=pivot_67 X Y Z W a b hX hY hZ hW v r hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot270
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p67 - (((1)/(Y^2)))*p166)*(1/((1)))

def rhsPivot271 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 285 - (((1)/(X)))*rhsPivot56 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot78 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot196 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_271 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 44 + ((1))*v 299 + ((((-1))/(Y^2*W^2)))*v 390=rhsPivot271 X Y Z W a b r := by
  have h:=hv 285
  change ((1))*v 44 + (((1)/(X)))*v 88 + ((1))*v 299=r 285 at h
  have p56:=pivot_56 X Y Z W a b hX hY hZ hW v r hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot271
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p56 - (((1)/(X*W^2)))*p78 - (((1)/(Y^2*W^2)))*p196)*(1/((1)))

#print axioms pivot_271

def rhsPivot272 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 287 - (((1)/(X)))*rhsPivot96 X Y Z W a b r - (((1)/(W^2)))*rhsPivot202 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot262 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_272 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 303 + (((1)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot272 X Y Z W a b r := by
  have h:=hv 287
  change ((1))*v 48 + (((1)/(X)))*v 96 + ((1))*v 303=r 287 at h
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot272
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p96 - (((1)/(W^2)))*p202 - (((1)/(X*W^2)))*p230 - ((1))*p262)*(1/((1)))

def rhsPivot273 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 288 - (((1)/(X)))*rhsPivot98 X Y Z W a b r - ((1))*rhsPivot134 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot208 X Y Z W a b r - ((((-1)*X*W^2)/(Y^2*Z)))*rhsPivot231 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_273 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 305 + (((1)/(Y^2)))*v 390 + (((1*X)/(2*Y^2)) + ((1*X*a)/(2*Y)) + ((1*X)/(2)) + (((-1)*X^2)/(Y^2)))*v 435=rhsPivot273 X Y Z W a b r := by
  have h:=hv 288
  change ((1))*v 50 + (((1)/(X)))*v 100 + ((1))*v 305=r 288 at h
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot273
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p98 - ((1))*p134 - (((1)/(Y^2)))*p208 - ((((-1)*X*W^2)/(Y^2*Z)))*p231 - ((((-1))/(Y^2)))*p235)*(1/((1)))

def rhsPivot274 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 291 - ((1))*rhsPivot155 X Y Z W a b r - (((1)/(X)))*rhsPivot242 X Y Z W a b r - ((1))*rhsPivot246 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_274 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X*Y^2)/(W^2)))*v 140 + ((1))*v 222 + ((((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)))*v 435=rhsPivot274 X Y Z W a b r := by
  have h:=hv 291
  change ((1))*v 55 + (((1)/(X)))*v 110 + ((1))*v 310=r 291 at h
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot274
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p155 - (((1)/(X)))*p242 - ((1))*p246)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot275 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 292)/((1))

compact_elimination_proof
theorem pivot_275 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 57 + (((1)/(X)))*v 114 + ((1))*v 312=rhsPivot275 X Y Z W a b r := by
  have h:=hv 292
  change ((1))*v 57 + (((1)/(X)))*v 114 + ((1))*v 312=r 292 at h
  unfold rhsPivot275
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot276 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 294)/((1))

compact_elimination_proof
theorem pivot_276 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 63 + (((1)/(X)))*v 126 + ((1))*v 318=rhsPivot276 X Y Z W a b r := by
  have h:=hv 294
  change ((1))*v 63 + (((1)/(X)))*v 126 + ((1))*v 318=r 294 at h
  unfold rhsPivot276
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot277 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 295 - ((1))*rhsPivot89 X Y Z W a b r - ((1))*rhsPivot219 X Y Z W a b r - (((1)/(Y^2)) + (1*X))*rhsPivot230 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_277 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(W^2)))*v 130 + ((((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)))*v 435 + ((1))*v 438=rhsPivot277 X Y Z W a b r := by
  have h:=hv 295
  change ((1))*v 65 + (((1)/(X)))*v 130 + ((1))*v 320=r 295 at h
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v r hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot277
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p89 - ((1))*p219 - (((1)/(Y^2)) + (1*X))*p230)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot278 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 296 - ((1))*rhsPivot199 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_278 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 132 + (((-1)*X))*v 288 + ((1))*v 321=rhsPivot278 X Y Z W a b r := by
  have h:=hv 296
  change ((1))*v 66 + (((1)/(X)))*v 132 + ((1))*v 321=r 296 at h
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot278
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p199)*(1/((1)))

def rhsPivot279 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 297 - ((1))*rhsPivot220 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_279 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 69 + (((1)/(X)))*v 138 + (((-1)*X))*v 162=rhsPivot279 X Y Z W a b r := by
  have h:=hv 297
  change ((1))*v 69 + (((1)/(X)))*v 138 + ((1))*v 324=r 297 at h
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot279
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p220)*(1/((1)))

def rhsPivot280 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 299)/((1))

compact_elimination_proof
theorem pivot_280 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 71 + (((1)/(X)))*v 142 + ((1))*v 326=rhsPivot280 X Y Z W a b r := by
  have h:=hv 299
  change ((1))*v 71 + (((1)/(X)))*v 142 + ((1))*v 326=r 299 at h
  unfold rhsPivot280
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot281 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 300)/((1))

compact_elimination_proof
theorem pivot_281 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 72 + (((1)/(X)))*v 144 + ((1))*v 327=rhsPivot281 X Y Z W a b r := by
  have h:=hv 300
  change ((1))*v 72 + (((1)/(X)))*v 144 + ((1))*v 327=r 300 at h
  unfold rhsPivot281
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot282 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 301 - ((1))*rhsPivot247 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_282 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X))*v 74 + ((1))*v 148 + (((-1)*X))*v 159=rhsPivot282 X Y Z W a b r := by
  have h:=hv 301
  change ((1))*v 74 + (((1)/(X)))*v 148 + ((1))*v 329=r 301 at h
  have p247:=pivot_247 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot282
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p247)*(1/(((1)/(X))))

def rhsPivot283 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 303)/((1))

compact_elimination_proof
theorem pivot_283 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 77 + (((1)/(X)))*v 154 + ((1))*v 332=rhsPivot283 X Y Z W a b r := by
  have h:=hv 303
  change ((1))*v 77 + (((1)/(X)))*v 154 + ((1))*v 332=r 303 at h
  unfold rhsPivot283
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot284 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 304 - ((1))*rhsPivot252 X Y Z W a b r - (((1)/(X)))*rhsPivot269 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_284 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 333 + (((2)/(X*W^2)) + (((-1))/(W^2)) + ((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + (((1)/(2*W^2)) + (1) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-5)*X)/(2*W^2)) + ((1*X)/(2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot284 X Y Z W a b r := by
  have h:=hv 304
  change ((1))*v 78 + (((1)/(X)))*v 156 + ((1))*v 333=r 304 at h
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot284
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p252 - (((1)/(X)))*p269)*(1/((1)))

def rhsPivot285 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 305)/((1))

compact_elimination_proof
theorem pivot_285 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 79 + (((1)/(X)))*v 158 + ((1))*v 334=rhsPivot285 X Y Z W a b r := by
  have h:=hv 305
  change ((1))*v 79 + (((1)/(X)))*v 158 + ((1))*v 334=r 305 at h
  unfold rhsPivot285
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot286 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 308 - ((1))*rhsPivot67 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot166 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_286 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 164 + ((1))*v 337 + (((1)/(Y^2*W^2)))*v 390=rhsPivot286 X Y Z W a b r := by
  have h:=hv 308
  change ((1))*v 82 + (((1)/(X)))*v 164 + ((1))*v 337=r 308 at h
  have p67:=pivot_67 X Y Z W a b hX hY hZ hW v r hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot286
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p67 - (((1*X)/(Y^2)))*p166)*(1/((1)))

def rhsPivot287 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 309 - ((1))*rhsPivot68 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot127 X Y Z W a b r - ((1))*rhsPivot191 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(X*Y^2*W^2)))*rhsPivot230 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_287 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 166 + (((-1)*X))*v 168 + (((1*X)/(2*Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X)/(2*W^2)))*v 435=rhsPivot287 X Y Z W a b r := by
  have h:=hv 309
  change ((1))*v 83 + (((1)/(X)))*v 166 + ((1))*v 338=r 309 at h
  have p68:=pivot_68 X Y Z W a b hX hY hZ hW v r hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v r hv
  have p191:=pivot_191 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot287
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p68 - (((1)/(X*Y^2)))*p127 - ((1))*p191 - (((1)/(Y^2*W^2)))*p198 - ((((-1))/(X*Y^2*W^2)))*p230)*(1/(((1)/(X))))

#print axioms pivot_287

def rhsPivot288 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 313 - ((1))*rhsPivot55 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_288 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 174 + ((1*X))*v 342 + (((1*X)/(W^2)))*v 435=rhsPivot288 X Y Z W a b r := by
  have h:=hv 313
  change ((1))*v 87 + (((1)/(X)))*v 174 + ((1))*v 342=r 313 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot288
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p55)*(1/(((1)/(X))))

def rhsPivot289 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 314 - ((1))*rhsPivot56 X Y Z W a b r - (((1)/(W^2)))*rhsPivot78 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot196 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_289 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 176 + ((1))*v 343 + ((((-1)*X)/(Y^2*W^2)))*v 390=rhsPivot289 X Y Z W a b r := by
  have h:=hv 314
  change ((1))*v 88 + (((1)/(X)))*v 176 + ((1))*v 343=r 314 at h
  have p56:=pivot_56 X Y Z W a b hX hY hZ hW v r hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot289
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p56 - (((1)/(W^2)))*p78 - (((1*X)/(Y^2*W^2)))*p196)*(1/((1)))

def rhsPivot290 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 315 - ((1))*rhsPivot79 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot232 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_290 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 178 + ((1))*v 344 + ((((-1))/(Y^2*W^2)) + (((-1)*X)/(2*Y^2*W^2)) + (((-1)*X*a)/(2*Y*W^2)) + (((-1)*X)/(2*W^2)))*v 435=rhsPivot290 X Y Z W a b r := by
  have h:=hv 315
  change ((1))*v 89 + (((1)/(X)))*v 178 + ((1))*v 344=r 315 at h
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot290
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p79 - (((1)/(X*Y^2*W^2)))*p232)*(1/((1)))

def rhsPivot291 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 321 - ((1))*rhsPivot96 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot202 X Y Z W a b r - (((1)/(W^2)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_291 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 192 + ((1))*v 351 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)))*v 435=rhsPivot291 X Y Z W a b r := by
  have h:=hv 321
  change ((1))*v 96 + (((1)/(X)))*v 192 + ((1))*v 351=r 321 at h
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot291
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p96 - (((1*X)/(W^2)))*p202 - (((1)/(W^2)))*p230)*(1/((1)))

def rhsPivot292 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 322)/((1))

compact_elimination_proof
theorem pivot_292 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 98 + (((1)/(X)))*v 196 + ((1))*v 353=rhsPivot292 X Y Z W a b r := by
  have h:=hv 322
  change ((1))*v 98 + (((1)/(X)))*v 196 + ((1))*v 353=r 322 at h
  unfold rhsPivot292
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot293 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 323 - ((1))*rhsPivot97 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_293 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 198 + ((1))*v 354 + (((1*Y^2)/(X*W^2)))*v 370=rhsPivot293 X Y Z W a b r := by
  have h:=hv 323
  change ((1))*v 99 + (((1)/(X)))*v 198 + ((1))*v 354=r 323 at h
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot293
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p97)*(1/((1)))

def rhsPivot294 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 324 - ((1))*rhsPivot98 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot208 X Y Z W a b r - (((1)/(X)))*rhsPivot227 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_294 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 355 + ((((-1))/(X)))*v 370 + (((1*X)/(Y^2)))*v 390=rhsPivot294 X Y Z W a b r := by
  have h:=hv 324
  change ((1))*v 100 + (((1)/(X)))*v 200 + ((1))*v 355=r 324 at h
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot294
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p98 - (((1*X)/(Y^2)))*p208 - (((1)/(X)))*p227 - ((((-1)*X)/(Y^2)))*p235)*(1/((1)))

def rhsPivot295 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 325)/((1))

compact_elimination_proof
theorem pivot_295 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 101 + (((1)/(X)))*v 202 + ((1))*v 356=rhsPivot295 X Y Z W a b r := by
  have h:=hv 325
  change ((1))*v 101 + (((1)/(X)))*v 202 + ((1))*v 356=r 325 at h
  unfold rhsPivot295
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot296 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 326)/((1))

compact_elimination_proof
theorem pivot_296 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 107 + (((1)/(X)))*v 214 + ((1))*v 362=rhsPivot296 X Y Z W a b r := by
  have h:=hv 326
  change ((1))*v 107 + (((1)/(X)))*v 214 + ((1))*v 362=r 326 at h
  unfold rhsPivot296
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot297 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 327)/((1))

compact_elimination_proof
theorem pivot_297 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 108 + (((1)/(X)))*v 216 + ((1))*v 363=rhsPivot297 X Y Z W a b r := by
  have h:=hv 327
  change ((1))*v 108 + (((1)/(X)))*v 216 + ((1))*v 363=r 327 at h
  unfold rhsPivot297
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot298 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 329 - (((1)/(X)))*rhsPivot180 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_298 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 114 + ((1))*v 369 + (((1*Y^2)/(X*W^2)))*v 440=rhsPivot298 X Y Z W a b r := by
  have h:=hv 329
  change ((1))*v 114 + (((1)/(X)))*v 228 + ((1))*v 369=r 329 at h
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot298
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p180)*(1/((1)))

def rhsPivot299 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 330 - ((1))*rhsPivot101 X Y Z W a b r - (((1)/(X)))*rhsPivot156 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot194 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_299 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X*Y^2)/(W^2)))*v 370 + ((1))*v 402 + ((((-1)*X)/(W^2)))*v 435=rhsPivot299 X Y Z W a b r := by
  have h:=hv 330
  change ((1))*v 115 + (((1)/(X)))*v 230 + ((1))*v 370=r 330 at h
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v r hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot299
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p101 - (((1)/(X)))*p156 - (((1)/(Y^2)))*p194)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot300 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 332 - (((1)/(X)))*rhsPivot158 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_300 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 117 + ((1))*v 372 + (((1)/(X*W^2)))*v 390=rhsPivot300 X Y Z W a b r := by
  have h:=hv 332
  change ((1))*v 117 + (((1)/(X)))*v 234 + ((1))*v 372=r 332 at h
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot300
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p158)*(1/((1)))

def rhsPivot301 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 346 - (((1)/(X)))*rhsPivot114 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_301 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 138 + ((((-1))/(X*W^2)))*v 390 + ((1))*v 393=rhsPivot301 X Y Z W a b r := by
  have h:=hv 346
  change ((1))*v 138 + (((1)/(X)))*v 276 + ((1))*v 393=r 346 at h
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot301
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p114 - (((1)/(X*W^2)))*p235)*(1/((1)))

def rhsPivot302 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 348 - (((1)/(X)))*rhsPivot62 X Y Z W a b r - ((1))*rhsPivot100 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_302 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 108 + (((1*X*Y^2)/(W^2)))*v 140 + (((1*X)/(W^2)))*v 435=rhsPivot302 X Y Z W a b r := by
  have h:=hv 348
  change ((1))*v 140 + (((1)/(X)))*v 280 + ((1))*v 395=r 348 at h
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v r hv
  have p100:=pivot_100 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot302
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p62 - ((1))*p100)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot303 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 355)/((1))

compact_elimination_proof
theorem pivot_303 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 154 + (((1)/(X)))*v 308 + ((1))*v 409=rhsPivot303 X Y Z W a b r := by
  have h:=hv 355
  change ((1))*v 154 + (((1)/(X)))*v 308 + ((1))*v 409=r 355 at h
  unfold rhsPivot303
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_303

def rhsPivot304 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 356 - ((1))*rhsPivot78 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot196 X Y Z W a b r - (((1)/(X)))*rhsPivot246 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_304 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X)))*v 140 + ((1))*v 155 + ((((-1)*X)/(Y^2)))*v 390=rhsPivot304 X Y Z W a b r := by
  have h:=hv 356
  change ((1))*v 155 + (((1)/(X)))*v 310 + ((1))*v 410=r 356 at h
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot304
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p78 - (((1*X)/(Y^2)))*p196 - (((1)/(X)))*p246)*(1/((1)))

def rhsPivot305 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 358)/((1))

compact_elimination_proof
theorem pivot_305 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 157 + (((1)/(X)))*v 314 + ((1))*v 412=rhsPivot305 X Y Z W a b r := by
  have h:=hv 358
  change ((1))*v 157 + (((1)/(X)))*v 314 + ((1))*v 412=r 358 at h
  unfold rhsPivot305
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot306 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 359 - ((1))*rhsPivot104 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_306 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 159 + (((1)/(X)))*v 318 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)))*v 435=rhsPivot306 X Y Z W a b r := by
  have h:=hv 359
  change ((1))*v 159 + (((1)/(X)))*v 318 + ((1))*v 414=r 359 at h
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot306
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p104 - (((1*X)/(W^2)))*p198 - ((((-1))/(W^2)))*p230)*(1/((1)))

def rhsPivot307 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 364 - ((1))*rhsPivot107 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot233 X Y Z W a b r - ((1))*rhsPivot287 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_307 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X^2))*v 168 + ((1))*v 332 + (((1*X)/(Y^2*W^2)))*v 435=rhsPivot307 X Y Z W a b r := by
  have h:=hv 364
  change ((1))*v 166 + (((1)/(X)))*v 332 + ((1))*v 421=r 364 at h
  have p107:=pivot_107 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p287:=pivot_287 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot307
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p107 - (((1)/(X*Y^2*W^2)))*p233 - ((1))*p287)*(1/(((1)/(X))))

def rhsPivot308 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 365 - ((1))*rhsPivot57 X Y Z W a b r - (((1)/(W^2)))*rhsPivot98 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot208 X Y Z W a b r - ((((-1)*X)/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_308 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 167 + (((1)/(X)))*v 334 + (((1*X)/(Y^2*W^2)))*v 390=rhsPivot308 X Y Z W a b r := by
  have h:=hv 365
  change ((1))*v 167 + (((1)/(X)))*v 334 + ((1))*v 422=r 365 at h
  have p57:=pivot_57 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot308
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p57 - (((1)/(W^2)))*p98 - (((1*X)/(Y^2*W^2)))*p208 - ((((-1)*X)/(Y^2*W^2)))*p235)*(1/((1)))

def rhsPivot309 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 366 - ((1))*rhsPivot54 X Y Z W a b r - (((1)/(W^2)))*rhsPivot194 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_309 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1*X))*v 168 + ((1))*v 336 + ((((-1)*X)/(W^2)))*v 435=rhsPivot309 X Y Z W a b r := by
  have h:=hv 366
  change ((1))*v 168 + (((1)/(X)))*v 336 + ((1))*v 423=r 366 at h
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot309
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p54 - (((1)/(W^2)))*p194)*(1/(((1)/(X))))

def rhsPivot310 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 307 - ((1))*rhsPivot66 X Y Z W a b r - (((1)/(X)))*rhsPivot126 X Y Z W a b r - (((1)/(W^2)))*rhsPivot236 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot309 X Y Z W a b r)/(((-1)*X))

compact_elimination_proof
theorem pivot_310 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X^2)))*v 162 + ((1))*v 168 + ((((-1))/(X^2*W^2)))*v 390=rhsPivot310 X Y Z W a b r := by
  have h:=hv 307
  change ((1))*v 81 + (((1)/(X)))*v 162 + ((1))*v 336=r 307 at h
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot310
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p66 - (((1)/(X)))*p126 - (((1)/(W^2)))*p236 - ((((-1)*Y^2)/(X*W^2)))*p256 - ((1))*p309)*(1/(((-1)*X)))

def rhsPivot311 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 370 - ((1))*rhsPivot122 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot152 X Y Z W a b r - ((1))*rhsPivot190 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot202 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(X)))*rhsPivot290 X Y Z W a b r)/((((-1))/(X^2)))

compact_elimination_proof
theorem pivot_311 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 178 + ((1*X^2))*v 342 + ((((-1)*X)/(Y^2*W^2)))*v 435=rhsPivot311 X Y Z W a b r := by
  have h:=hv 370
  change ((1))*v 172 + (((1)/(X)))*v 344 + ((1))*v 427=r 370 at h
  have p122:=pivot_122 X Y Z W a b hX hY hZ hW v r hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v r hv
  have p190:=pivot_190 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p290:=pivot_290 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot311
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p122 - (((1)/(X*Y^2)))*p152 - ((1))*p190 - (((1)/(Y^2*W^2)))*p202 - (((1)/(X*Y^2*W^2)))*p230 - (((1)/(X)))*p290)*(1/((((-1))/(X^2))))

def rhsPivot312 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 371 - ((1))*rhsPivot123 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_312 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 173 + (((1)/(X)))*v 346 + ((((-1))/(Y^2*W^2)))*v 390=rhsPivot312 X Y Z W a b r := by
  have h:=hv 371
  change ((1))*v 173 + (((1)/(X)))*v 346 + ((1))*v 428=r 371 at h
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot312
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p123 - (((1)/(Y^2*W^2)))*p235)*(1/((1)))

def rhsPivot313 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 372 - ((1))*rhsPivot87 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot288 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_313 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)*X^2))*v 342 + ((1))*v 348 + ((((-1))/(W^2)))*v 390=rhsPivot313 X Y Z W a b r := by
  have h:=hv 372
  change ((1))*v 174 + (((1)/(X)))*v 348 + ((1))*v 429=r 372 at h
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot313
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p87 - (((1*Y^2)/(X*W^2)))*p256 - ((1))*p288)*(1/(((1)/(X))))

def rhsPivot314 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 374)/((1))

compact_elimination_proof
theorem pivot_314 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 176 + (((1)/(X)))*v 352 + ((1))*v 431=rhsPivot314 X Y Z W a b r := by
  have h:=hv 374
  change ((1))*v 176 + (((1)/(X)))*v 352 + ((1))*v 431=r 374 at h
  unfold rhsPivot314
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot315 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 379)/((1))

compact_elimination_proof
theorem pivot_315 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 184 + (((1)/(X)))*v 368 + ((1))*v 439=rhsPivot315 X Y Z W a b r := by
  have h:=hv 379
  change ((1))*v 184 + (((1)/(X)))*v 368 + ((1))*v 439=r 379 at h
  unfold rhsPivot315
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot316 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 380)/((1))

compact_elimination_proof
theorem pivot_316 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 185 + (((1)/(X)))*v 370 + ((1))*v 440=rhsPivot316 X Y Z W a b r := by
  have h:=hv 380
  change ((1))*v 185 + (((1)/(X)))*v 370 + ((1))*v 440=r 380 at h
  unfold rhsPivot316
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot317 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 384 - ((1))*rhsPivot90 X Y Z W a b r - ((1))*rhsPivot205 X Y Z W a b r - ((((-1))/(Y^2)) + ((-1)*X))*rhsPivot230 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_317 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*W^2)/(Y^2)))*v 72 + ((1))*v 380 + (((1*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot317 X Y Z W a b r := by
  have h:=hv 384
  change ((1))*v 190 + (((1)/(X)))*v 380 + ((1))*v 445=r 384 at h
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot317
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p90 - ((1))*p205 - ((((-1))/(Y^2)) + ((-1)*X))*p230)*(1/(((1)/(X))))

def rhsPivot318 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 385)/((1))

compact_elimination_proof
theorem pivot_318 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 192 + (((1)/(X)))*v 384 + ((1))*v 447=rhsPivot318 X Y Z W a b r := by
  have h:=hv 385
  change ((1))*v 192 + (((1)/(X)))*v 384 + ((1))*v 447=r 385 at h
  unfold rhsPivot318
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot319 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 386)/((1))

compact_elimination_proof
theorem pivot_319 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 198 + (((1)/(X)))*v 396 + ((1))*v 453=rhsPivot319 X Y Z W a b r := by
  have h:=hv 386
  change ((1))*v 198 + (((1)/(X)))*v 396 + ((1))*v 453=r 386 at h
  unfold rhsPivot319
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

#print axioms pivot_319

def rhsPivot320 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 387 - ((1))*rhsPivot148 X Y Z W a b r - ((1))*rhsPivot227 X Y Z W a b r - (((1)/(X)))*rhsPivot239 X Y Z W a b r)/(((1*W^2)/(X*Y^2)))

compact_elimination_proof
theorem pivot_320 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 288 + ((((-1)*X*Y^2)/(W^2)))*v 370 + (((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)))*v 435=rhsPivot320 X Y Z W a b r := by
  have h:=hv 387
  change ((1))*v 200 + (((1)/(X)))*v 400 + ((1))*v 455=r 387 at h
  have p148:=pivot_148 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot320
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p148 - ((1))*p227 - (((1)/(X)))*p239)*(1/(((1*W^2)/(X*Y^2))))

def rhsPivot321 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 389 - (((1)/(X)))*rhsPivot78 X Y Z W a b r - ((1))*rhsPivot136 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot196 X Y Z W a b r - ((((-1)*X*W^2)/(Y^2*Z)))*rhsPivot234 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_321 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 205 + ((((-1))/(Y^2)))*v 390 + ((((-1)*X)/(2*Y^2)) + (((-1)*X*a)/(2*Y)) + (((-1)*X)/(2)) + ((1*X^2)/(Y^2)))*v 435=rhsPivot321 X Y Z W a b r := by
  have h:=hv 389
  change ((1))*v 205 + (((1)/(X)))*v 410 + ((1))*v 460=r 389 at h
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot321
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p78 - ((1))*p136 - (((1)/(Y^2)))*p196 - ((((-1)*X*W^2)/(Y^2*Z)))*p234)*(1/((1)))

def rhsPivot322 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 390 - (((1)/(X)))*rhsPivot104 X Y Z W a b r - (((1)/(W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot268 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_322 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 207 + ((((-1))/(W^2)) + ((1*X)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot322 X Y Z W a b r := by
  have h:=hv 390
  change ((1))*v 207 + (((1)/(X)))*v 414 + ((1))*v 462=r 390 at h
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot322
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p104 - (((1)/(W^2)))*p198 - ((((-1))/(X*W^2)))*p230 - ((1))*p268)*(1/((1)))

def rhsPivot323 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 392 - (((1)/(X)))*rhsPivot57 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot98 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot208 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_323 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 211 + (((1)/(Y^2*W^2)))*v 390 + ((1))*v 466=rhsPivot323 X Y Z W a b r := by
  have h:=hv 392
  change ((1))*v 211 + (((1)/(X)))*v 422 + ((1))*v 466=r 392 at h
  have p57:=pivot_57 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot323
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p57 - (((1)/(X*W^2)))*p98 - (((1)/(Y^2*W^2)))*p208 - ((((-1))/(Y^2*W^2)))*p235)*(1/((1)))

def rhsPivot324 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 395 - (((1)/(X)))*rhsPivot123 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot235 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_324 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 214 + ((((-1))/(X*Y^2*W^2)))*v 390 + ((1))*v 469=rhsPivot324 X Y Z W a b r := by
  have h:=hv 395
  change ((1))*v 214 + (((1)/(X)))*v 428 + ((1))*v 469=r 395 at h
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot324
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p123 - (((1)/(X*Y^2*W^2)))*p235)*(1/((1)))

def rhsPivot325 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 396 - (((1)/(X)))*rhsPivot124 X Y Z W a b r - ((1))*rhsPivot151 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot219 X Y Z W a b r - (((1)/(X*W^2)) + ((1*Y^2)/(W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot253 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_325 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 216 + ((((-1)*Y^2)/(X*W^2)))*v 390 + ((((-1)*Y^2)/(W^2)) + ((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)))*v 435=rhsPivot325 X Y Z W a b r := by
  have h:=hv 396
  change ((1))*v 216 + (((1)/(X)))*v 432 + ((1))*v 471=r 396 at h
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v r hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v r hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot325
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p124 - ((1))*p151 - (((1*Y^2)/(X*W^2)))*p219 - (((1)/(X*W^2)) + ((1*Y^2)/(W^2)))*p230 - ((1))*p253)*(1/((1)))

def rhsPivot326 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 397)/((1))

compact_elimination_proof
theorem pivot_326 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 218 + (((1)/(X)))*v 436 + ((1))*v 473=rhsPivot326 X Y Z W a b r := by
  have h:=hv 397
  change ((1))*v 218 + (((1)/(X)))*v 436 + ((1))*v 473=r 397 at h
  unfold rhsPivot326
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h)*(1/((1)))

def rhsPivot327 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 398 - ((1))*rhsPivot152 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot202 X Y Z W a b r - (((1)/(W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(X)))*rhsPivot277 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_327 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)))*v 130 + ((1))*v 219 + (((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)))*v 435=rhsPivot327 X Y Z W a b r := by
  have h:=hv 398
  change ((1))*v 219 + (((1)/(X)))*v 438 + ((1))*v 474=r 398 at h
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot327
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p152 - (((1*X)/(W^2)))*p202 - (((1)/(W^2)))*p230 - (((1)/(X)))*p277)*(1/((1)))

def rhsPivot328 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 399 - ((1))*rhsPivot111 X Y Z W a b r - ((1))*rhsPivot144 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot232 X Y Z W a b r - (((1*X*W^2)/(Y^2)))*rhsPivot253 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_328 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)*X))*v 390 + ((((-1)*X)/(Y^2)) + ((-1)*X^2) + ((1*X^3)/(Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2)))*v 435 + ((1))*v 440=rhsPivot328 X Y Z W a b r := by
  have h:=hv 399
  change ((1))*v 220 + (((1)/(X)))*v 440 + ((1))*v 475=r 399 at h
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v r hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot328
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p111 - ((1))*p144 - (((1)/(X*Y^2)))*p232 - (((1*X*W^2)/(Y^2)))*p253)*(1/(((1)/(X))))

def rhsPivot329 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 247 - ((1))*rhsPivot1 X Y Z W a b r - ((1))*rhsPivot21 X Y Z W a b r - ((1))*rhsPivot31 X Y Z W a b r - ((1))*rhsPivot43 X Y Z W a b r - ((1))*rhsPivot60 X Y Z W a b r - ((1))*rhsPivot62 X Y Z W a b r - ((1))*rhsPivot64 X Y Z W a b r - ((1))*rhsPivot78 X Y Z W a b r - ((1))*rhsPivot88 X Y Z W a b r - ((1))*rhsPivot92 X Y Z W a b r - ((1))*rhsPivot93 X Y Z W a b r - ((1))*rhsPivot98 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot126 X Y Z W a b r - ((1))*rhsPivot134 X Y Z W a b r - ((1))*rhsPivot136 X Y Z W a b r - ((1))*rhsPivot144 X Y Z W a b r - ((1))*rhsPivot156 X Y Z W a b r - ((1))*rhsPivot164 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot192 X Y Z W a b r - ((1))*rhsPivot193 X Y Z W a b r - (((2*X)/(Y^2)))*rhsPivot194 X Y Z W a b r - (((-1)))*rhsPivot195 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot196 X Y Z W a b r - ((1))*rhsPivot205 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot208 X Y Z W a b r - ((1))*rhsPivot219 X Y Z W a b r - ((1))*rhsPivot227 X Y Z W a b r - ((((-1)*X*W^2)/(Y^2*Z)))*rhsPivot231 X Y Z W a b r - ((((-1)*X*W^2)/(Y^2*Z)))*rhsPivot234 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot235 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot236 X Y Z W a b r - ((1))*rhsPivot239 X Y Z W a b r - ((1))*rhsPivot242 X Y Z W a b r - ((1))*rhsPivot246 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot252 X Y Z W a b r - (((1*X*W^2)/(Y^2)))*rhsPivot253 X Y Z W a b r - ((1))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot317 X Y Z W a b r - ((1))*rhsPivot328 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_329 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*W^2)/(Y^2)))*v 72 + ((1))*v 130 + ((((-1)*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot329 X Y Z W a b r := by
  have h:=hv 247
  change ((1))*v 10 + ((1))*v 20 + ((1))*v 40 + ((1))*v 50 + ((1))*v 70 + ((1))*v 80 + ((1))*v 100 + ((1))*v 110 + ((1))*v 130 + ((1))*v 140 + ((1))*v 160 + ((1))*v 190 + ((1))*v 200 + ((1))*v 220 + ((1))*v 230 + ((1))*v 250 + ((1))*v 260 + ((1))*v 280 + ((1))*v 290 + ((1))*v 310 + ((1))*v 320 + ((1))*v 350 + ((1))*v 370 + ((1))*v 380 + ((1))*v 400 + ((1))*v 410 + ((1))*v 430 + ((1))*v 440 + ((1))*v 460 + ((1))*v 470 + ((1))*v 490 + ((1))*v 500=r 247 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v r hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v r hv
  have p31:=pivot_31 X Y Z W a b hX hY hZ hW v r hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v r hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v r hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v r hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v r hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v r hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p134:=pivot_134 X Y Z W a b hX hY hZ hW v r hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v r hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v r hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v r hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v r hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot329
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p1 - ((1))*p21 - ((1))*p31 - ((1))*p43 - ((1))*p60 - ((1))*p62 - ((1))*p64 - ((1))*p78 - ((1))*p88 - ((1))*p92 - ((1))*p93 - ((1))*p98 - (((1*W^2)/(Y^2)))*p126 - ((1))*p134 - ((1))*p136 - ((1))*p144 - ((1))*p156 - ((1))*p164 - (((1*X)/(Y^2)))*p189 - ((1))*p192 - ((1))*p193 - (((2*X)/(Y^2)))*p194 - (((-1)))*p195 - (((1*X)/(Y^2)))*p196 - ((1))*p205 - (((1*X)/(Y^2)))*p208 - ((1))*p219 - ((1))*p227 - ((((-1)*X*W^2)/(Y^2*Z)))*p231 - ((((-1)*X*W^2)/(Y^2*Z)))*p234 - ((((-1)*X)/(Y^2)))*p235 - (((1*X)/(Y^2)))*p236 - ((1))*p239 - ((1))*p242 - ((1))*p246 - (((1*W^2)/(Y^2)))*p252 - (((1*X*W^2)/(Y^2)))*p253 - ((1))*p264 - ((1))*p317 - ((1))*p328)*(1/((1)))

def rhsPivot330 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 378 - ((1))*rhsPivot277 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot329 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_330 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)))*v 72 + ((1))*v 183 + (((1)/(X)))*v 366=rhsPivot330 X Y Z W a b r := by
  have h:=hv 378
  change ((1))*v 183 + (((1)/(X)))*v 366 + ((1))*v 438=r 378 at h
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot330
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p277 - ((((-1)*Y^2)/(W^2)))*p329)*(1/((1)))

def rhsPivot331 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 403 - ((1))*rhsPivot74 X Y Z W a b r - (((1)/(X)))*rhsPivot114 X Y Z W a b r - ((1))*rhsPivot180 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot235 X Y Z W a b r - (((1*Y^2)/(W^2)))*rhsPivot328 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_331 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + (((1*X^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435 + ((1))*v 456=rhsPivot331 X Y Z W a b r := by
  have h:=hv 403
  change ((1))*v 228 + (((1)/(X)))*v 456 + ((1))*v 483=r 403 at h
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot331
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p74 - (((1)/(X)))*p114 - ((1))*p180 - (((1)/(X*W^2)))*p235 - (((1*Y^2)/(W^2)))*p328)*(1/(((1)/(X))))

def rhsPivot332 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 405 - ((1))*rhsPivot158 X Y Z W a b r - ((1))*rhsPivot253 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_332 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(W^2)) + ((1*X)/(W^2)))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)))*v 435 + ((1))*v 468=rhsPivot332 X Y Z W a b r := by
  have h:=hv 405
  change ((1))*v 234 + (((1)/(X)))*v 468 + ((1))*v 489=r 405 at h
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot332
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p158 - ((1))*p253)*(1/(((1)/(X))))

def rhsPivot333 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 408 - ((1))*rhsPivot61 X Y Z W a b r - ((1))*rhsPivot160 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot233 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot256 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_333 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X)/(Y^2*W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^3)/(Y^2*W^2)))*v 435 + ((1))*v 484=rhsPivot333 X Y Z W a b r := by
  have h:=hv 408
  change ((1))*v 242 + (((1)/(X)))*v 484 + ((1))*v 497=r 408 at h
  have p61:=pivot_61 X Y Z W a b hX hY hZ hW v r hv
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot333
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p61 - ((1))*p160 - (((1)/(X*Y^2*W^2)))*p233 - (((1*X)/(Y^2*W^2)))*p236 - ((((-1))/(W^2)))*p256)*(1/(((1)/(X))))

def rhsPivot334 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 417 - ((((-1)*a)/(Y)))*rhsPivot126 X Y Z W a b r - ((1))*rhsPivot140 X Y Z W a b r - ((((-1)*X*a)/(Y*W^2)))*rhsPivot236 X Y Z W a b r - (((1*Y*a)/(W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot311 X Y Z W a b r - ((1))*rhsPivot313 X Y Z W a b r)/(((1)/(Y^2)))

compact_elimination_proof
theorem pivot_334 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 72 + (((1)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)))*v 390 + (((1*X)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*v 435=rhsPivot334 X Y Z W a b r := by
  have h:=hv 417
  change ((1))*v 8 + ((((-1)*a)/(Y)))*v 24 + (((1)/(Y^2)))*v 72 + ((1))*v 178 + ((1))*v 348=r 417 at h
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p140:=pivot_140 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p311:=pivot_311 X Y Z W a b hX hY hZ hW v r hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot334
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p126 - ((1))*p140 - ((((-1)*X*a)/(Y*W^2)))*p236 - (((1*Y*a)/(W^2)))*p256 - ((1))*p311 - ((1))*p313)*(1/(((1)/(Y^2))))

def rhsPivot335 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 456 - ((1))*rhsPivot106 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot158 X Y Z W a b r - ((1))*rhsPivot177 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot233 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((1))*rhsPivot252 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot256 X Y Z W a b r)/(((1)/(Y^2)))

compact_elimination_proof
theorem pivot_335 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 192 + (((1)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^4)/(W^2)))*v 390 + (((1*X)/(W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)))*v 435=rhsPivot335 X Y Z W a b r := by
  have h:=hv 456
  change ((1))*v 78 + (((1)/(Y^2)))*v 192 + ((((-1)*a)/(Y)))*v 234 + ((1))*v 248 + ((1))*v 418=r 456 at h
  have p106:=pivot_106 X Y Z W a b hX hY hZ hW v r hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v r hv
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot335
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p106 - ((((-1)*a)/(Y)))*p158 - ((1))*p177 - (((1)/(Y^2*W^2)))*p233 - (((1*X)/(Y^2*W^2)))*p236 - ((1))*p252 - ((((-1))/(W^2)))*p256)*(1/(((1)/(Y^2))))

#print axioms pivot_335

def rhsPivot336 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 463 - ((1))*rhsPivot81 X Y Z W a b r - ((1))*rhsPivot94 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot111 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot114 X Y Z W a b r - ((1))*rhsPivot124 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot131 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot235 X Y Z W a b r - ((1*X))*rhsPivot253 X Y Z W a b r - (((1)/(W^2)))*rhsPivot256 X Y Z W a b r)/(((1)/(Y^2)))

compact_elimination_proof
theorem pivot_336 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 318 + ((((-1))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)))*v 390 + ((((-1)*X)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)))*v 435=rhsPivot336 X Y Z W a b r := by
  have h:=hv 463
  change ((1))*v 92 + ((1))*v 262 + ((((-1)*a)/(Y)))*v 276 + (((1)/(Y^2)))*v 318 + ((1))*v 432=r 463 at h
  have p81:=pivot_81 X Y Z W a b hX hY hZ hW v r hv
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v r hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot336
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p81 - ((1))*p94 - (((1*X)/(W^2)))*p111 - ((((-1)*a)/(Y)))*p114 - ((1))*p124 - (((1*X)/(Y^2*W^2)))*p131 - (((1)/(Y^2*W^2)))*p232 - ((((-1)*a)/(Y*W^2)))*p235 - ((1*X))*p253 - (((1)/(W^2)))*p256)*(1/(((1)/(Y^2))))

def rhsPivot337 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 480 - ((((-1)*a)/(Y)))*rhsPivot54 X Y Z W a b r - ((1))*rhsPivot112 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot163 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot194 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot230 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_337 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 141 + ((1))*v 311 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + (((-1))/(2*W^2)))*v 435=rhsPivot337 X Y Z W a b r := by
  have h:=hv 480
  change ((1))*v 141 + (((1)/(Y^2)))*v 249 + ((1))*v 311 + ((((-1)*a)/(Y)))*v 423 + ((1))*v 481=r 480 at h
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v r hv
  have p112:=pivot_112 X Y Z W a b hX hY hZ hW v r hv
  have p163:=pivot_163 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot337
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p54 - ((1))*p112 - (((1)/(Y^2)))*p163 - ((((-1)*a)/(Y*W^2)))*p194 - (((1)/(X*Y^2*W^2)))*p230)*(1/((1)))

def rhsPivot338 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 495 - ((1))*rhsPivot4 X Y Z W a b r - ((1))*rhsPivot70 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot77 X Y Z W a b r - (((1)/(W^2)))*rhsPivot150 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*X)/(W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot325 X Y Z W a b r - ((1))*rhsPivot336 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_338 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 114 + (((1*Y^2)/(X*W^2)) + ((2)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^4)/(W^2)))*v 390 + (((1*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(W^2)) + (((-3)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot338 X Y Z W a b r := by
  have h:=hv 495
  change ((1))*v 12 + ((((-1)*b)/(W)))*v 60 + ((1))*v 114 + ((1))*v 216 + (((1)/(W^2)))*v 300 + ((1))*v 318 + ((1))*v 420=r 495 at h
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p325:=pivot_325 X Y Z W a b hX hY hZ hW v r hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot338
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p4 - ((1))*p70 - ((((-1)*b)/(W)))*p77 - (((1)/(W^2)))*p150 - (((1*X)/(W^2)))*p189 - ((((-1)*X)/(W^2)))*p257 - ((1))*p325 - ((1))*p336)*(1/((1)))

def rhsPivot339 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 429 - ((((-1)*a)/(Y)))*rhsPivot55 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot80 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot91 X Y Z W a b r - ((1))*rhsPivot172 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot194 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot195 X Y Z W a b r - ((((-1))/(X*Y^2*W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot298 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot328 X Y Z W a b r - (((-1)))*rhsPivot338 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_339 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 199 + (((1*Y^2)/(X*W^2)) + ((2)/(W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^4)/(W^2)))*v 390 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + ((1*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot339 X Y Z W a b r := by
  have h:=hv 429
  change ((1))*v 29 + ((((-1)*a)/(Y)))*v 87 + ((1))*v 199 + (((1)/(Y^2)))*v 261 + ((1))*v 369=r 429 at h
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p172:=pivot_172 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  have p338:=pivot_338 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot339
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p55 - (((1)/(Y^2)))*p80 - (((1)/(X*Y^2*W^2)))*p91 - ((1))*p172 - (((1)/(Y^2*W^2)))*p194 - (((1)/(X*Y^2*W^2)))*p195 - ((((-1))/(X*Y^2*W^2)))*p230 - ((1))*p298 - ((((-1)*Y^2)/(X*W^2)))*p328 - (((-1)))*p338)*(1/((1)))

def rhsPivot340 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 502 - (((1)/(W^2)))*rhsPivot3 X Y Z W a b r - ((1))*rhsPivot124 X Y Z W a b r - ((1))*rhsPivot126 X Y Z W a b r - ((1))*rhsPivot180 X Y Z W a b r - ((1))*rhsPivot230 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot235 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot236 X Y Z W a b r - ((1*X))*rhsPivot253 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot256 X Y Z W a b r - (((1*Y^2)/(W^2)))*rhsPivot328 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_340 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 126 + (((1)/(W^2)) + ((1*b)/(W)) + (((-1)*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + (((3*X)/(2*W^2)) + (((-1)*X)/(2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot340 X Y Z W a b r := by
  have h:=hv 502
  change ((1))*v 24 + (((1)/(W^2)))*v 90 + ((((-1)*b)/(W)))*v 120 + ((1))*v 126 + ((1))*v 228 + ((1))*v 330 + ((1))*v 432=r 502 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot340
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(W^2)))*p3 - ((1))*p124 - ((1))*p126 - ((1))*p180 - ((1))*p230 - ((((-1)*b)/(W)))*p235 - (((1*X)/(W^2)))*p236 - ((1*X))*p253 - ((((-1)*Y^2)/(W^2)))*p256 - (((1*Y^2)/(W^2)))*p328)*(1/((1)))

def rhsPivot341 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 504 - ((1))*rhsPivot157 X Y Z W a b r - ((1))*rhsPivot166 X Y Z W a b r - (((1)/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot196 X Y Z W a b r - (((1)/(W^2)))*rhsPivot198 X Y Z W a b r - ((1))*rhsPivot214 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot284 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_341 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 384 + ((((-1))/(W^2)) + (((-1)*b)/(W)) + ((1*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + ((((-3)*X)/(2*W^2)) + ((1*X)/(2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot341 X Y Z W a b r := by
  have h:=hv 504
  change ((1))*v 27 + ((1))*v 129 + ((((-1)*b)/(W)))*v 135 + (((1)/(W^2)))*v 165 + ((1))*v 231 + ((1))*v 333 + ((1))*v 435=r 504 at h
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v r hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot341
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p157 - ((1))*p166 - (((1)/(W^2)))*p189 - ((((-1)*b)/(W)))*p196 - (((1)/(W^2)))*p198 - ((1))*p214 - ((((-1))/(X*W^2)))*p230 - ((((-1))/(W^2)))*p257 - ((1))*p284)*(1/(((-1))))

def rhsPivot342 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 487 - ((1))*rhsPivot178 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*X)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot269 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot332 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot341 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_342 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 326 + (((2)/(Y^2*W^2)) + ((1*b)/(Y^2*W)) + ((1)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((3*X)/(2*Y^2*W^2)) + (((-1)*X)/(2*Y^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X*a)/(2*Y)) + ((1*X*a^2)/(2*W^2)) + ((1*X)/(2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((3*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + (((-3)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 435=rhsPivot342 X Y Z W a b r := by
  have h:=hv 487
  change ((1))*v 156 + ((1))*v 326 + (((1)/(Y^2)))*v 384 + ((((-1)*a)/(Y)))*v 468 + ((1))*v 496=r 487 at h
  have p178:=pivot_178 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot342
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p178 - (((1*X)/(Y^2*W^2)))*p189 - ((((-1)*X)/(Y^2*W^2)))*p257 - ((1))*p269 - ((((-1)*a)/(Y)))*p332 - (((1)/(Y^2)))*p341)*(1/((1)))

def rhsPivot343 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 362 - ((1))*rhsPivot106 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(X)))*rhsPivot342 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_343 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 163 + ((((-2))/(X*Y^2*W^2)) + (((-1)*b)/(X*Y^2*W)) + (((-1))/(X*W^2)) + ((1*Y*a)/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + ((((-3))/(2*Y^2*W^2)) + ((1)/(2*Y^2)) + (((-1)*a)/(Y*W^2)) + ((1*a)/(2*Y)) + (((-1)*a^2)/(2*W^2)) + (((-1))/(2)) + (((-1)*Y^2)/(2*W^2)) + ((1*X)/(Y^2*W^2)) + (((-3)*X*a)/(2*Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + (((-1)*X)/(2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2*a^2)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((3*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot343 X Y Z W a b r := by
  have h:=hv 362
  change ((1))*v 163 + (((1)/(X)))*v 326 + ((1))*v 418=r 362 at h
  have p106:=pivot_106 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot343
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p106 - (((1*X)/(Y^2*W^2)))*p236 - ((((-1))/(W^2)))*p256 - (((1)/(X)))*p342)*(1/((1)))

def rhsPivot344 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 512 - ((((-1)*b)/(W)))*rhsPivot131 X Y Z W a b r - ((1))*rhsPivot153 X Y Z W a b r - ((1))*rhsPivot161 X Y Z W a b r - (((1)/(W^2)))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot202 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot205 X Y Z W a b r - ((((-1))/(X*W^2)) + ((1)/(X)) + (((-1)*Y^2)/(W^2)))*rhsPivot230 X Y Z W a b r - ((((-1)*Y^2*b)/(X*W)))*rhsPivot256 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot318 X Y Z W a b r - (((-1)))*rhsPivot335 X Y Z W a b r - ((((-1))/(X)))*rhsPivot341 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_344 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 141 + (((1)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^4)/(W^2)))*v 390 + ((((-1))/(W^2)) + ((1*Y^2)/(W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)))*v 435=rhsPivot344 X Y Z W a b r := by
  have h:=hv 512
  change ((1))*v 39 + ((1))*v 141 + ((((-1)*b)/(W)))*v 195 + ((1))*v 243 + ((1))*v 345 + ((1))*v 447 + (((1)/(W^2)))*v 465=r 512 at h
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v r hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v r hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v r hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot344
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*b)/(W)))*p131 - ((1))*p153 - ((1))*p161 - (((1)/(W^2)))*p189 - ((1))*p202 - (((1*Y^2)/(X*W^2)))*p205 - ((((-1))/(X*W^2)) + ((1)/(X)) + (((-1)*Y^2)/(W^2)))*p230 - ((((-1)*Y^2*b)/(X*W)))*p256 - ((((-1))/(W^2)))*p257 - ((1))*p318 - (((-1)))*p335 - ((((-1))/(X)))*p341)*(1/((1)))

def rhsPivot345 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 349 - (((1)/(X)))*rhsPivot170 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot344 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_345 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)))*v 390 + ((1))*v 396 + ((((-1)*Y^2)/(W^2)) + ((1*X*b)/(W)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)))*v 435=rhsPivot345 X Y Z W a b r := by
  have h:=hv 349
  change ((1))*v 141 + (((1)/(X)))*v 282 + ((1))*v 396=r 349 at h
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p344:=pivot_344 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot345
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p170 - (((1*Y^2)/(X*W^2)))*p264 - ((1))*p344)*(1/((1)))

def rhsPivot346 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 528 - ((1))*rhsPivot74 X Y Z W a b r - (((1)/(X)))*rhsPivot114 X Y Z W a b r - ((1))*rhsPivot116 X Y Z W a b r - ((1))*rhsPivot194 X Y Z W a b r - (((1)/(W^2)))*rhsPivot202 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot208 X Y Z W a b r - ((1))*rhsPivot211 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(X*W^2)) + ((1*b)/(W)))*rhsPivot235 X Y Z W a b r - (((1)/(W^2)))*rhsPivot257 X Y Z W a b r - (((-1)))*rhsPivot340 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_346 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 177 + ((((-2))/(X*W^2)) + ((1)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + ((-1)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + ((5*X)/(2*W^2)) + (((-1)*X)/(2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((3*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot346 X Y Z W a b r := by
  have h:=hv 528
  change ((1))*v 75 + ((1))*v 177 + ((1))*v 279 + (((1)/(W^2)))*v 345 + ((((-1)*b)/(W)))*v 375 + ((1))*v 381 + ((1))*v 483=r 528 at h
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p116:=pivot_116 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot346
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p74 - (((1)/(X)))*p114 - ((1))*p116 - ((1))*p194 - (((1)/(W^2)))*p202 - ((((-1)*b)/(W)))*p208 - ((1))*p211 - (((1)/(X*W^2)))*p230 - (((1)/(X*W^2)) + ((1*b)/(W)))*p235 - (((1)/(W^2)))*p257 - (((-1)))*p340)*(1/((1)))

def rhsPivot347 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 416 - ((((-1)*a)/(Y)))*rhsPivot65 X Y Z W a b r - ((1))*rhsPivot139 X Y Z W a b r - ((((-1)*a)/(X*Y)))*rhsPivot252 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot276 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot336 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot340 X Y Z W a b r - ((1))*rhsPivot346 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_347 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 347 + (((2)/(X*Y^2*W^2)) + ((1*b)/(X*Y^2*W)) + ((1)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + (((-1))/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + (((3)/(2*Y^2*W^2)) + (((-1))/(2*Y^2)) + ((1*a)/(Y*W^2)) + (((-1)*a)/(2*Y)) + ((1*a^2)/(2*W^2)) + ((1)/(2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((3*X*a)/(2*Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X*a^2)/(W^2)) + ((1*X)/(2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y*a^3)/(2*W^2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot347 X Y Z W a b r := by
  have h:=hv 416
  change ((1))*v 7 + ((((-1)*a)/(Y)))*v 21 + (((1)/(Y^2)))*v 63 + ((1))*v 177 + ((1))*v 347=r 416 at h
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v r hv
  have p139:=pivot_139 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v r hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot347
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p65 - ((1))*p139 - ((((-1)*a)/(X*Y)))*p252 - (((1)/(Y^2)))*p276 - ((((-1))/(Y^2)))*p336 - ((((-1))/(X*Y^2)))*p340 - ((1))*p346)*(1/((1)))

def rhsPivot348 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 318 - ((1))*rhsPivot94 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot131 X Y Z W a b r - (((1)/(W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot347 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_348 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 184 + ((((-2))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-1))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-3)*X)/(2*Y^2*W^2)) + ((1*X)/(2*Y^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X*a)/(2*Y)) + (((-1)*X*a^2)/(2*W^2)) + (((-1)*X)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + (((-3)*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*a^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + ((3*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(Y*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=rhsPivot348 X Y Z W a b r := by
  have h:=hv 318
  change ((1))*v 92 + (((1)/(X)))*v 184 + ((1))*v 347=r 318 at h
  have p94:=pivot_94 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p347:=pivot_347 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot348
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p94 - (((1*X)/(Y^2*W^2)))*p131 - (((1)/(W^2)))*p256 - ((1))*p347)*(1/(((1)/(X))))

def rhsPivot349 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 203 - (((1)/(X*Z)))*rhsPivot10 X Y Z W a b r - ((1))*rhsPivot99 X Y Z W a b r - ((1))*rhsPivot103 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot113 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot143 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot165 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot322 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_349 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(X*W^2)))*v 140 + ((1))*v 309 + (((1)/(X)) + ((1)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + ((((-3))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot349 X Y Z W a b r := by
  have h:=hv 203
  change (((1)/(X*Z)))*v 0 + (((1)/(X*Z)))*v 102 + ((1))*v 105 + (((1)/(X*Z)))*v 204 + ((1))*v 207 + (((1)/(X*Z)))*v 306 + ((1))*v 309 + ((1))*v 411=r 203 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v r hv
  have p113:=pivot_113 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot349
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p10 - ((1))*p99 - ((1))*p103 - (((1)/(X*Z)))*p113 - (((1)/(X*Z)))*p143 - (((1)/(X*Z)))*p165 - ((((-1))/(X*W^2)))*p195 - ((1))*p322)*(1/((1)))

def rhsPivot350 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 204 - (((1)/(X*Z)))*rhsPivot10 X Y Z W a b r - ((1))*rhsPivot97 X Y Z W a b r - ((1))*rhsPivot102 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot120 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot143 X Y Z W a b r - (((1)/(X*Z)))*rhsPivot165 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot194 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot195 X Y Z W a b r - (((1)/(X)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot272 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_350 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 201 + (((1*Y^2)/(X*W^2)))*v 370 + ((((-1))/(X)) + (((-1))/(W^2)) + ((1*X)/(W^2)))*v 390 + (((3)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot350 X Y Z W a b r := by
  have h:=hv 204
  change (((1)/(X*Z)))*v 0 + ((1))*v 99 + ((1))*v 201 + (((1)/(X*Z)))*v 204 + ((1))*v 303 + (((1)/(X*Z)))*v 306 + ((1))*v 405 + (((1)/(X*Z)))*v 408=r 204 at h
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p97:=pivot_97 X Y Z W a b hX hY hZ hW v r hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  have p120:=pivot_120 X Y Z W a b hX hY hZ hW v r hv
  have p143:=pivot_143 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot350
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X*Z)))*p10 - ((1))*p97 - ((1))*p102 - (((1)/(X*Z)))*p120 - (((1)/(X*Z)))*p143 - (((1)/(X*Z)))*p165 - ((((-1))/(W^2)))*p194 - ((((-1))/(X*W^2)))*p195 - (((1)/(X)))*p235 - ((1))*p272)*(1/((1)))

def rhsPivot351 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 205 - (((1*X)/(Z)))*rhsPivot6 X Y Z W a b r - ((1))*rhsPivot104 X Y Z W a b r - ((1))*rhsPivot121 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot130 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot230 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot231 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot232 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot234 X Y Z W a b r - ((1*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot302 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_351 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*X*Y^2)/(W^2)))*v 140 + ((1))*v 312 + (((-1)))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X^2)/(2*W^2)) + (1*X^2) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot351 X Y Z W a b r := by
  have h:=hv 205
  change (((1*X)/(Z)))*v 51 + ((1))*v 108 + (((1*X)/(Z)))*v 153 + ((1))*v 210 + (((1*X)/(Z)))*v 255 + ((1))*v 312 + (((1*X)/(Z)))*v 357 + ((1))*v 414=r 205 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot351
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z)))*p6 - ((1))*p104 - ((1))*p121 - (((1*X)/(Z)))*p130 - (((1*X)/(W^2)))*p198 - ((((-1))/(W^2)))*p230 - (((1*X)/(Z)))*p231 - ((((-1))/(W^2)))*p232 - (((1*X)/(Z)))*p234 - ((1*X))*p257 - ((1))*p302)*(1/((1)))

#print axioms pivot_351

def rhsPivot352 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 206 - (((1*X)/(Z)))*rhsPivot6 X Y Z W a b r - ((1))*rhsPivot96 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot135 X Y Z W a b r - ((1))*rhsPivot150 X Y Z W a b r - ((1*X))*rhsPivot189 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot202 X Y Z W a b r - (((1)/(W^2)))*rhsPivot230 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot231 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot233 X Y Z W a b r - (((1*X)/(Z)))*rhsPivot234 X Y Z W a b r - (((-1)*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot299 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_352 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 198 + ((((-1)*X*Y^2)/(W^2)))*v 370 + ((1))*v 390 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + ((-1)*X^2) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot352 X Y Z W a b r := by
  have h:=hv 206
  change ((1))*v 96 + (((1*X)/(Z)))*v 153 + ((1))*v 198 + (((1*X)/(Z)))*v 255 + ((1))*v 300 + (((1*X)/(Z)))*v 357 + ((1))*v 402 + (((1*X)/(Z)))*v 459=r 206 at h
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v r hv
  have p135:=pivot_135 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot352
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*X)/(Z)))*p6 - ((1))*p96 - (((1*X)/(Z)))*p135 - ((1))*p150 - ((1*X))*p189 - (((1*X)/(W^2)))*p202 - (((1)/(W^2)))*p230 - (((1*X)/(Z)))*p231 - ((((-1))/(W^2)))*p233 - (((1*X)/(Z)))*p234 - (((-1)*X))*p257 - ((1))*p299)*(1/((1)))

def rhsPivot353 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 209 - (((1*Z)/(X*Y^2)))*rhsPivot0 X Y Z W a b r - ((1))*rhsPivot12 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot204 X Y Z W a b r - ((1))*rhsPivot207 X Y Z W a b r - (((-1)))*rhsPivot238 X Y Z W a b r - ((1))*rhsPivot240 X Y Z W a b r - ((1))*rhsPivot244 X Y Z W a b r - ((((-1)*Z)/(Y^2)))*rhsPivot313 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot320 X Y Z W a b r)/((((-1)*X^2*Z)/(Y^2)))

compact_elimination_proof
theorem pivot_353 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 342 + ((((-1)*Y^2)/(X^2*W^2)))*v 370 + ((((-1))/(X^3)) + ((1)/(X^2*W^2)))*v 390 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + (((-1))/(2*X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)))*v 435=rhsPivot353 X Y Z W a b r := by
  have h:=hv 209
  change (((1*Z)/(X*Y^2)))*v 84 + ((1))*v 119 + (((1*Z)/(X*Y^2)))*v 186 + ((1))*v 221 + (((1*Z)/(X*Y^2)))*v 288 + ((1))*v 323 + (((1*Z)/(X*Y^2)))*v 390 + ((1))*v 425=r 209 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v r hv
  have p12:=pivot_12 X Y Z W a b hX hY hZ hW v r hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v r hv
  have p207:=pivot_207 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  have p240:=pivot_240 X Y Z W a b hX hY hZ hW v r hv
  have p244:=pivot_244 X Y Z W a b hX hY hZ hW v r hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot353
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1*Z)/(X*Y^2)))*p0 - ((1))*p12 - (((1*Z)/(X*Y^2)))*p204 - ((1))*p207 - (((-1)))*p238 - ((1))*p240 - ((1))*p244 - ((((-1)*Z)/(Y^2)))*p313 - (((1*Z)/(X*Y^2)))*p320)*(1/((((-1)*X^2*Z)/(Y^2))))

def rhsPivot354 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 210 - ((1))*rhsPivot11 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot16 X Y Z W a b r - ((1))*rhsPivot217 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot220 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot237 X Y Z W a b r - (((-1)))*rhsPivot241 X Y Z W a b r - ((1))*rhsPivot243 X Y Z W a b r - (((1*Z)/(X*Y^2)))*rhsPivot274 X Y Z W a b r)/((((-1)*Z)/(Y^2)))

compact_elimination_proof
theorem pivot_354 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(W^2)))*v 140 + ((1))*v 162 + (((1)/(X)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)))*v 435=rhsPivot354 X Y Z W a b r := by
  have h:=hv 210
  change ((1))*v 85 + (((1*Z)/(X*Y^2)))*v 120 + ((1))*v 187 + (((1*Z)/(X*Y^2)))*v 222 + ((1))*v 289 + (((1*Z)/(X*Y^2)))*v 324 + ((1))*v 391 + (((1*Z)/(X*Y^2)))*v 426=r 210 at h
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  have p16:=pivot_16 X Y Z W a b hX hY hZ hW v r hv
  have p217:=pivot_217 X Y Z W a b hX hY hZ hW v r hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p237:=pivot_237 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  have p243:=pivot_243 X Y Z W a b hX hY hZ hW v r hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot354
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p11 - (((1*Z)/(X*Y^2)))*p16 - ((1))*p217 - (((1*Z)/(X*Y^2)))*p220 - (((1*Z)/(X*Y^2)))*p235 - ((1))*p237 - (((-1)))*p241 - ((1))*p243 - (((1*Z)/(X*Y^2)))*p274)*(1/((((-1)*Z)/(Y^2))))

def rhsPivot355 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 214 - ((1))*rhsPivot77 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot118 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot119 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot133 X Y Z W a b r - ((((-1)*X)/(W^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot239 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot241 X Y Z W a b r - (((-1)*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot332 X Y Z W a b r - ((1))*rhsPivot354 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_355 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(W^2)))*v 140 + ((1))*v 366 + ((((-1))/(X)) + (1) + ((1*Y^2)/(W^2)) + (((-1)*X)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(2*W^2)) + (1*X) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(W^2)) + ((-1)*X^2) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot355 X Y Z W a b r := by
  have h:=hv 214
  change (((1*Y^2)/(Z)))*v 34 + ((1))*v 60 + (((1*Y^2)/(Z)))*v 136 + ((1))*v 162 + (((1*Y^2)/(Z)))*v 340 + ((1))*v 366 + (((1*Y^2)/(Z)))*v 442 + ((1))*v 468=r 214 at h
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  have p119:=pivot_119 X Y Z W a b hX hY hZ hW v r hv
  have p133:=pivot_133 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p241:=pivot_241 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot355
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p77 - (((1*Y^2)/(Z)))*p118 - (((1*Y^2)/(Z)))*p119 - (((1*Y^2)/(Z)))*p133 - ((((-1)*X)/(W^2)))*p194 - ((((-1)*Y^2)/(W^2)))*p239 - (((1*Y^2)/(Z)))*p241 - (((-1)*X))*p257 - ((1))*p332 - ((1))*p354)*(1/((1)))

def rhsPivot356 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 215 - ((1))*rhsPivot91 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot117 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot128 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot169 X Y Z W a b r - (((-1)*X))*rhsPivot189 X Y Z W a b r - ((1*X))*rhsPivot194 X Y Z W a b r - (((1*Y^2)/(Z)))*rhsPivot238 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot242 X Y Z W a b r - ((1*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot261 X Y Z W a b r - ((1))*rhsPivot313 X Y Z W a b r - ((1*X^2))*rhsPivot353 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_356 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 144 + (((1*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((-1)) + (((-1)*Y^2)/(W^2)) + ((1*X)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(2*W^2)) + ((-1)*X) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X^2)/(W^2)) + (1*X^2) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot356 X Y Z W a b r := by
  have h:=hv 215
  change ((1))*v 42 + (((1*Y^2)/(Z)))*v 68 + ((1))*v 144 + (((1*Y^2)/(Z)))*v 170 + ((1))*v 348 + (((1*Y^2)/(Z)))*v 374 + ((1))*v 450 + (((1*Y^2)/(Z)))*v 476=r 215 at h
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p128:=pivot_128 X Y Z W a b hX hY hZ hW v r hv
  have p169:=pivot_169 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p238:=pivot_238 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot356
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p91 - (((1*Y^2)/(Z)))*p117 - (((1*Y^2)/(Z)))*p128 - (((1*Y^2)/(Z)))*p169 - (((-1)*X))*p189 - ((1*X))*p194 - (((1*Y^2)/(Z)))*p238 - ((((-1)*Y^2)/(W^2)))*p242 - ((1*X))*p257 - ((1))*p261 - ((1))*p313 - ((1*X^2))*p353)*(1/((1)))

def rhsPivot357 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 227 - ((((-1)*X)/(Y^2)))*rhsPivot2 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot5 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot6 X Y Z W a b r - ((1))*rhsPivot43 X Y Z W a b r - ((1))*rhsPivot60 X Y Z W a b r - ((1))*rhsPivot62 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot83 X Y Z W a b r - ((1))*rhsPivot88 X Y Z W a b r - ((1))*rhsPivot98 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot99 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot102 X Y Z W a b r - ((1))*rhsPivot118 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot131 X Y Z W a b r - ((1))*rhsPivot136 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot137 X Y Z W a b r - ((1))*rhsPivot144 X Y Z W a b r - ((1))*rhsPivot193 X Y Z W a b r - ((((-2)*X)/(Y^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot196 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot198 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot202 X Y Z W a b r - ((1))*rhsPivot205 X Y Z W a b r - ((((-1))/(Y^2)) + ((-1)) + ((-1)*X))*rhsPivot230 X Y Z W a b r - ((((-1)*X*W^2)/(Y^2*Z)))*rhsPivot234 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot235 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot236 X Y Z W a b r - ((1))*rhsPivot239 X Y Z W a b r - ((1))*rhsPivot246 X Y Z W a b r - (((1*X*W^2)/(Y^2)))*rhsPivot253 X Y Z W a b r - ((1))*rhsPivot256 X Y Z W a b r - ((((-1)*X*Z)/(Y^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot329 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot334 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_357 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 140 + (((-1)))*v 370 + (((2)/(Y^2)) + (((-1)*Z)/(Y^2)) + (((-1)*a)/(Y)) + (2) + (((-1)*X)/(Y^2)) + (1*X))*v 390 + ((((-3)*X)/(2*Y^2)) + (((-1)*X*a)/(Y)) + (1*X) + (((-1)*X*a^2)/(2)) + ((-1)*X*Y*a) + (((-1)*X*Y^2)/(2)) + (((-7)*X^2)/(2*Y^2)) + ((1*X^2*Z)/(Y^2)) + (((-1)*X^2*a^2)/(2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + (((-1)*X^3)/(2)) + (((-1)*X^3*a^2)/(2)) + ((1*X^3*Z)/(2)) + ((-1)*X^3*Y*a) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot357 X Y Z W a b r := by
  have h:=hv 227
  change ((((-1)*X)/(Y^2)))*v 15 + ((1))*v 40 + ((((-1)*X)/(Y^2)))*v 45 + ((1))*v 70 + ((((-1)*X)/(Y^2)))*v 75 + ((1))*v 100 + ((((-1)*X)/(Y^2)))*v 105 + ((1))*v 130 + ((((-1)*X)/(Y^2)))*v 135 + ((1))*v 160 + ((((-1)*X)/(Y^2)))*v 165 + ((1))*v 190 + ((((-1)*X)/(Y^2)))*v 195 + ((1))*v 220 + ((((-1)*X)/(Y^2)))*v 225 + ((1))*v 250 + ((((-1)*X)/(Y^2)))*v 255 + ((1))*v 280 + ((((-1)*X)/(Y^2)))*v 285 + ((1))*v 310 + ((((-1)*X)/(Y^2)))*v 315 + ((1))*v 340 + ((((-1)*X)/(Y^2)))*v 345 + ((1))*v 370 + ((((-1)*X)/(Y^2)))*v 375 + ((1))*v 400 + ((((-1)*X)/(Y^2)))*v 405 + ((1))*v 430 + ((((-1)*X)/(Y^2)))*v 435 + ((1))*v 460 + ((1))*v 490 + ((((-1)*X)/(Y^2)))*v 495=r 227 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v r hv
  have p6:=pivot_6 X Y Z W a b hX hY hZ hW v r hv
  have p43:=pivot_43 X Y Z W a b hX hY hZ hW v r hv
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  have p62:=pivot_62 X Y Z W a b hX hY hZ hW v r hv
  have p83:=pivot_83 X Y Z W a b hX hY hZ hW v r hv
  have p88:=pivot_88 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  have p118:=pivot_118 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p136:=pivot_136 X Y Z W a b hX hY hZ hW v r hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v r hv
  have p144:=pivot_144 X Y Z W a b hX hY hZ hW v r hv
  have p193:=pivot_193 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot357
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*X)/(Y^2)))*p2 - ((((-1)*X)/(Y^2)))*p5 - ((((-1)*X)/(Y^2)))*p6 - ((1))*p43 - ((1))*p60 - ((1))*p62 - ((((-1)*X)/(Y^2)))*p83 - ((1))*p88 - ((1))*p98 - ((((-1)*X)/(Y^2)))*p99 - ((((-1)*X)/(Y^2)))*p102 - ((1))*p118 - ((((-1)*X)/(Y^2)))*p131 - ((1))*p136 - ((((-1)*X)/(Y^2)))*p137 - ((1))*p144 - ((1))*p193 - ((((-2)*X)/(Y^2)))*p194 - ((((-1)*X)/(Y^2)))*p196 - ((((-1)*X)/(Y^2)))*p198 - ((((-1)*X)/(Y^2)))*p202 - ((1))*p205 - ((((-1))/(Y^2)) + ((-1)) + ((-1)*X))*p230 - ((((-1)*X*W^2)/(Y^2*Z)))*p234 - ((((-1))/(Y^2)))*p235 - ((((-1)*X)/(Y^2)))*p236 - ((1))*p239 - ((1))*p246 - (((1*X*W^2)/(Y^2)))*p253 - ((1))*p256 - ((((-1)*X*Z)/(Y^2)))*p257 - ((1))*p264 - ((1))*p329 - (((1*W^2)/(Y^2)))*p334)*(1/(((-1))))

def rhsPivot358 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 222 - ((((-1))/(X*Y^2)))*rhsPivot4 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot9 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot10 X Y Z W a b r - ((1))*rhsPivot11 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot13 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot15 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot27 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot77 X Y Z W a b r - ((1))*rhsPivot82 X Y Z W a b r - ((1))*rhsPivot90 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot91 X Y Z W a b r - ((1))*rhsPivot101 X Y Z W a b r - ((1))*rhsPivot105 X Y Z W a b r - ((1))*rhsPivot111 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot121 X Y Z W a b r - ((1))*rhsPivot132 X Y Z W a b r - ((1))*rhsPivot141 X Y Z W a b r - ((1))*rhsPivot149 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot150 X Y Z W a b r - ((1))*rhsPivot155 X Y Z W a b r - ((((-1)*W^2)/(X*Y^2*Z)))*rhsPivot165 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot215 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot233 X Y Z W a b r - ((1))*rhsPivot250 X Y Z W a b r - ((1))*rhsPivot255 X Y Z W a b r - (((1*Y^2)/(X)))*rhsPivot256 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot257 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot268 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot274 X Y Z W a b r - ((1))*rhsPivot294 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot299 X Y Z W a b r - ((1))*rhsPivot321 X Y Z W a b r - (((-1)))*rhsPivot329 X Y Z W a b r - (((1*W^2)/(X*Y^2)) + (((-1)*W^2)/(Y^2)))*rhsPivot334 X Y Z W a b r - ((1))*rhsPivot357 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_358 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 325 + (((1)/(X)))*v 370 + ((((-2))/(X*Y^2)) + ((1*a)/(X*Y)) + (((-2))/(X)) + ((1)/(Y^2)) + ((1*Z)/(Y^2)) + ((-1)) + ((-1)*X))*v 390 + (((3)/(2*Y^2)) + ((1*a)/(Y)) + ((-1)) + ((1*a^2)/(2)) + (1*Y*a) + ((1*Y^2)/(2)) + ((5*X)/(2*Y^2)) + ((1*X*a^2)/(2)) + (1*X*Y*a) + ((1*X*Y^2)/(2)) + ((1*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)) + ((1*X^2*a^2)/(2)) + (1*X^2*Y*a) + ((1*X^2*Y^2)/(2)) + ((1*X^3)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + (((-1)*X^3*Z*a)/(2*Y)) + ((1*X^3*a^2)/(2)) + (((-1)*X^3*Z)/(2)) + ((1*X^3*Y*a)/(2)))*v 435=rhsPivot358 X Y Z W a b r := by
  have h:=hv 222
  change ((((-1))/(X*Y^2)))*v 0 + ((1))*v 25 + ((((-1))/(X*Y^2)))*v 30 + ((1))*v 55 + ((((-1))/(X*Y^2)))*v 60 + ((1))*v 85 + ((1))*v 115 + ((((-1))/(X*Y^2)))*v 120 + ((1))*v 145 + ((((-1))/(X*Y^2)))*v 150 + ((1))*v 175 + ((((-1))/(X*Y^2)))*v 180 + ((1))*v 205 + ((((-1))/(X*Y^2)))*v 210 + ((1))*v 235 + ((((-1))/(X*Y^2)))*v 240 + ((1))*v 265 + ((((-1))/(X*Y^2)))*v 270 + ((1))*v 295 + ((((-1))/(X*Y^2)))*v 300 + ((1))*v 325 + ((((-1))/(X*Y^2)))*v 330 + ((1))*v 355 + ((((-1))/(X*Y^2)))*v 360 + ((1))*v 385 + ((((-1))/(X*Y^2)))*v 390 + ((1))*v 415 + ((((-1))/(X*Y^2)))*v 420 + ((1))*v 445 + ((((-1))/(X*Y^2)))*v 450 + ((1))*v 475 + ((((-1))/(X*Y^2)))*v 480=r 222 at h
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p11:=pivot_11 X Y Z W a b hX hY hZ hW v r hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p82:=pivot_82 X Y Z W a b hX hY hZ hW v r hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p101:=pivot_101 X Y Z W a b hX hY hZ hW v r hv
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v r hv
  have p111:=pivot_111 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p132:=pivot_132 X Y Z W a b hX hY hZ hW v r hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v r hv
  have p149:=pivot_149 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p155:=pivot_155 X Y Z W a b hX hY hZ hW v r hv
  have p165:=pivot_165 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p215:=pivot_215 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p250:=pivot_250 X Y Z W a b hX hY hZ hW v r hv
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v r hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v r hv
  have p294:=pivot_294 X Y Z W a b hX hY hZ hW v r hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v r hv
  have p321:=pivot_321 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot358
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*Y^2)))*p4 - ((((-1))/(X*Y^2)))*p9 - ((((-1))/(X*Y^2)))*p10 - ((1))*p11 - ((((-1))/(X*Y^2)))*p13 - ((((-1))/(X*Y^2)))*p15 - ((((-1))/(X*Y^2)))*p27 - ((((-1))/(X*Y^2)))*p77 - ((1))*p82 - ((1))*p90 - ((((-1))/(X*Y^2)))*p91 - ((1))*p101 - ((1))*p105 - ((1))*p111 - ((((-1))/(X*Y^2)))*p121 - ((1))*p132 - ((1))*p141 - ((1))*p149 - ((((-1))/(X*Y^2)))*p150 - ((1))*p155 - ((((-1)*W^2)/(X*Y^2*Z)))*p165 - ((((-1))/(Y^2)))*p189 - ((((-1))/(Y^2)))*p194 - ((1))*p215 - ((((-1))/(X*Y^2)))*p233 - ((1))*p250 - ((1))*p255 - (((1*Y^2)/(X)))*p256 - ((((-1))/(Y^2)))*p257 - (((1*W^2)/(X*Y^2)))*p268 - (((1*W^2)/(X*Y^2)))*p274 - ((1))*p294 - (((1*W^2)/(X*Y^2)))*p299 - ((1))*p321 - (((-1)))*p329 - (((1*W^2)/(X*Y^2)) + (((-1)*W^2)/(Y^2)))*p334 - ((1))*p357)*(1/((1)))

def rhsPivot359 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 270 - ((1))*rhsPivot75 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot115 X Y Z W a b r - ((1))*rhsPivot197 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot227 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot256 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_359 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 44 + (((1*X)/(W^2)))*v 370 + ((((-1))/(Y^2*W^2)))*v 390 + (((1*X^2)/(Y^2*W^2)))*v 435=rhsPivot359 X Y Z W a b r := by
  have h:=hv 270
  change ((1))*v 22 + (((1)/(X)))*v 44 + ((1))*v 277=r 270 at h
  have p75:=pivot_75 X Y Z W a b hX hY hZ hW v r hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v r hv
  have p197:=pivot_197 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot359
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p75 - (((1)/(X*Y^2)))*p115 - ((1))*p197 - ((((-1))/(W^2)))*p227 - (((1)/(X*W^2)))*p256)*(1/(((1)/(X))))

def rhsPivot360 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 274 - ((1))*rhsPivot173 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_360 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X)))*v 62 + ((1))*v 286 + (((1)/(X*Y^2*W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)))*v 435=rhsPivot360 X Y Z W a b r := by
  have h:=hv 274
  change ((1))*v 31 + (((1)/(X)))*v 62 + ((1))*v 286=r 274 at h
  have p173:=pivot_173 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot360
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p173 - (((1)/(Y^2*W^2)))*p189 - ((((-1))/(Y^2*W^2)))*p257)*(1/((1)))

def rhsPivot361 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 284 - (((1)/(X)))*rhsPivot59 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_361 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 43 + ((1))*v 298 + (((1)/(X*Y^2*W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)))*v 435=rhsPivot361 X Y Z W a b r := by
  have h:=hv 284
  change ((1))*v 43 + (((1)/(X)))*v 86 + ((1))*v 298=r 284 at h
  have p59:=pivot_59 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot361
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p59 - (((1)/(Y^2*W^2)))*p189 - ((((-1))/(Y^2*W^2)))*p257)*(1/((1)))

def rhsPivot362 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 336 - (((1)/(X)))*rhsPivot162 X Y Z W a b r - (((1)/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_362 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 123 + ((1))*v 378 + (((1)/(X*W^2)))*v 390 + ((((-1)*X)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)))*v 435=rhsPivot362 X Y Z W a b r := by
  have h:=hv 336
  change ((1))*v 123 + (((1)/(X)))*v 246 + ((1))*v 378=r 336 at h
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot362
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p162 - (((1)/(W^2)))*p189 - ((((-1))/(W^2)))*p257)*(1/((1)))

def rhsPivot363 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 343 - (((1)/(X)))*rhsPivot109 X Y Z W a b r - (((1)/(W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_363 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 132 + ((1))*v 387 + ((((-1))/(X*W^2)))*v 390 + (((1*X)/(W^2)) + ((1*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)))*v 435=rhsPivot363 X Y Z W a b r := by
  have h:=hv 343
  change ((1))*v 132 + (((1)/(X)))*v 264 + ((1))*v 387=r 343 at h
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot363
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p109 - (((1)/(W^2)))*p257)*(1/((1)))

def rhsPivot364 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 352 - (((1)/(X)))*rhsPivot267 X Y Z W a b r - ((1))*rhsPivot299 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_364 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 147 + ((((-1)*X*Y^2)/(W^2)))*v 370 + ((((-1)*Y^2)/(X^2*W^2)))*v 390 + ((((-1)*Y^2)/(X*W^2)) + ((1)/(W^2)) + ((1*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(W^2)))*v 435=rhsPivot364 X Y Z W a b r := by
  have h:=hv 352
  change ((1))*v 147 + (((1)/(X)))*v 294 + ((1))*v 402=r 352 at h
  have p267:=pivot_267 X Y Z W a b hX hY hZ hW v r hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot364
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p267 - ((1))*p299)*(1/((1)))

def rhsPivot365 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 377 - ((1))*rhsPivot228 X Y Z W a b r - (((-1)))*rhsPivot291 X Y Z W a b r - (((1)/(X)))*rhsPivot335 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_365 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 362 + ((((-1))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)))*v 390 + ((((-1)*X)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)))*v 435 + ((1*X))*v 436=rhsPivot365 X Y Z W a b r := by
  have h:=hv 377
  change ((1))*v 181 + (((1)/(X)))*v 362 + ((1))*v 436=r 377 at h
  have p228:=pivot_228 X Y Z W a b hX hY hZ hW v r hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v r hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot365
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p228 - (((-1)))*p291 - (((1)/(X)))*p335)*(1/(((1)/(X))))

def rhsPivot366 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 393 - (((1)/(X)))*rhsPivot108 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot121 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_366 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 212 + ((((-1))/(X*Y^2*W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)))*v 435 + ((1))*v 467=rhsPivot366 X Y Z W a b r := by
  have h:=hv 393
  change ((1))*v 212 + (((1)/(X)))*v 424 + ((1))*v 467=r 393 at h
  have p108:=pivot_108 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot366
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(X)))*p108 - (((1)/(X*Y^2*W^2)))*p121 - (((1)/(Y^2*W^2)))*p257)*(1/((1)))

def rhsPivot367 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 402 - ((1))*rhsPivot168 X Y Z W a b r - (((1)/(X)))*rhsPivot171 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_367 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 224 + ((((-1))/(X*Y^2*W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)))*v 435 + (((1)/(X)))*v 448=rhsPivot367 X Y Z W a b r := by
  have h:=hv 402
  change ((1))*v 224 + (((1)/(X)))*v 448 + ((1))*v 479=r 402 at h
  have p168:=pivot_168 X Y Z W a b hX hY hZ hW v r hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot367
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p168 - (((1)/(X)))*p171 - (((1)/(Y^2*W^2)))*p257)*(1/((1)))

#print axioms pivot_367

def rhsPivot368 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 404 - ((1))*rhsPivot181 X Y Z W a b r - ((1))*rhsPivot225 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot246 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(W^2)))*rhsPivot357 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_368 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*X)/(W^2)))*v 370 + (((1)/(Y^2*W^2)) + (((-2)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-2)*X)/(W^2)) + ((1*X^2)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 390 + (((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(2*W^2)) + ((7*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*Z)/(Y^2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4)/(2*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)))*v 435 + ((1))*v 466=rhsPivot368 X Y Z W a b r := by
  have h:=hv 404
  change ((1))*v 233 + (((1)/(X)))*v 466 + ((1))*v 488=r 404 at h
  have p181:=pivot_181 X Y Z W a b hX hY hZ hW v r hv
  have p225:=pivot_225 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p246:=pivot_246 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot368
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p181 - ((1))*p225 - (((1)/(Y^2*W^2)))*p236 - ((((-1))/(W^2)))*p246 - ((((-1))/(X*W^2)))*p256 - (((1)/(W^2)))*p357)*(1/(((1)/(X))))

def rhsPivot369 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 414 - ((1))*rhsPivot34 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot69 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot166 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot189 X Y Z W a b r - (((1*a)/(Y*W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot289 X Y Z W a b r - ((1))*rhsPivot312 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_369 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 176 + ((1))*v 346 + ((((-1))/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 390 + ((((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)))*v 435=rhsPivot369 X Y Z W a b r := by
  have h:=hv 414
  change ((1))*v 3 + ((((-1)*a)/(Y)))*v 9 + (((1)/(Y^2)))*v 27 + ((1))*v 173 + ((1))*v 343=r 414 at h
  have p34:=pivot_34 X Y Z W a b hX hY hZ hW v r hv
  have p69:=pivot_69 X Y Z W a b hX hY hZ hW v r hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p289:=pivot_289 X Y Z W a b hX hY hZ hW v r hv
  have p312:=pivot_312 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot369
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p34 - ((((-1)*a)/(Y)))*p69 - (((1)/(Y^2)))*p166 - ((((-1)*a)/(Y*W^2)))*p189 - (((1*a)/(Y*W^2)))*p257 - ((1))*p289 - ((1))*p312)*(1/((((-1))/(X))))

def rhsPivot370 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 423 - ((1))*rhsPivot19 X Y Z W a b r - ((1))*rhsPivot204 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot262 X Y Z W a b r - (((-1)*X))*rhsPivot313 X Y Z W a b r - (((-1)*X^3))*rhsPivot353 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot356 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_370 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 356 + ((((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 370 + ((((-1))/(X*Y^2)) + ((1)/(Y^2)) + (((-1)*a)/(Y*W^2)) + ((1)/(W^2)) + ((-1)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)))*v 390 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(2*Y^2*W^2)) + ((1*X)/(Y^2)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)))*v 435=rhsPivot370 X Y Z W a b r := by
  have h:=hv 423
  change ((1))*v 16 + ((((-1)*a)/(Y)))*v 48 + (((1)/(Y^2)))*v 144 + ((1))*v 186 + ((1))*v 356=r 423 at h
  have p19:=pivot_19 X Y Z W a b hX hY hZ hW v r hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v r hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v r hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot370
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p19 - ((1))*p204 - ((((-1)*a)/(Y)))*p262 - (((-1)*X))*p313 - (((-1)*X^3))*p353 - (((1)/(Y^2)))*p356)*(1/((1)))

def rhsPivot371 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 376 - ((1))*rhsPivot311 X Y Z W a b r - (((-1)*X^2))*rhsPivot353 X Y Z W a b r - (((1)/(X)))*rhsPivot370 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_371 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X*W^2)))*v 370 + (((1)/(X^2*Y^2)) + (((-1))/(X*Y^2)) + ((1*a)/(X*Y*W^2)) + (((-1))/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1)/(W^2)))*v 390 + ((1))*v 433 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + ((1)/(2*Y^2*W^2)) + (((-1))/(Y^2)) + ((1*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + ((2*X)/(Y^2*W^2)) + ((1*X)/(Y^2)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)))*v 435=rhsPivot371 X Y Z W a b r := by
  have h:=hv 376
  change ((1))*v 178 + (((1)/(X)))*v 356 + ((1))*v 433=r 376 at h
  have p311:=pivot_311 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  have p370:=pivot_370 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot371
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p311 - (((-1)*X^2))*p353 - (((1)/(X)))*p370)*(1/((1)))

def rhsPivot372 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 426 - ((1))*rhsPivot197 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot199 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot227 X Y Z W a b r - (((1*X*a)/(Y)))*rhsPivot320 X Y Z W a b r - ((1))*rhsPivot335 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot352 X Y Z W a b r - ((1))*rhsPivot365 X Y Z W a b r)/(((-1)*X))

compact_elimination_proof
theorem pivot_372 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X*Y*a)/(W^2)))*v 370 + (((1)/(X*Y^2)))*v 390 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + (((-1)*X)/(2*Y^2*W^2)) + (((-1)*X)/(Y^2)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X*a^2)/(2*W^2)) + (((-3)*X*Y*a)/(2*W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)))*v 435 + ((1))*v 436=rhsPivot372 X Y Z W a b r := by
  have h:=hv 426
  change ((1))*v 22 + ((((-1)*a)/(Y)))*v 66 + ((1))*v 192 + (((1)/(Y^2)))*v 198 + ((1))*v 362=r 426 at h
  have p197:=pivot_197 X Y Z W a b hX hY hZ hW v r hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v r hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v r hv
  have p365:=pivot_365 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot372
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p197 - ((((-1)*a)/(Y)))*p199 - ((((-1))/(W^2)))*p227 - (((1*X*a)/(Y)))*p320 - ((1))*p335 - (((1)/(Y^2)))*p352 - ((1))*p365)*(1/(((-1)*X)))

def rhsPivot373 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 427 - (((1)/(Y^2)))*rhsPivot158 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot252 X Y Z W a b r - ((1))*rhsPivot260 X Y Z W a b r - ((1))*rhsPivot355 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_373 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 196 + ((((-1)*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((1)/(Y^2*W^2)) + ((2)/(W^2)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X*a^2)/(2*W^2)) + ((-1)*X) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + ((3*X^2*a)/(2*Y*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^2*a^2)/(2*W^2)) + (1*X^2) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-1)*X^3)/(Y^2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)))*v 435=rhsPivot373 X Y Z W a b r := by
  have h:=hv 427
  change ((1))*v 26 + ((((-1)*a)/(Y)))*v 78 + ((1))*v 196 + (((1)/(Y^2)))*v 234 + ((1))*v 366=r 427 at h
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p260:=pivot_260 X Y Z W a b hX hY hZ hW v r hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot373
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2)))*p158 - ((((-1)*a)/(Y)))*p252 - ((1))*p260 - ((1))*p355 - ((((-1)*Y^2)/(W^2)))*p357)*(1/((1)))

def rhsPivot374 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 428 - ((((-1)*a)/(Y)))*rhsPivot0 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot45 X Y Z W a b r - ((1))*rhsPivot167 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*X)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot352 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_374 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 368 + (((1*X*Y^2)/(W^2)))*v 370 + (((1)/(Y^2*W^2)) + ((-1)))*v 390 + (((1*X)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2)/(2*W^2)) + (1*X^2) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot374 X Y Z W a b r := by
  have h:=hv 428
  change ((1))*v 28 + ((((-1)*a)/(Y)))*v 84 + ((1))*v 198 + (((1)/(Y^2)))*v 252 + ((1))*v 368=r 428 at h
  have p0:=pivot_0 X Y Z W a b hX hY hZ hW v r hv
  have p45:=pivot_45 X Y Z W a b hX hY hZ hW v r hv
  have p167:=pivot_167 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot374
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p0 - (((1)/(Y^2)))*p45 - ((1))*p167 - (((1*X)/(Y^2*W^2)))*p189 - ((((-1)*X)/(Y^2*W^2)))*p257 - ((1))*p352)*(1/((1)))

def rhsPivot375 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 432 - ((1))*rhsPivot22 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot96 X Y Z W a b r - ((((-1)*X*a)/(Y*W^2)))*rhsPivot202 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot320 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_375 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 202 + (((1*X)/(W^2)))*v 370 + ((1))*v 372 + ((((-1)*X)/(Y^2*W^2)) + ((1*X)/(W^2)))*v 435=rhsPivot375 X Y Z W a b r := by
  have h:=hv 432
  change ((1))*v 32 + ((((-1)*a)/(Y)))*v 96 + ((1))*v 202 + (((1)/(Y^2)))*v 288 + ((1))*v 372=r 432 at h
  have p22:=pivot_22 X Y Z W a b hX hY hZ hW v r hv
  have p96:=pivot_96 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot375
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p22 - ((((-1)*a)/(Y)))*p96 - ((((-1)*X*a)/(Y*W^2)))*p202 - ((((-1)*a)/(Y*W^2)))*p230 - (((1)/(Y^2)))*p320)*(1/((1)))

def rhsPivot376 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 444 - (((1)/(Y^2)))*rhsPivot115 X Y Z W a b r - ((1))*rhsPivot245 X Y Z W a b r - (((1)/(W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot263 X Y Z W a b r - ((((-1)*X*Y^2)/(W^2)))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot349 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot354 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y*a)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot367 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_376 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y^2)/(W^2)) + ((1*X*Y*a)/(W^2)))*v 370 + ((((-1))/(Y^2*W^2)) + (((-1)*a)/(Y)) + (((-2))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-2)*Y^2)/(W^2)) + ((1*X)/(Y^2*W^2)) + (((-2)*X*a)/(Y*W^2)) + ((1*X*Z*a)/(Y*W^2)) + ((3*X)/(W^2)) + ((1*X*a^2)/(W^2)) + (((-2)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 390 + (((1*X*a)/(2*Y*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(W^2)) + ((3*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((7*X^2)/(2*W^2)) + ((1*X^2*a^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a^3)/(W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((4*X^3*a)/(Y*W^2)) + (((-1)*X^3*Z*a)/(Y*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((3*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4*a)/(Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4)/(2*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z*a^2)/(2*W^2)) + ((1*X^4*Y*a^3)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(2*W^2)) + ((1*X^5)/(W^2)) + ((1*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 435 + ((1))*v 448=rhsPivot376 X Y Z W a b r := by
  have h:=hv 444
  change ((1))*v 54 + ((((-1)*a)/(Y)))*v 162 + ((1))*v 224 + ((1))*v 394 + (((1)/(Y^2)))*v 486=r 444 at h
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v r hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p263:=pivot_263 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p367:=pivot_367 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot376
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2)))*p115 - ((1))*p245 - (((1)/(W^2)))*p256 - ((1))*p263 - ((((-1)*X*Y^2)/(W^2)))*p264 - ((1))*p349 - ((((-1)*a)/(Y)))*p354 - ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y*a)/(W^2)))*p357 - ((1))*p367)*(1/((((-1))/(X))))

def rhsPivot377 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 445 - ((1))*rhsPivot29 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot204 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot262 X Y Z W a b r - ((1))*rhsPivot299 X Y Z W a b r - (((1*X*a)/(Y)))*rhsPivot313 X Y Z W a b r - (((1*X^3*a)/(Y)))*rhsPivot353 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_377 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 62 + (((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 370 + (((1)/(Y^2*W^2)) + ((1*a)/(Y)) + (((-1)*X)/(Y^2*W^2)))*v 390 + ((((-1)*X*a)/(2*Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)))*v 435=rhsPivot377 X Y Z W a b r := by
  have h:=hv 445
  change (((1)/(Y^2)))*v 48 + ((1))*v 62 + ((((-1)*a)/(Y)))*v 186 + ((1))*v 232 + ((1))*v 402=r 445 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v r hv
  have p204:=pivot_204 X Y Z W a b hX hY hZ hW v r hv
  have p262:=pivot_262 X Y Z W a b hX hY hZ hW v r hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v r hv
  have p313:=pivot_313 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot377
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p29 - ((((-1)*a)/(Y)))*p204 - (((1)/(Y^2)))*p262 - ((1))*p299 - (((1*X*a)/(Y)))*p313 - (((1*X^3*a)/(Y)))*p353)*(1/((1)))

def rhsPivot378 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 450 - ((1))*rhsPivot42 X Y Z W a b r - ((1))*rhsPivot103 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot214 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot223 X Y Z W a b r - ((1))*rhsPivot280 X Y Z W a b r - (((1*a)/(Y)))*rhsPivot332 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot341 X Y Z W a b r - (((-1)))*rhsPivot342 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot357 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_378 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 142 + ((((-1)*Y^2)/(W^2)))*v 370 + (((2)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-3)*X)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 390 + ((((-3)*X)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-4)*X^2)/(W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(2*Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + (((-1)*X^5)/(W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 435=rhsPivot378 X Y Z W a b r := by
  have h:=hv 450
  change ((1))*v 71 + (((1)/(Y^2)))*v 129 + ((((-1)*a)/(Y)))*v 213 + ((1))*v 241 + ((1))*v 411=r 450 at h
  have p42:=pivot_42 X Y Z W a b hX hY hZ hW v r hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v r hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v r hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v r hv
  have p280:=pivot_280 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot378
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p42 - ((1))*p103 - (((1)/(Y^2)))*p214 - ((((-1)*a)/(Y)))*p223 - ((1))*p280 - (((1*a)/(Y)))*p332 - ((((-1))/(Y^2)))*p341 - (((-1)))*p342 - (((1*Y^2)/(X*W^2)))*p357)*(1/((((-1))/(X))))

def rhsPivot379 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 451 - ((1))*rhsPivot160 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot256 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot325 X Y Z W a b r - ((1))*rhsPivot334 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_379 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(Y^2)))*v 138 + ((((-1)*Y*a)/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 390 + ((1))*v 412 + ((((-1)*Y*a)/(W^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X*a^2)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + (((-1)*X^2*Y*a)/(W^2)))*v 435=rhsPivot379 X Y Z W a b r := by
  have h:=hv 451
  change ((1))*v 72 + (((1)/(Y^2)))*v 138 + ((((-1)*a)/(Y)))*v 216 + ((1))*v 242 + ((1))*v 412=r 451 at h
  have p160:=pivot_160 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p325:=pivot_325 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot379
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p160 - (((1*X)/(Y^2*W^2)))*p236 - ((((-1))/(W^2)))*p256 - ((((-1)*a)/(Y)))*p325 - ((1))*p334)*(1/((1)))

def rhsPivot380 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 452 - ((1))*rhsPivot48 X Y Z W a b r - ((1))*rhsPivot104 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot198 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot269 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot274 X Y Z W a b r - ((((-1)*X*Y*a)/(W^2)))*rhsPivot357 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_380 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 74 + ((((-1)*X*Y*a)/(W^2)))*v 370 + (((2)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((2*X*a)/(Y*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + (((-1)*X*a^2)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*v 390 + (((1*X)/(2*Y^2*W^2)) + ((1*X)/(Y^2)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(2*W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2)) + (((-3)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + (((-4)*X^3*a)/(Y*W^2)) + ((1*X^3*Z*a)/(Y*W^2)) + (((-3)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((1*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4*Z*a^2)/(2*W^2)) + (((-1)*X^4*Y*a^3)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=rhsPivot380 X Y Z W a b r := by
  have h:=hv 452
  change ((1))*v 74 + (((1)/(Y^2)))*v 156 + ((((-1)*a)/(Y)))*v 222 + ((1))*v 244 + ((1))*v 414=r 452 at h
  have p48:=pivot_48 X Y Z W a b hX hY hZ hW v r hv
  have p104:=pivot_104 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p269:=pivot_269 X Y Z W a b hX hY hZ hW v r hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot380
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p48 - ((1))*p104 - (((1*X)/(W^2)))*p198 - ((((-1))/(W^2)))*p230 - (((1)/(Y^2)))*p269 - ((((-1)*a)/(Y)))*p274 - ((((-1)*X*Y*a)/(W^2)))*p357)*(1/((1)))

def rhsPivot381 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 454 - ((1))*rhsPivot162 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot180 X Y Z W a b r - ((1))*rhsPivot188 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*X)/(W^2)))*rhsPivot257 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot261 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot288 X Y Z W a b r - ((((-1)*Y*a)/(W^2)))*rhsPivot328 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot353 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_381 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 76 + ((((-1))/(X*W^2)))*v 370 + ((((-1))/(X^2*Y^2)) + ((1)/(X*Y^2*W^2)) + ((1*X)/(Y^2*W^2)) + (((-1)*X*Y*a)/(W^2)))*v 390 + (((1)/(2*X*Y^2*W^2)) + ((1*a)/(2*X*Y*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^2)/(2*X*W^2)) + (((-1))/(2*Y^2*W^2)) + (((-1))/(W^2)) + ((1*a^2)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X)/(2*Y^2*W^2)) + (((-1)*X*a)/(2*Y*W^2)) + (((-1)*X)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^3*a)/(Y*W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)))*v 435=rhsPivot381 X Y Z W a b r := by
  have h:=hv 454
  change ((1))*v 76 + (((1)/(Y^2)))*v 174 + ((((-1)*a)/(Y)))*v 228 + ((1))*v 246 + ((1))*v 416=r 454 at h
  have p162:=pivot_162 X Y Z W a b hX hY hZ hW v r hv
  have p180:=pivot_180 X Y Z W a b hX hY hZ hW v r hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p288:=pivot_288 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot381
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p162 - ((((-1)*a)/(Y)))*p180 - ((1))*p188 - (((1*X)/(W^2)))*p189 - ((((-1)*X)/(W^2)))*p257 - (((1)/(Y^2)))*p261 - (((1)/(Y^2)))*p288 - ((((-1)*Y*a)/(W^2)))*p328 - ((((-1)*X)/(Y^2)))*p353)*(1/((1)))

def rhsPivot382 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 455 - ((1))*rhsPivot26 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot157 X Y Z W a b r - ((1))*rhsPivot176 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot189 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot208 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r - (((1*a)/(Y*W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot283 X Y Z W a b r - (((-1)))*rhsPivot307 X Y Z W a b r - ((1*X^2))*rhsPivot310 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot330 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot334 X Y Z W a b r - ((1))*rhsPivot354 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot355 X Y Z W a b r - (((1)/(X*W^2)) + ((1*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_382 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 154 + ((((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 370 + (((1)/(X*Y^2)) + ((2)/(Y^2*W^2)) + (((-1))/(Y^2)) + (((-1)*Z)/(Y^2*W^2)) + ((1)/(W^2)) + (1) + (((-1)*X*a)/(Y*W^2)) + ((3*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((2*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(Y^2)) + (((-1)*X*a)/(2*Y*W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-3)*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-5)*X^2)/(2*Y^2*W^2)) + ((1*X^2)/(Y^2)) + ((1*X^2*Z)/(Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + (((-3)*X^2*Y*a)/(2*W^2)) + ((3*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^3)/(Y^2*W^2)) + ((1*X^3)/(2*Y^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y*W^2)) + (((-4)*X^3)/(W^2)) + (((-1)*X^3*a^2)/(W^2)) + ((1*X^3)/(2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot382 X Y Z W a b r := by
  have h:=hv 455
  change ((1))*v 77 + (((1)/(Y^2)))*v 183 + ((((-1)*a)/(Y)))*v 231 + ((1))*v 247 + ((1))*v 417=r 455 at h
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v r hv
  have p176:=pivot_176 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p283:=pivot_283 X Y Z W a b hX hY hZ hW v r hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot382
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p26 - ((((-1)*a)/(Y)))*p157 - ((1))*p176 - ((((-1)*a)/(Y*W^2)))*p189 - (((1)/(Y^2*W^2)))*p208 - ((((-1))/(Y^2*W^2)))*p235 - (((1*a)/(Y*W^2)))*p257 - ((1))*p283 - (((-1)))*p307 - ((1*X^2))*p310 - (((1)/(Y^2)))*p330 - (((1)/(Y^2)))*p334 - ((1))*p354 - ((((-1))/(X*Y^2)))*p355 - (((1)/(X*W^2)) + ((1*Y^2)/(W^2)))*p357)*(1/((((-1))/(X))))

def rhsPivot383 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 464 - ((1))*rhsPivot109 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot170 X Y Z W a b r - ((1))*rhsPivot182 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot257 X Y Z W a b r - ((((-1)*Y*a)/(W^2)))*rhsPivot264 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot309 X Y Z W a b r - ((((-1)*X)/(Y^2)))*rhsPivot310 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot332 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot354 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot357 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_383 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1))/(X*W^2)))*v 370 + (((1)/(X^2*Y^2)) + ((1)/(X*Y^2*W^2)) + (((-1)*Z)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((2)/(X*W^2)) + (((-1))/(Y^2*W^2)) + ((1)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*Y*a)/(W^2)))*v 390 + ((1))*v 434 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + (((-1))/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((2)/(W^2)) + (((-1)*a^2)/(W^2)) + (((-1)*Y*a)/(W^2)) + (((-3)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + ((1*X^2*Z)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + ((1*X^2*Z*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)))*v 435=rhsPivot383 X Y Z W a b r := by
  have h:=hv 464
  change ((1))*v 94 + ((1))*v 264 + ((((-1)*a)/(Y)))*v 282 + (((1)/(Y^2)))*v 336 + ((1))*v 434=r 464 at h
  have p109:=pivot_109 X Y Z W a b hX hY hZ hW v r hv
  have p170:=pivot_170 X Y Z W a b hX hY hZ hW v r hv
  have p182:=pivot_182 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot383
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p109 - ((((-1)*a)/(Y)))*p170 - ((1))*p182 - (((1*X)/(W^2)))*p257 - ((((-1)*Y*a)/(W^2)))*p264 - (((1)/(Y^2)))*p309 - ((((-1)*X)/(Y^2)))*p310 - (((1)/(Y^2)))*p332 - ((((-1))/(X*Y^2)))*p354 - ((((-1))/(X*W^2)))*p357)*(1/((1)))

#print axioms pivot_383

def rhsPivot384 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 475 - ((1))*rhsPivot216 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot259 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot261 X Y Z W a b r - ((1))*rhsPivot272 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot346 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_384 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((-1)))*v 388 + (((2)/(X*Y^2*W^2)) + (((-1))/(Y^2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*X*a)/(Y*W^2)))*v 390 + (((1)/(2*Y^2*W^2)) + ((1)/(Y^2)) + ((1)/(W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a^3)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-5)*X)/(2*Y^2*W^2)) + ((1*X)/(2*Y^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X*a)/(2*Y)) + ((1*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + ((1*X)/(2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-2)*X^2*a)/(Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435 + ((1))*v 473=rhsPivot384 X Y Z W a b r := by
  have h:=hv 475
  change ((1))*v 133 + (((1)/(Y^2)))*v 177 + ((1))*v 303 + ((((-1)*a)/(Y)))*v 399 + ((1))*v 473=r 475 at h
  have p216:=pivot_216 X Y Z W a b hX hY hZ hW v r hv
  have p259:=pivot_259 X Y Z W a b hX hY hZ hW v r hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v r hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot384
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p216 - ((((-1)*a)/(Y)))*p259 - ((((-1)*a)/(Y)))*p261 - ((1))*p272 - (((1)/(Y^2)))*p346)*(1/((1)))

def rhsPivot385 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 482 - (((1)/(Y^2)))*rhsPivot114 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot124 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r - ((((-1)*X*a)/(Y)))*rhsPivot253 X Y Z W a b r - ((1))*rhsPivot333 X Y Z W a b r - ((1))*rhsPivot356 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_385 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 314 + ((((-1)*Y^2)/(W^2)))*v 370 + ((((-1))/(X)) + (((-1))/(Y^2*W^2)) + (1) + ((1*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(2*Y*W^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + (1*X) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-3)*X^2*a)/(2*Y*W^2)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + ((-1)*X^2) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot385 X Y Z W a b r := by
  have h:=hv 482
  change ((1))*v 144 + (((1)/(Y^2)))*v 276 + ((1))*v 314 + ((((-1)*a)/(Y)))*v 432 + ((1))*v 484=r 482 at h
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p124:=pivot_124 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p253:=pivot_253 X Y Z W a b hX hY hZ hW v r hv
  have p333:=pivot_333 X Y Z W a b hX hY hZ hW v r hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot385
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(Y^2)))*p114 - ((((-1)*a)/(Y)))*p124 - (((1)/(Y^2*W^2)))*p235 - ((((-1)*X*a)/(Y)))*p253 - ((1))*p333 - ((1))*p356)*(1/((1)))

def rhsPivot386 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 488 - ((1))*rhsPivot58 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot152 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*X*a)/(Y*W^2)))*rhsPivot202 X Y Z W a b r - ((1))*rhsPivot221 X Y Z W a b r - ((((-1)*a)/(Y*W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot299 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_386 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 158 + (((-1)*X))*v 164 + ((((-1)*X)/(W^2)))*v 370 + (((1*X)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)))*v 435=rhsPivot386 X Y Z W a b r := by
  have h:=hv 488
  change ((1))*v 158 + ((1))*v 328 + (((1)/(Y^2)))*v 402 + ((((-1)*a)/(Y)))*v 474 + ((1))*v 498=r 488 at h
  have p58:=pivot_58 X Y Z W a b hX hY hZ hW v r hv
  have p152:=pivot_152 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p202:=pivot_202 X Y Z W a b hX hY hZ hW v r hv
  have p221:=pivot_221 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p299:=pivot_299 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot386
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p58 - ((((-1)*a)/(Y)))*p152 - (((1*X)/(W^2)))*p194 - ((((-1)*X*a)/(Y*W^2)))*p202 - ((1))*p221 - ((((-1)*a)/(Y*W^2)))*p230 - (((1)/(Y^2)))*p299)*(1/((1)))

def rhsPivot387 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 491 - ((((-1)*a)/(Y)))*rhsPivot37 X Y Z W a b r - ((1))*rhsPivot47 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot331 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_387 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 164 + ((1))*v 334 + (((1)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 390 + ((((-1)*X^2)/(Y^2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^4)/(Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)))*v 435=rhsPivot387 X Y Z W a b r := by
  have h:=hv 491
  change ((1))*v 164 + ((1))*v 334 + (((1)/(Y^2)))*v 456 + ((((-1)*a)/(Y)))*v 492 + ((1))*v 504=r 491 at h
  have p37:=pivot_37 X Y Z W a b hX hY hZ hW v r hv
  have p47:=pivot_47 X Y Z W a b hX hY hZ hW v r hv
  have p331:=pivot_331 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot387
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p37 - ((1))*p47 - (((1)/(Y^2)))*p331)*(1/((1)))

def rhsPivot388 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 493 - ((1))*rhsPivot140 X Y Z W a b r - ((1))*rhsPivot188 X Y Z W a b r - (((1)/(W^2)))*rhsPivot227 X Y Z W a b r - ((1))*rhsPivot242 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot256 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot261 X Y Z W a b r - ((1))*rhsPivot385 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_388 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 212 + ((((-1))/(W^2)) + ((1*Y^2)/(W^2)))*v 370 + (((1)/(X)) + ((2)/(Y^2*W^2)) + ((1*b)/(Y^2*W)) + (((-1))/(W^2)) + ((-1)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((2*X)/(Y^2*W^2)) + ((1*X)/(W^2)))*v 390 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((3*X)/(2*Y^2*W^2)) + (((-1)*X)/(Y^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X*a)/(2*Y)) + ((1*X*a^2)/(2*W^2)) + (((-1)*X*a^2)/(2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + ((3*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*b)/(Y^2*W)) + ((2*X^2*a)/(Y*W^2)) + ((3*X^2)/(2*W^2)) + ((1*X^2*a^2)/(W^2)) + (1*X^2) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(Y^2*W^2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot388 X Y Z W a b r := by
  have h:=hv 493
  change ((1))*v 8 + ((((-1)*b)/(W)))*v 40 + ((1))*v 110 + (((1)/(W^2)))*v 200 + ((1))*v 212 + ((1))*v 314 + ((1))*v 416=r 493 at h
  have p140:=pivot_140 X Y Z W a b hX hY hZ hW v r hv
  have p188:=pivot_188 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p385:=pivot_385 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot388
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p140 - ((1))*p188 - (((1)/(W^2)))*p227 - ((1))*p242 - ((((-1)*b)/(W)))*p256 - (((1)/(Y^2)))*p261 - ((1))*p385)*(1/((1)))

def rhsPivot389 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 496 - ((1))*rhsPivot57 X Y Z W a b r - (((1)/(W^2)))*rhsPivot98 X Y Z W a b r - ((1))*rhsPivot171 X Y Z W a b r - (((1)/(W^2)))*rhsPivot192 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot206 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot208 X Y Z W a b r - ((1))*rhsPivot219 X Y Z W a b r - (((-1)))*rhsPivot229 X Y Z W a b r - (((1)/(Y^2)) + ((1)/(W^2)) + (1*X))*rhsPivot230 X Y Z W a b r - ((((-1)*X)/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot264 X Y Z W a b r - ((1))*rhsPivot326 X Y Z W a b r - ((1))*rhsPivot350 X Y Z W a b r - ((((-1))/(X)))*rhsPivot372 X Y Z W a b r - (((-1)))*rhsPivot384 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_389 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X^2*W^2)) + ((1)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y*a)/(W^2)))*v 370 + ((1))*v 388 + ((((-1))/(X^2*Y^2)) + (((-2))/(X*Y^2*W^2)) + (((-1))/(X)) + ((2)/(Y^2*W^2)) + (((-1))/(W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*b)/(W)))*v 390 + (((1)/(2*X*Y^2*W^2)) + ((1*a)/(2*X*Y*W^2)) + ((1)/(2*X*W^2)) + (((-1)*a)/(2*Y*W^2)) + ((3)/(2*W^2)) + (((-1)*a^2)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((5*X)/(2*Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + ((1*X)/(2*Y^2)) + ((1*X*a)/(Y*W^2)) + ((1*X*a)/(2*Y)) + ((1*X*a^2)/(2*W^2)) + ((1*X)/(2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + ((2*X^2*a)/(Y*W^2)) + ((1*X^2*a)/(2*Y)) + ((3*X^2)/(2*W^2)) + ((1*X^2*a^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2)/(2)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + (1*X^2*Y*a) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + (((-3)*X^3)/(2*Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + (((-1)*X^3*a)/(Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)))*v 435=rhsPivot389 X Y Z W a b r := by
  have h:=hv 496
  change ((1))*v 14 + ((((-1)*b)/(W)))*v 70 + ((1))*v 116 + ((1))*v 218 + ((1))*v 320 + (((1)/(W^2)))*v 350 + ((1))*v 422=r 496 at h
  have p57:=pivot_57 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p171:=pivot_171 X Y Z W a b hX hY hZ hW v r hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p206:=pivot_206 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p219:=pivot_219 X Y Z W a b hX hY hZ hW v r hv
  have p229:=pivot_229 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p264:=pivot_264 X Y Z W a b hX hY hZ hW v r hv
  have p326:=pivot_326 X Y Z W a b hX hY hZ hW v r hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v r hv
  have p372:=pivot_372 X Y Z W a b hX hY hZ hW v r hv
  have p384:=pivot_384 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot389
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p57 - (((1)/(W^2)))*p98 - ((1))*p171 - (((1)/(W^2)))*p192 - ((((-1))/(W^2)))*p195 - ((1))*p206 - (((1*X)/(Y^2*W^2)))*p208 - ((1))*p219 - (((-1)))*p229 - (((1)/(Y^2)) + ((1)/(W^2)) + (1*X))*p230 - ((((-1)*X)/(Y^2*W^2)))*p235 - (((1*X)/(Y^2*W^2)))*p257 - ((((-1)*b)/(W)))*p264 - ((1))*p326 - ((1))*p350 - ((((-1))/(X)))*p372 - (((-1)))*p384)*(1/(((-1))))

def rhsPivot390 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 500 - (((1)/(W^2)))*rhsPivot1 X Y Z W a b r - ((1))*rhsPivot64 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot98 X Y Z W a b r - ((1))*rhsPivot123 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot194 X Y Z W a b r - ((((-1)*X*b)/(Y^2*W)))*rhsPivot208 X Y Z W a b r - ((1))*rhsPivot209 X Y Z W a b r - (((1)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot342 X Y Z W a b r - ((1))*rhsPivot367 X Y Z W a b r - ((((-1))/(X)))*rhsPivot376 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_390 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y*a)/(W^2)))*v 370 + ((1))*v 377 + (((1*a)/(X*Y)) + ((2)/(X*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((2)/(Y^2*W^2)) + ((1*b)/(Y^2*W)) + ((2*a)/(Y*W^2)) + (((-1)*Z*a)/(Y*W^2)) + (((-2))/(W^2)) + (((-1)*a^2)/(W^2)) + ((1*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X)/(W^2)) + ((1*X*Y*a)/(W^2)))*v 390 + ((((-1)*a)/(2*Y*W^2)) + (((-1)*a^2)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((3*X)/(2*Y^2*W^2)) + ((1*X)/(2*Y^2)) + (((-1)*X*a)/(2*Y)) + (((-7)*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + ((1*X)/(2)) + ((1*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-2)*X^2*a)/(Y*W^2)) + ((1*X^2*Z*a)/(Y*W^2)) + ((1*X^2*a^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-3)*X^3)/(2*Y^2*W^2)) + (((-2)*X^3*a)/(Y*W^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(W^2)) + ((1*X^3*Z*a^2)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot390 X Y Z W a b r := by
  have h:=hv 500
  change ((1))*v 20 + ((((-1)*b)/(W)))*v 100 + ((1))*v 122 + ((1))*v 224 + ((1))*v 326 + ((1))*v 428 + (((1)/(W^2)))*v 500=r 500 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v r hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v r hv
  have p98:=pivot_98 X Y Z W a b hX hY hZ hW v r hv
  have p123:=pivot_123 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p208:=pivot_208 X Y Z W a b hX hY hZ hW v r hv
  have p209:=pivot_209 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p342:=pivot_342 X Y Z W a b hX hY hZ hW v r hv
  have p367:=pivot_367 X Y Z W a b hX hY hZ hW v r hv
  have p376:=pivot_376 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot390
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(W^2)))*p1 - ((1))*p64 - ((((-1)*b)/(W)))*p98 - ((1))*p123 - (((1*X)/(Y^2)))*p194 - ((((-1)*X*b)/(Y^2*W)))*p208 - ((1))*p209 - (((1)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)))*p235 - ((1))*p342 - ((1))*p367 - ((((-1))/(X)))*p376)*(1/(((-1))))

def rhsPivot391 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 435 - ((((-1)*a)/(Y)))*rhsPivot258 X Y Z W a b r - ((1))*rhsPivot266 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot284 X Y Z W a b r - ((1))*rhsPivot322 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot332 X Y Z W a b r - ((((-1))/(X)))*rhsPivot380 X Y Z W a b r - ((1))*rhsPivot390 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_391 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 292 + ((((-1)*Y^2)/(X*W^2)))*v 370 + (((1*a)/(X*Y)) + ((2)/(X*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((2)/(Y^2*W^2)) + ((1*b)/(Y^2*W)) + (((-2))/(W^2)) + ((1*Y^2)/(W^2)) + ((1*X*b)/(Y^2*W)) + ((2*X)/(W^2)))*v 390 + ((((-1)*Y*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X)/(2*Y^2)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X*a)/(2*Y)) + (((-3)*X)/(W^2)) + ((1*X)/(2)) + ((1*X*Z)/(W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2)/(W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*a^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-3)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 435=rhsPivot391 X Y Z W a b r := by
  have h:=hv 435
  change ((1))*v 37 + ((((-1)*a)/(Y)))*v 111 + ((1))*v 207 + (((1)/(Y^2)))*v 333 + ((1))*v 377=r 435 at h
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v r hv
  have p266:=pivot_266 X Y Z W a b hX hY hZ hW v r hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v r hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p380:=pivot_380 X Y Z W a b hX hY hZ hW v r hv
  have p390:=pivot_390 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot391
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*a)/(Y)))*p258 - ((1))*p266 - (((1)/(Y^2)))*p284 - ((1))*p322 - ((((-1)*a)/(Y)))*p332 - ((((-1))/(X)))*p380 - ((1))*p390)*(1/(((-1))))

def rhsPivot392 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 501 - (((1)/(W^2)))*rhsPivot5 X Y Z W a b r - ((1))*rhsPivot65 X Y Z W a b r - ((1))*rhsPivot87 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot99 X Y Z W a b r - ((1))*rhsPivot137 X Y Z W a b r - (((1)/(X)))*rhsPivot252 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r - ((1))*rhsPivot281 X Y Z W a b r - (((-1)))*rhsPivot334 X Y Z W a b r - ((((-1))/(X)))*rhsPivot356 X Y Z W a b r - ((1))*rhsPivot362 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_392 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X*W^2)))*v 370 + ((1))*v 378 + ((((-1))/(X^2)) + ((2)/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + (((-2))/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 390 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-3)*X)/(W^2)) + ((-1)*X) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-3)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)))*v 435=rhsPivot392 X Y Z W a b r := by
  have h:=hv 501
  change (((1)/(W^2)))*v 15 + ((1))*v 21 + ((((-1)*b)/(W)))*v 105 + ((1))*v 123 + ((1))*v 225 + ((1))*v 327 + ((1))*v 429=r 501 at h
  have p5:=pivot_5 X Y Z W a b hX hY hZ hW v r hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v r hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v r hv
  have p99:=pivot_99 X Y Z W a b hX hY hZ hW v r hv
  have p137:=pivot_137 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v r hv
  have p362:=pivot_362 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot392
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - (((1)/(W^2)))*p5 - ((1))*p65 - ((1))*p87 - ((((-1)*b)/(W)))*p99 - ((1))*p137 - (((1)/(X)))*p252 - (((1*Y^2)/(X*W^2)))*p256 - ((1))*p281 - (((-1)))*p334 - ((((-1))/(X)))*p356 - ((1))*p362)*(1/(((-1))))

def rhsPivot393 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 219 - ((((-1))/(X*W^2)))*rhsPivot3 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot4 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot9 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot10 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot13 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot15 X Y Z W a b r - ((1))*rhsPivot18 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot27 X Y Z W a b r - ((1))*rhsPivot38 X Y Z W a b r - ((1))*rhsPivot54 X Y Z W a b r - ((1))*rhsPivot74 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot77 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot91 X Y Z W a b r - (((1)/(X)))*rhsPivot114 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot121 X Y Z W a b r - ((1))*rhsPivot146 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot150 X Y Z W a b r - ((1))*rhsPivot161 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot223 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot233 X Y Z W a b r - ((1))*rhsPivot234 X Y Z W a b r - ((1))*rhsPivot272 X Y Z W a b r - ((1))*rhsPivot276 X Y Z W a b r - ((1))*rhsPivot284 X Y Z W a b r - ((1))*rhsPivot297 X Y Z W a b r - ((1))*rhsPivot301 X Y Z W a b r - (((-1)))*rhsPivot302 X Y Z W a b r - ((1))*rhsPivot319 X Y Z W a b r - ((((-1))/(X)))*rhsPivot325 X Y Z W a b r - ((1))*rhsPivot330 X Y Z W a b r - (((-1)))*rhsPivot332 X Y Z W a b r - ((1))*rhsPivot334 X Y Z W a b r - (((-1)))*rhsPivot336 X Y Z W a b r - ((((-1))/(X)))*rhsPivot340 X Y Z W a b r - ((((-1))/(X)))*rhsPivot345 X Y Z W a b r - (((-1)))*rhsPivot352 X Y Z W a b r - ((((-1))/(X)))*rhsPivot355 X Y Z W a b r - (((1*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot362 X Y Z W a b r - (((-1)))*rhsPivot392 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_393 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 138 + (((1)/(X^2*W^2)) + ((2)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((2)/(X*W^2)) + (((-2)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((4)/(W^2)) + ((-1)) + (((-3)*Y*a)/(W^2)) + ((4*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((2*Y^2)/(W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-3)*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + (((-5)*X)/(2*W^2)) + ((5*X)/(2)) + ((2*X*Z)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-2)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-4)*X^2)/(W^2)) + (2*X^2) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (1*X^2*Y^2) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-2)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot393 X Y Z W a b r := by
  have h:=hv 219
  change ((((-1))/(X*W^2)))*v 0 + ((((-1))/(X*W^2)))*v 30 + ((1))*v 33 + ((((-1))/(X*W^2)))*v 60 + ((1))*v 63 + ((((-1))/(X*W^2)))*v 90 + ((1))*v 93 + ((((-1))/(X*W^2)))*v 120 + ((1))*v 123 + ((((-1))/(X*W^2)))*v 150 + ((1))*v 153 + ((((-1))/(X*W^2)))*v 180 + ((1))*v 183 + ((((-1))/(X*W^2)))*v 210 + ((1))*v 213 + ((((-1))/(X*W^2)))*v 240 + ((1))*v 243 + ((((-1))/(X*W^2)))*v 270 + ((1))*v 273 + ((((-1))/(X*W^2)))*v 300 + ((1))*v 303 + ((((-1))/(X*W^2)))*v 330 + ((1))*v 333 + ((1))*v 363 + ((((-1))/(X*W^2)))*v 390 + ((1))*v 393 + ((((-1))/(X*W^2)))*v 420 + ((1))*v 423 + ((((-1))/(X*W^2)))*v 450 + ((1))*v 453 + ((((-1))/(X*W^2)))*v 480 + ((1))*v 483=r 219 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p18:=pivot_18 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p38:=pivot_38 X Y Z W a b hX hY hZ hW v r hv
  have p54:=pivot_54 X Y Z W a b hX hY hZ hW v r hv
  have p74:=pivot_74 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p114:=pivot_114 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p146:=pivot_146 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p234:=pivot_234 X Y Z W a b hX hY hZ hW v r hv
  have p272:=pivot_272 X Y Z W a b hX hY hZ hW v r hv
  have p276:=pivot_276 X Y Z W a b hX hY hZ hW v r hv
  have p284:=pivot_284 X Y Z W a b hX hY hZ hW v r hv
  have p297:=pivot_297 X Y Z W a b hX hY hZ hW v r hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v r hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v r hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v r hv
  have p325:=pivot_325 X Y Z W a b hX hY hZ hW v r hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v r hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v r hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p362:=pivot_362 X Y Z W a b hX hY hZ hW v r hv
  have p392:=pivot_392 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot393
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p3 - ((((-1))/(X*W^2)))*p4 - ((((-1))/(X*W^2)))*p9 - ((((-1))/(X*W^2)))*p10 - ((((-1))/(X*W^2)))*p13 - ((((-1))/(X*W^2)))*p15 - ((1))*p18 - ((((-1))/(X*W^2)))*p27 - ((1))*p38 - ((1))*p54 - ((1))*p74 - ((((-1))/(X*W^2)))*p77 - ((((-1))/(X*W^2)))*p91 - (((1)/(X)))*p114 - ((((-1))/(X*W^2)))*p121 - ((1))*p146 - ((((-1))/(X*W^2)))*p150 - ((1))*p161 - ((((-1))/(W^2)))*p189 - ((((-1))/(X*W^2)))*p195 - ((1))*p223 - (((1)/(X*W^2)))*p230 - ((((-1))/(X*W^2)))*p233 - ((1))*p234 - ((1))*p272 - ((1))*p276 - ((1))*p284 - ((1))*p297 - ((1))*p301 - (((-1)))*p302 - ((1))*p319 - ((((-1))/(X)))*p325 - ((1))*p330 - (((-1)))*p332 - ((1))*p334 - (((-1)))*p336 - ((((-1))/(X)))*p340 - ((((-1))/(X)))*p345 - (((-1)))*p352 - ((((-1))/(X)))*p355 - (((1*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)))*p357 - ((1))*p362 - (((-1)))*p392)*(1/(((-1))))

def rhsPivot394 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 534 - ((1))*rhsPivot2 X Y Z W a b r - ((1))*rhsPivot55 X Y Z W a b r - (((1)/(W^2)))*rhsPivot196 X Y Z W a b r - ((1))*rhsPivot265 X Y Z W a b r - ((1))*rhsPivot301 X Y Z W a b r - ((((-1))/(X)))*rhsPivot334 X Y Z W a b r - (((-1)))*rhsPivot393 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_394 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 189 + (((1)/(X^2*W^2)) + ((2)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((4)/(X*W^2)) + (((-2)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-3)*Y*a)/(X*W^2)) + ((3*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((3)/(W^2)) + ((-1)) + (((-3)*Y*a)/(W^2)) + ((4*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 390 + ((((-1))/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + (((-2)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((2*Y^2)/(W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-3)*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + (((-3)*X)/(W^2)) + ((5*X)/(2)) + ((2*X*Z)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-2)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-4)*X^2)/(W^2)) + (2*X^2) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (1*X^2*Y^2) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-2)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot394 X Y Z W a b r := by
  have h:=hv 534
  change ((1))*v 87 + (((1)/(W^2)))*v 135 + ((1))*v 189 + ((1))*v 291 + ((1))*v 393 + ((((-1)*b)/(W)))*v 435 + ((1))*v 495=r 534 at h
  have p2:=pivot_2 X Y Z W a b hX hY hZ hW v r hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v r hv
  have p301:=pivot_301 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot394
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p2 - ((1))*p55 - (((1)/(W^2)))*p196 - ((1))*p265 - ((1))*p301 - ((((-1))/(X)))*p334 - (((-1)))*p393)*(1/((1)))

def rhsPivot395 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 425 - ((1))*rhsPivot63 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot199 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot222 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot275 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot320 X Y Z W a b r - (((1*a)/(X*Y)))*rhsPivot338 X Y Z W a b r - (((1*a)/(Y)))*rhsPivot351 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot353 X Y Z W a b r - (((1*X*Y*a)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot394 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_395 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 359 + ((((-1))/(X^3*W^2)) + (((-1)*X)/(W^2)) + ((1*X*Y*a)/(W^2)))*v 370 + ((((-1))/(X^4*Y^2)) + ((1)/(X^3*Y^2*W^2)) + (((-1))/(X^2*W^2)) + (((-2))/(X^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-2)*a)/(X*Y*W^2)) + (((-4))/(X*W^2)) + ((1*a^2)/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((3*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1*a)/(Y)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X*a)/(Y*W^2)) + ((1*X*Z*a)/(Y*W^2)) + ((1*X*a^2)/(W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(2*X^3*Y^2*W^2)) + ((1*a)/(2*X^3*Y*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^2)/(2*X^3*W^2)) + (((-1))/(2*X^2*Y^2*W^2)) + (((-1))/(X^2*W^2)) + ((1*a^2)/(2*X^2*W^2)) + (((-1)*Y^2)/(2*X^2*W^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*a*b)/(Y*W)) + (((-1))/(W^2)) + ((1*a^2)/(2*W^2)) + ((2*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + ((1*Y*a^3)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((3*X*a)/(2*Y*W^2)) + ((2*X)/(W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-5)*X)/(2)) + (((-2)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^3*a^3)/(2*W^2)) + ((1*X*Y^4*a^2)/(W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(Y)) + ((4*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + (((-3)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((7*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((7*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*Z*a)/(Y*W^2)) + ((2*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Z)/(W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + ((-1)*X^3*Y*a) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4*a)/(Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + (((-1)*X^4*Z*a^2)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y*a^3)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((3*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((3*X^4*Y^3*a)/(2*W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot395 X Y Z W a b r := by
  have h:=hv 425
  change ((1))*v 19 + ((((-1)*a)/(Y)))*v 57 + (((1)/(Y^2)))*v 171 + ((1))*v 189 + ((1))*v 359=r 425 at h
  have p63:=pivot_63 X Y Z W a b hX hY hZ hW v r hv
  have p199:=pivot_199 X Y Z W a b hX hY hZ hW v r hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v r hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  have p338:=pivot_338 X Y Z W a b hX hY hZ hW v r hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p394:=pivot_394 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot395
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p63 - (((1)/(X*Y^2)))*p199 - (((1)/(Y^2)))*p222 - ((((-1)*a)/(Y)))*p275 - ((((-1))/(Y^2)))*p320 - (((1*a)/(X*Y)))*p338 - (((1*a)/(Y)))*p351 - ((((-1))/(X*Y^2)))*p353 - (((1*X*Y*a)/(W^2)))*p357 - ((1))*p394)*(1/((1)))

def rhsPivot396 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 437 - ((1))*rhsPivot211 X Y Z W a b r - ((1))*rhsPivot270 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot298 X Y Z W a b r - ((1))*rhsPivot323 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot328 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot338 X Y Z W a b r - (((-1)))*rhsPivot340 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot362 X Y Z W a b r - (((-1)))*rhsPivot368 X Y Z W a b r - (((1*a)/(Y)))*rhsPivot392 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_396 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 296 + ((((-1)*Y*a)/(X*W^2)) + (((-1)*X)/(W^2)))*v 370 + ((((-1)*a)/(X^2*Y)) + ((1)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + ((1*a*b)/(X*Y*W)) + ((1*a)/(X*Y)) + (((-1))/(X*W^2)) + (((-2))/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*a^2)/(W^2)) + (((-1)*b)/(W)) + (((-1)*Y*a)/(W^2)) + ((2*X)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + ((2*X)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 390 + (((1*a)/(2*X*Y*W^2)) + ((1*a^2)/(2*X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1)/(Y^2*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-3)*X*a)/(2*Y*W^2)) + (((-1)*X*a)/(Y)) + (((-1)*X)/(2*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X)/(2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + (((-2)*X^2*a)/(Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + ((3*X^2)/(2*W^2)) + (((-2)*X^2*a^2)/(W^2)) + (((-1)*X^2*a^2)/(2)) + (((-3)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-3)*X^2*Y^2)/(2*W^2)) + (((-3)*X^3)/(Y^2*W^2)) + ((1*X^3*Z)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((1*X^4*Z*a)/(2*Y*W^2)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y^2)/(2*W^2)))*v 435=rhsPivot396 X Y Z W a b r := by
  have h:=hv 437
  change ((1))*v 41 + ((((-1)*a)/(Y)))*v 123 + ((1))*v 211 + (((1)/(Y^2)))*v 369 + ((1))*v 381=r 437 at h
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v r hv
  have p270:=pivot_270 X Y Z W a b hX hY hZ hW v r hv
  have p298:=pivot_298 X Y Z W a b hX hY hZ hW v r hv
  have p323:=pivot_323 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  have p338:=pivot_338 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  have p362:=pivot_362 X Y Z W a b hX hY hZ hW v r hv
  have p368:=pivot_368 X Y Z W a b hX hY hZ hW v r hv
  have p392:=pivot_392 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot396
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p211 - ((1))*p270 - (((1)/(Y^2)))*p298 - ((1))*p323 - ((((-1))/(X*W^2)))*p328 - ((((-1))/(Y^2)))*p338 - (((-1)))*p340 - ((((-1)*a)/(Y)))*p362 - (((-1)))*p368 - (((1*a)/(Y)))*p392)*(1/(((-1))))

def rhsPivot397 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 353 - ((1))*rhsPivot282 X Y Z W a b r - ((1*X))*rhsPivot306 X Y Z W a b r - (((-1)))*rhsPivot336 X Y Z W a b r - (((-1)*X))*rhsPivot380 X Y Z W a b r - (((1)/(X)))*rhsPivot396 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_397 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1*Y*a)/(X^2*W^2)) + ((1)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)))*v 370 + (((1*a)/(X^3*Y)) + (((-1))/(X^2*Y^2*W^2)) + (((-1)*a)/(X^2*Y*W^2)) + (((-1)*a*b)/(X^2*Y*W)) + (((-1)*a)/(X^2*Y)) + ((1)/(X^2*W^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-1)*a^2)/(X*W^2)) + ((1*b)/(X*W)) + ((1*Y*a)/(X*W^2)) + (((-2))/(Y^2*W^2)) + ((1*Z)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-3))/(W^2)) + ((1*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((2*X^2*a)/(Y*W^2)) + (((-1)*X^2*Z*a)/(Y*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^3*a)/(Y*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y*a)/(W^2)))*v 390 + ((1))*v 403 + ((((-1)*a)/(2*X^2*Y*W^2)) + (((-1)*a^2)/(2*X^2*W^2)) + (((-1)*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1))/(X*Y^2*W^2)) + ((1)/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + ((3*a)/(2*Y*W^2)) + ((1*a)/(Y)) + ((1)/(2*W^2)) + (((-1)*a^2)/(2*W^2)) + (((-1))/(2)) + (((-1)*Y*a)/(2)) + ((1*Y^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((2*X*a)/(Y*W^2)) + ((1*X*a)/(2*Y)) + (((-5)*X)/(2*W^2)) + ((2*X*a^2)/(W^2)) + ((1*X*a^2)/(2)) + ((3*X*Y*a)/(2*W^2)) + ((1*X*Y*a)/(2)) + ((2*X*Y^2)/(W^2)) + ((1*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((7*X^2)/(2*Y^2*W^2)) + ((1*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(Y^2*W^2)) + ((1*X^3)/(2*Y^2)) + (((-1)*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3)/(2)) + (((-1)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + ((1*X^4)/(2*Y^2*W^2)) + (((-4)*X^4*a)/(Y*W^2)) + ((1*X^4*Z*a)/(Y*W^2)) + (((-3)*X^4)/(2*W^2)) + (((-1)*X^4*Y*a^3)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)) + ((1*X^5)/(Y^2*W^2)) + (((-1)*X^5*a)/(2*Y*W^2)) + ((1*X^5*Z*a)/(2*Y*W^2)) + ((1*X^5*Z*a^2)/(2*W^2)) + (((-1)*X^5*Y*a^3)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 435=rhsPivot397 X Y Z W a b r := by
  have h:=hv 353
  change ((1))*v 148 + (((1)/(X)))*v 296 + ((1))*v 403=r 353 at h
  have p282:=pivot_282 X Y Z W a b hX hY hZ hW v r hv
  have p306:=pivot_306 X Y Z W a b hX hY hZ hW v r hv
  have p336:=pivot_336 X Y Z W a b hX hY hZ hW v r hv
  have p380:=pivot_380 X Y Z W a b hX hY hZ hW v r hv
  have p396:=pivot_396 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot397
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p282 - ((1*X))*p306 - (((-1)))*p336 - (((-1)*X))*p380 - (((1)/(X)))*p396)*(1/((1)))

def rhsPivot398 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 438 - ((1))*rhsPivot261 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot340 X Y Z W a b r - ((1))*rhsPivot388 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot392 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_398 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    (((1)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + ((1))*v 382 + (((1)/(X^2*Y^2)) + (((-2))/(X*Y^2*W^2)) + (((-1)*b)/(X*Y^2*W)) + (((-1))/(X*Y^2)) + (((-1))/(X)) + (((-1)*b)/(Y^2*W)) + ((1*a*b)/(Y*W)) + ((2)/(W^2)) + (1) + (((-2)*X)/(Y^2*W^2)) + ((1*X*Y*a)/(W^2)))*v 390 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + ((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + ((3*X)/(2*Y^2*W^2)) + ((2*X)/(Y^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)))*v 435=rhsPivot398 X Y Z W a b r := by
  have h:=hv 438
  change ((1))*v 42 + ((((-1)*a)/(Y)))*v 126 + ((1))*v 212 + (((1)/(Y^2)))*v 378 + ((1))*v 382=r 438 at h
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  have p388:=pivot_388 X Y Z W a b hX hY hZ hW v r hv
  have p392:=pivot_392 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot398
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p261 - ((((-1)*a)/(Y)))*p340 - ((1))*p388 - (((1)/(Y^2)))*p392)*(1/((1)))

def rhsPivot399 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 448 - ((1))*rhsPivot41 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot258 X Y Z W a b r - ((1))*rhsPivot279 X Y Z W a b r - ((1))*rhsPivot303 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot322 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot332 X Y Z W a b r - ((1*X))*rhsPivot354 X Y Z W a b r - (((1*X*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r - (((-1)))*rhsPivot382 X Y Z W a b r - ((((-1))/(X)))*rhsPivot393 X Y Z W a b r)/((((-1))/(X)))

compact_elimination_proof
theorem pivot_399 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 308 + (((1*X)/(W^2)))*v 370 + ((((-1))/(X^2*W^2)) + (((-2))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-2))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(Y^2)) + (((-4))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(Y^2*W^2)) + ((1*X)/(Y^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(Y^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((1)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((3*X)/(2*W^2)) + (((-5)*X)/(2)) + (((-2)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(2*Y^2*W^2)) + ((1*X^2)/(Y^2)) + ((1*X^2*a)/(Y*W^2)) + ((3*X^2)/(W^2)) + ((1*X^2*a^2)/(2*W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((3*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((7*X^3)/(2*Y^2*W^2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*Z)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y)) + ((2*X^3)/(W^2)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + (((-1)*X^4)/(2*Y^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a)/(2*Y)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((3*X^4)/(2*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4)/(2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot399 X Y Z W a b r := by
  have h:=hv 448
  change ((1))*v 69 + (((1)/(Y^2)))*v 111 + ((((-1)*a)/(Y)))*v 207 + ((1))*v 239 + ((1))*v 409=r 448 at h
  have p41:=pivot_41 X Y Z W a b hX hY hZ hW v r hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v r hv
  have p279:=pivot_279 X Y Z W a b hX hY hZ hW v r hv
  have p303:=pivot_303 X Y Z W a b hX hY hZ hW v r hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p382:=pivot_382 X Y Z W a b hX hY hZ hW v r hv
  have p393:=pivot_393 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot399
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p41 - (((1)/(Y^2)))*p258 - ((1))*p279 - ((1))*p303 - ((((-1)*a)/(Y)))*p322 - (((1)/(Y^2)))*p332 - ((1*X))*p354 - (((1*X*Y^2)/(W^2)))*p357 - (((-1)))*p382 - ((((-1))/(X)))*p393)*(1/((((-1))/(X))))

#print axioms pivot_399

def rhsPivot400 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 503 - ((1))*rhsPivot156 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot260 X Y Z W a b r - ((1))*rhsPivot307 X Y Z W a b r - (((-1)*X^2))*rhsPivot310 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot329 X Y Z W a b r - ((((-1)*W*b)/(Y^2)))*rhsPivot334 X Y Z W a b r - (((-1)))*rhsPivot354 X Y Z W a b r - (((1)/(W^2)) + (((-1)*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot383 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_400 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 128 + (((1)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Y^2)/(W^2)))*v 370 + ((((-1))/(X^2*Y^2)) + (((-1))/(X*Y^2*W^2)) + ((1*Z)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-2))/(X*W^2)) + ((1)/(X)) + (((-1))/(Y^2*W^2)) + ((1*b)/(Y^2*W)) + ((1*Z)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*a*b)/(Y*W)) + (((-2))/(W^2)) + ((1*b)/(W)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + ((3*X)/(Y^2*W^2)) + (((-2)*X)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + (((1)/(2*X*Y^2*W^2)) + ((1*a)/(2*X*Y*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^2)/(2*X*W^2)) + ((1)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-5))/(2*W^2)) + ((1*a^2)/(W^2)) + ((1*Y*a)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((9*X)/(2*Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X)/(Y^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-5)*X)/(2*W^2)) + ((1*X*a^2)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^3*a)/(W^2)) + ((6*X^2)/(Y^2*W^2)) + (((-1)*X^2*b)/(2*Y^2*W)) + (((-3)*X^2*Z)/(2*Y^2*W^2)) + ((3*X^2*a)/(2*Y*W^2)) + ((1*X^2*a*b)/(2*Y*W)) + (((-1)*X^2*Z*a)/(2*Y*W^2)) + (((-7)*X^2)/(2*W^2)) + ((3*X^2*a^2)/(2*W^2)) + (((-1)*X^2*b)/(2*W)) + ((1*X^2*Z)/(2*W^2)) + ((3*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-1)*X^3*Z)/(2*Y^2*W^2)) + ((3*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*a^2)/(W^2)) + (((-1)*X^3*b)/(2*W)) + ((1*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)))*v 435=rhsPivot400 X Y Z W a b r := by
  have h:=hv 503
  change ((1))*v 26 + ((1))*v 128 + ((((-1)*b)/(W)))*v 130 + (((1)/(W^2)))*v 140 + ((1))*v 230 + ((1))*v 332 + ((1))*v 434=r 503 at h
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p260:=pivot_260 X Y Z W a b hX hY hZ hW v r hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p383:=pivot_383 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot400
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p156 - (((1*X)/(Y^2)))*p194 - ((1))*p260 - ((1))*p307 - (((-1)*X^2))*p310 - ((((-1)*b)/(W)))*p329 - ((((-1)*W*b)/(Y^2)))*p334 - (((-1)))*p354 - (((1)/(W^2)) + (((-1)*Y^2)/(W^2)))*p357 - ((1))*p383)*(1/((1)))

def rhsPivot401 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 505 - ((1))*rhsPivot29 X Y Z W a b r - ((1))*rhsPivot167 X Y Z W a b r - (((1*X)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - (((1)/(W^2)))*rhsPivot205 X Y Z W a b r - ((((-1))/(Y^2*W^2)) + (((-1)*X)/(W^2)))*rhsPivot230 X Y Z W a b r - ((((-1)*X)/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot329 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot334 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot372 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_401 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 334 + (((1)/(X*W^2)) + ((1)/(W^2)) + (((-1)*b)/(W)) + ((1*X*Y*a)/(W^2)))*v 370 + ((((-1))/(X*Y^2)) + ((1)/(Y^2*W^2)) + ((2*b)/(Y^2*W)) + (((-1))/(Y^2)) + (((-1)*Z*b)/(Y^2*W)) + (((-1)*a*b)/(Y*W)) + ((1*a)/(Y)) + ((2*b)/(W)) + ((-1)) + (((-1)*X*b)/(Y^2*W)) + ((1*X*b)/(W)))*v 390 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + ((1*X)/(Y^2*W^2)) + (((-3)*X*b)/(2*Y^2*W)) + (((-1)*X*a*b)/(Y*W)) + ((3*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + ((1*X*b)/(W)) + (((-1)*X*a^2*b)/(2*W)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y*a*b)/(W)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X^2)/(Y^2*W^2)) + (((-7)*X^2*b)/(2*Y^2*W)) + ((1*X^2)/(Y^2)) + ((1*X^2*Z*b)/(Y^2*W)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*a^2*b)/(2*W)) + (1*X^2) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(W)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*b)/(Y^2*W)) + ((1*X^3*Z*b)/(2*Y^2*W)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a*b)/(2*Y*W)) + ((1*X^3*Z*a*b)/(2*Y*W)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*b)/(2*W)) + (((-1)*X^3*a^2*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Z*b)/(2*W)) + (((-1)*X^3*Y*a*b)/(W)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 435=rhsPivot401 X Y Z W a b r := by
  have h:=hv 505
  change ((1))*v 28 + ((1))*v 130 + ((((-1)*b)/(W)))*v 140 + (((1)/(W^2)))*v 190 + ((1))*v 232 + ((1))*v 334 + ((1))*v 436=r 505 at h
  have p29:=pivot_29 X Y Z W a b hX hY hZ hW v r hv
  have p167:=pivot_167 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p372:=pivot_372 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot401
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p29 - ((1))*p167 - (((1*X)/(Y^2*W^2)))*p189 - (((1)/(W^2)))*p205 - ((((-1))/(Y^2*W^2)) + (((-1)*X)/(W^2)))*p230 - ((((-1)*X)/(Y^2*W^2)))*p257 - ((1))*p329 - (((1*W^2)/(Y^2)))*p334 - ((((-1)*b)/(W)))*p357 - ((1))*p372)*(1/((1)))

def rhsPivot402 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 506 - ((1))*rhsPivot15 X Y Z W a b r - (((1)/(W^2)))*rhsPivot27 X Y Z W a b r - ((1))*rhsPivot158 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot233 X Y Z W a b r - ((1))*rhsPivot277 X Y Z W a b r - ((1))*rhsPivot309 X Y Z W a b r - (((-1)*X))*rhsPivot310 X Y Z W a b r - ((((-1)*Y^2)/(W^2)))*rhsPivot329 X Y Z W a b r - (((-1)))*rhsPivot334 X Y Z W a b r - ((((-1))/(X)))*rhsPivot354 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot357 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_402 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 132 + ((((-1)*Y^2)/(X*W^2)))*v 370 + (((1)/(X^2)) + ((1)/(X*W^2)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)))*v 390 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-1))/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-1)*Y^3*a)/(W^2)) + (((-3)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(2*W)) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)))*v 435=rhsPivot402 X Y Z W a b r := by
  have h:=hv 506
  change ((1))*v 30 + ((1))*v 132 + ((((-1)*b)/(W)))*v 150 + ((1))*v 234 + (((1)/(W^2)))*v 240 + ((1))*v 336 + ((1))*v 438=r 506 at h
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p158:=pivot_158 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v r hv
  have p309:=pivot_309 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot402
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p15 - (((1)/(W^2)))*p27 - ((1))*p158 - ((((-1)*b)/(W)))*p233 - ((1))*p277 - ((1))*p309 - (((-1)*X))*p310 - ((((-1)*Y^2)/(W^2)))*p329 - (((-1)))*p334 - ((((-1))/(X)))*p354 - ((((-1)*Y^2)/(X*W^2)))*p357)*(1/((1)))

def rhsPivot403 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 220 - ((((-1))/(X*W^2)))*rhsPivot3 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot4 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot9 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot10 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot13 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot15 X Y Z W a b r - ((1))*rhsPivot26 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot27 X Y Z W a b r - ((1))*rhsPivot39 X Y Z W a b r - ((1))*rhsPivot55 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot77 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot91 X Y Z W a b r - ((1))*rhsPivot110 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot121 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot150 X Y Z W a b r - ((1))*rhsPivot159 X Y Z W a b r - ((1))*rhsPivot166 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot194 X Y Z W a b r - ((1))*rhsPivot200 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((1))*rhsPivot231 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot232 X Y Z W a b r - (((-1)))*rhsPivot261 X Y Z W a b r - ((1))*rhsPivot275 X Y Z W a b r - ((1))*rhsPivot281 X Y Z W a b r - ((1))*rhsPivot300 X Y Z W a b r - ((1))*rhsPivot318 X Y Z W a b r - ((1))*rhsPivot322 X Y Z W a b r - (((-1)))*rhsPivot334 X Y Z W a b r - (((-1)))*rhsPivot335 X Y Z W a b r - ((((-1))/(X)))*rhsPivot338 X Y Z W a b r - ((((-1))/(X)))*rhsPivot341 X Y Z W a b r - ((1))*rhsPivot346 X Y Z W a b r - (((-1)))*rhsPivot351 X Y Z W a b r - ((((-1))/(X)))*rhsPivot356 X Y Z W a b r - ((((-1)*X*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot363 X Y Z W a b r - ((1))*rhsPivot364 X Y Z W a b r - (((-1)))*rhsPivot402 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_403 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 372 + ((((-2))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-4))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 390 + (((1)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-1))/(2*W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-3)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-3)*Y^4)/(2*W^2)) + ((4*X)/(W^2)) + ((1*X*b)/(W)) + (((-3)*X)/(2)) + (((-2)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((5*X^2)/(W^2)) + ((1*X^2*b)/(2*W)) + (((-3)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((2*X^2*Y^2)/(W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((3*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((2*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 435=rhsPivot403 X Y Z W a b r := by
  have h:=hv 220
  change ((((-1))/(X*W^2)))*v 0 + ((1))*v 27 + ((((-1))/(X*W^2)))*v 30 + ((1))*v 57 + ((((-1))/(X*W^2)))*v 60 + ((1))*v 87 + ((((-1))/(X*W^2)))*v 90 + ((1))*v 117 + ((((-1))/(X*W^2)))*v 120 + ((1))*v 147 + ((1))*v 177 + ((((-1))/(X*W^2)))*v 180 + ((1))*v 207 + ((((-1))/(X*W^2)))*v 210 + ((1))*v 237 + ((((-1))/(X*W^2)))*v 240 + ((1))*v 267 + ((((-1))/(X*W^2)))*v 270 + ((1))*v 297 + ((((-1))/(X*W^2)))*v 300 + ((1))*v 327 + ((((-1))/(X*W^2)))*v 330 + ((1))*v 357 + ((((-1))/(X*W^2)))*v 360 + ((1))*v 387 + ((((-1))/(X*W^2)))*v 390 + ((1))*v 417 + ((((-1))/(X*W^2)))*v 420 + ((1))*v 447 + ((((-1))/(X*W^2)))*v 450 + ((1))*v 477 + ((((-1))/(X*W^2)))*v 480=r 220 at h
  have p3:=pivot_3 X Y Z W a b hX hY hZ hW v r hv
  have p4:=pivot_4 X Y Z W a b hX hY hZ hW v r hv
  have p9:=pivot_9 X Y Z W a b hX hY hZ hW v r hv
  have p10:=pivot_10 X Y Z W a b hX hY hZ hW v r hv
  have p13:=pivot_13 X Y Z W a b hX hY hZ hW v r hv
  have p15:=pivot_15 X Y Z W a b hX hY hZ hW v r hv
  have p26:=pivot_26 X Y Z W a b hX hY hZ hW v r hv
  have p27:=pivot_27 X Y Z W a b hX hY hZ hW v r hv
  have p39:=pivot_39 X Y Z W a b hX hY hZ hW v r hv
  have p55:=pivot_55 X Y Z W a b hX hY hZ hW v r hv
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v r hv
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p159:=pivot_159 X Y Z W a b hX hY hZ hW v r hv
  have p166:=pivot_166 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p200:=pivot_200 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p231:=pivot_231 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p261:=pivot_261 X Y Z W a b hX hY hZ hW v r hv
  have p275:=pivot_275 X Y Z W a b hX hY hZ hW v r hv
  have p281:=pivot_281 X Y Z W a b hX hY hZ hW v r hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v r hv
  have p318:=pivot_318 X Y Z W a b hX hY hZ hW v r hv
  have p322:=pivot_322 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v r hv
  have p338:=pivot_338 X Y Z W a b hX hY hZ hW v r hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  have p346:=pivot_346 X Y Z W a b hX hY hZ hW v r hv
  have p351:=pivot_351 X Y Z W a b hX hY hZ hW v r hv
  have p356:=pivot_356 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p363:=pivot_363 X Y Z W a b hX hY hZ hW v r hv
  have p364:=pivot_364 X Y Z W a b hX hY hZ hW v r hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot403
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1))/(X*W^2)))*p3 - ((((-1))/(X*W^2)))*p4 - ((((-1))/(X*W^2)))*p9 - ((((-1))/(X*W^2)))*p10 - ((((-1))/(X*W^2)))*p13 - ((((-1))/(X*W^2)))*p15 - ((1))*p26 - ((((-1))/(X*W^2)))*p27 - ((1))*p39 - ((1))*p55 - ((((-1))/(X*W^2)))*p77 - ((((-1))/(X*W^2)))*p91 - ((1))*p110 - ((((-1))/(X*W^2)))*p121 - ((((-1))/(X*W^2)))*p150 - ((1))*p159 - ((1))*p166 - ((((-1))/(W^2)))*p189 - ((((-1))/(W^2)))*p194 - ((1))*p200 - ((((-1))/(X*W^2)))*p230 - ((1))*p231 - ((((-1))/(X*W^2)))*p232 - (((-1)))*p261 - ((1))*p275 - ((1))*p281 - ((1))*p300 - ((1))*p318 - ((1))*p322 - (((-1)))*p334 - (((-1)))*p335 - ((((-1))/(X)))*p338 - ((((-1))/(X)))*p341 - ((1))*p346 - (((-1)))*p351 - ((((-1))/(X)))*p356 - ((((-1)*X*Y^2)/(W^2)))*p357 - ((1))*p363 - ((1))*p364 - (((-1)))*p402)*(1/(((-1))))

def rhsPivot404 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 226 - ((((-1)*Y^2)/(X*W^2)))*rhsPivot1 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot21 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot64 X Y Z W a b r - ((1))*rhsPivot65 X Y Z W a b r - ((1))*rhsPivot66 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot78 X Y Z W a b r - ((1))*rhsPivot80 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot91 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot92 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot93 X Y Z W a b r - ((1))*rhsPivot103 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot117 X Y Z W a b r - ((1))*rhsPivot130 X Y Z W a b r - ((1))*rhsPivot151 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot156 X Y Z W a b r - ((1))*rhsPivot157 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot164 X Y Z W a b r - (((1*Z)/(W^2)))*rhsPivot189 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot192 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot194 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot195 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot196 X Y Z W a b r - ((1))*rhsPivot211 X Y Z W a b r - ((1))*rhsPivot222 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot227 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot230 X Y Z W a b r - ((((-1)*Z)/(X*W^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot242 X Y Z W a b r - ((((-1)*Z)/(W^2)))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot258 X Y Z W a b r - ((1))*rhsPivot265 X Y Z W a b r - ((1))*rhsPivot278 X Y Z W a b r - ((1))*rhsPivot291 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot317 X Y Z W a b r - ((1*X))*rhsPivot320 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot328 X Y Z W a b r - ((1))*rhsPivot332 X Y Z W a b r - ((((-1))/(X)))*rhsPivot335 X Y Z W a b r - (((-1)))*rhsPivot340 X Y Z W a b r - ((1))*rhsPivot344 X Y Z W a b r - ((1))*rhsPivot350 X Y Z W a b r - ((((-1))/(X)))*rhsPivot353 X Y Z W a b r - ((((-1))/(X)))*rhsPivot402 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_404 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((((-1)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + ((((-1))/(X^4)) + ((1)/(X^3*W^2)) + ((1)/(X^3)) + ((1)/(X^2*W^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + ((1)/(X*W^2)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((2)/(W^2)) + ((1*b)/(W)) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + (((-1))/(X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1))/(2*W^2)) + (((-1)*b)/(W)) + ((2*Z)/(W^2)) + (((-3)*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((1*X*b)/(2*W)) + (((-1)*X)/(2)) + ((2*X*Y*a)/(W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-3)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-2)*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((7*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435 + ((1))*v 441=rhsPivot404 X Y Z W a b r := by
  have h:=hv 226
  change ((((-1)*Y^2)/(X*W^2)))*v 20 + ((1))*v 21 + ((1))*v 51 + ((((-1)*Y^2)/(X*W^2)))*v 80 + ((1))*v 81 + ((((-1)*Y^2)/(X*W^2)))*v 110 + ((1))*v 111 + ((((-1)*Y^2)/(X*W^2)))*v 140 + ((1))*v 141 + ((((-1)*Y^2)/(X*W^2)))*v 170 + ((1))*v 171 + ((((-1)*Y^2)/(X*W^2)))*v 200 + ((1))*v 201 + ((((-1)*Y^2)/(X*W^2)))*v 230 + ((1))*v 231 + ((((-1)*Y^2)/(X*W^2)))*v 260 + ((1))*v 261 + ((((-1)*Y^2)/(X*W^2)))*v 290 + ((1))*v 291 + ((((-1)*Y^2)/(X*W^2)))*v 320 + ((1))*v 321 + ((((-1)*Y^2)/(X*W^2)))*v 350 + ((1))*v 351 + ((((-1)*Y^2)/(X*W^2)))*v 380 + ((1))*v 381 + ((((-1)*Y^2)/(X*W^2)))*v 410 + ((1))*v 411 + ((((-1)*Y^2)/(X*W^2)))*v 440 + ((1))*v 441 + ((((-1)*Y^2)/(X*W^2)))*v 470 + ((1))*v 471 + ((((-1)*Y^2)/(X*W^2)))*v 500=r 226 at h
  have p1:=pivot_1 X Y Z W a b hX hY hZ hW v r hv
  have p21:=pivot_21 X Y Z W a b hX hY hZ hW v r hv
  have p64:=pivot_64 X Y Z W a b hX hY hZ hW v r hv
  have p65:=pivot_65 X Y Z W a b hX hY hZ hW v r hv
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v r hv
  have p78:=pivot_78 X Y Z W a b hX hY hZ hW v r hv
  have p80:=pivot_80 X Y Z W a b hX hY hZ hW v r hv
  have p91:=pivot_91 X Y Z W a b hX hY hZ hW v r hv
  have p92:=pivot_92 X Y Z W a b hX hY hZ hW v r hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v r hv
  have p103:=pivot_103 X Y Z W a b hX hY hZ hW v r hv
  have p117:=pivot_117 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p151:=pivot_151 X Y Z W a b hX hY hZ hW v r hv
  have p156:=pivot_156 X Y Z W a b hX hY hZ hW v r hv
  have p157:=pivot_157 X Y Z W a b hX hY hZ hW v r hv
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p192:=pivot_192 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p196:=pivot_196 X Y Z W a b hX hY hZ hW v r hv
  have p211:=pivot_211 X Y Z W a b hX hY hZ hW v r hv
  have p222:=pivot_222 X Y Z W a b hX hY hZ hW v r hv
  have p227:=pivot_227 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p242:=pivot_242 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p258:=pivot_258 X Y Z W a b hX hY hZ hW v r hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v r hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v r hv
  have p291:=pivot_291 X Y Z W a b hX hY hZ hW v r hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p335:=pivot_335 X Y Z W a b hX hY hZ hW v r hv
  have p340:=pivot_340 X Y Z W a b hX hY hZ hW v r hv
  have p344:=pivot_344 X Y Z W a b hX hY hZ hW v r hv
  have p350:=pivot_350 X Y Z W a b hX hY hZ hW v r hv
  have p353:=pivot_353 X Y Z W a b hX hY hZ hW v r hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot404
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((((-1)*Y^2)/(X*W^2)))*p1 - ((((-1)*Y^2)/(X*W^2)))*p21 - ((((-1)*Y^2)/(X*W^2)))*p64 - ((1))*p65 - ((1))*p66 - ((((-1)*Y^2)/(X*W^2)))*p78 - ((1))*p80 - (((1)/(X*W^2)))*p91 - ((((-1)*Y^2)/(X*W^2)))*p92 - ((((-1)*Y^2)/(X*W^2)))*p93 - ((1))*p103 - ((((-1)*Y^2)/(X*W^2)))*p117 - ((1))*p130 - ((1))*p151 - ((((-1)*Y^2)/(X*W^2)))*p156 - ((1))*p157 - ((((-1)*Y^2)/(X*W^2)))*p164 - (((1*Z)/(W^2)))*p189 - ((((-1)*Y^2)/(X*W^2)))*p192 - ((((-1))/(W^2)))*p194 - (((1*Y^2)/(X*W^2)))*p195 - ((((-1))/(W^2)))*p196 - ((1))*p211 - ((1))*p222 - ((((-1)*Y^2)/(X*W^2)))*p227 - ((((-1)*Y^2)/(X*W^2)))*p230 - ((((-1)*Z)/(X*W^2)))*p232 - ((((-1)*Y^2)/(X*W^2)))*p242 - ((((-1)*Z)/(W^2)))*p257 - ((1))*p258 - ((1))*p265 - ((1))*p278 - ((1))*p291 - ((((-1)*Y^2)/(X*W^2)))*p317 - ((1*X))*p320 - ((((-1)*Y^2)/(X*W^2)))*p328 - ((1))*p332 - ((((-1))/(X)))*p335 - (((-1)))*p340 - ((1))*p344 - ((1))*p350 - ((((-1))/(X)))*p353 - ((((-1))/(X)))*p402)*(1/((1)))

def rhsPivot405 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 420 - ((1))*rhsPivot129 X Y Z W a b r - ((((-1))/(Y^2*Z)))*rhsPivot130 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot153 X Y Z W a b r - ((((-1)*Y*a)/(X*W^2)))*rhsPivot205 X Y Z W a b r - (((1*a)/(X*Y*W^2)) + ((1*Y*a)/(W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot232 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot300 X Y Z W a b r - ((1))*rhsPivot330 X Y Z W a b r - ((1))*rhsPivot334 X Y Z W a b r - ((((-1))/(X)))*rhsPivot355 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot357 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot403 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_405 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 353 + (((1*Y^2)/(X*W^2)))*v 370 + ((((-2))/(X^2*Y^2)) + (((-2))/(X^2*W^2)) + (((-1))/(X^2)) + (((-5))/(X*Y^2*W^2)) + ((1*b)/(X*Y^2*W)) + ((1)/(X*Y^2)) + ((1*Z)/(X*Y^2*W^2)) + ((2*a)/(X*Y*W^2)) + (((-4))/(X*W^2)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-4))/(Y^2*W^2)) + ((1)/(Y^2)) + ((3*a)/(Y*W^2)) + (((-5))/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X^2)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 390 + (((1)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-3))/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-3))/(2*Y^2*W^2)) + ((1*b)/(Y^2*W)) + (((-1))/(2*Y^2)) + ((1*Z)/(2*Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*a)/(2*Y)) + ((1*Z*a)/(2*Y*W^2)) + (((-2))/(W^2)) + ((3*a^2)/(2*W^2)) + ((1)/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((7*X)/(2*Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-3)*X)/(2*Y^2)) + (((-2)*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*a)/(2*Y)) + ((1*X)/(W^2)) + ((1*X*a^2)/(2*W^2)) + (((-3)*X)/(2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((5*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(2*Y^2*W)) + (((-3)*X^2)/(2*Y^2)) + (((-1)*X^2*Z)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2*a*b)/(2*Y*W)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y*W^2)) + ((3*X^2)/(W^2)) + ((3*X^2*a^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((-1)*X^2) + (((-1)*X^2*Z)/(W^2)) + ((5*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((3*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + ((2*X^3)/(Y^2*W^2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*Z)/(Y^2*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4)/(2*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)))*v 435=rhsPivot405 X Y Z W a b r := by
  have h:=hv 420
  change ((1))*v 13 + ((((-1)*a)/(Y)))*v 39 + (((1)/(Y^2)))*v 117 + ((1))*v 183 + ((1))*v 353=r 420 at h
  have p129:=pivot_129 X Y Z W a b hX hY hZ hW v r hv
  have p130:=pivot_130 X Y Z W a b hX hY hZ hW v r hv
  have p153:=pivot_153 X Y Z W a b hX hY hZ hW v r hv
  have p205:=pivot_205 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p300:=pivot_300 X Y Z W a b hX hY hZ hW v r hv
  have p330:=pivot_330 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p403:=pivot_403 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot405
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p129 - ((((-1))/(Y^2*Z)))*p130 - ((((-1)*a)/(Y)))*p153 - ((((-1)*Y*a)/(X*W^2)))*p205 - (((1*a)/(X*Y*W^2)) + ((1*Y*a)/(W^2)))*p230 - (((1)/(X*Y^2*W^2)))*p232 - (((1)/(Y^2)))*p300 - ((1))*p330 - ((1))*p334 - ((((-1))/(X)))*p355 - (((1*Y^2)/(X*W^2)))*p357 - ((((-1))/(Y^2)))*p403)*(1/((1)))

def rhsPivot406 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 439 - ((1))*rhsPivot213 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot214 X Y Z W a b r - ((1))*rhsPivot223 X Y Z W a b r - (((-1)))*rhsPivot332 X Y Z W a b r - (((1*a)/(Y)))*rhsPivot341 X Y Z W a b r - ((1))*rhsPivot361 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot363 X Y Z W a b r - (((-1)))*rhsPivot400 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot402 X Y Z W a b r)/(((-1)))

compact_elimination_proof
theorem pivot_406 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 298 + ((((-1))/(W^2)) + ((1*Y^2)/(W^2)))*v 370 + ((((-1))/(X)) + (((-1)*b)/(Y^2*W)) + (((-1)*Z)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + (((-1)*b)/(W)) + ((1*Z)/(W^2)) + ((2*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-3)*X)/(Y^2*W^2)) + ((1*X)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 390 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-3)*X)/(Y^2*W^2)) + ((1*X)/(Y^2)) + (((-2)*X*a)/(Y*W^2)) + ((1*X*a)/(2*Y)) + ((2*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + ((1*X*a^2)/(2)) + ((1*X*Y*a)/(2)) + (((-2)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-5)*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2*Z)/(Y^2*W^2)) + (((-2)*X^2*a)/(Y*W^2)) + ((3*X^2)/(W^2)) + (((-3)*X^2*a^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3*Y*a*b)/(2*W)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 435=rhsPivot406 X Y Z W a b r := by
  have h:=hv 439
  change ((1))*v 43 + ((((-1)*a)/(Y)))*v 129 + ((1))*v 213 + ((1))*v 383 + (((1)/(Y^2)))*v 387=r 439 at h
  have p213:=pivot_213 X Y Z W a b hX hY hZ hW v r hv
  have p214:=pivot_214 X Y Z W a b hX hY hZ hW v r hv
  have p223:=pivot_223 X Y Z W a b hX hY hZ hW v r hv
  have p332:=pivot_332 X Y Z W a b hX hY hZ hW v r hv
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  have p361:=pivot_361 X Y Z W a b hX hY hZ hW v r hv
  have p363:=pivot_363 X Y Z W a b hX hY hZ hW v r hv
  have p400:=pivot_400 X Y Z W a b hX hY hZ hW v r hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot406
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p213 - ((((-1)*a)/(Y)))*p214 - ((1))*p223 - (((-1)))*p332 - (((1*a)/(Y)))*p341 - ((1))*p361 - (((1)/(Y^2)))*p363 - (((-1)))*p400 - ((((-1))/(Y^2)))*p402)*(1/(((-1))))

def rhsPivot407 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 440 - ((1))*rhsPivot341 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot345 X Y Z W a b r - ((1))*rhsPivot359 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot402 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_407 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 214 + ((((-1)*Y*a)/(X*W^2)) + (((-1)*X)/(W^2)))*v 370 + (((1*a)/(X^2*Y)) + ((1)/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-1)*Z*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + (((-1)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + ((2)/(Y^2*W^2)) + ((1)/(W^2)) + (((-1)*a^2)/(W^2)) + ((1*b)/(W)) + ((2*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 390 + ((((-1)*a)/(2*X*Y*W^2)) + (((-1)*a^2)/(2*X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*a)/(Y*W^2)) + ((1)/(W^2)) + (((-1)*a^2)/(W^2)) + ((2*Y*a)/(W^2)) + (((-1)*Y*a^3)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-2)*X*a)/(Y*W^2)) + (((-1)*X*a*b)/(Y*W)) + ((1*X*Z*a)/(Y*W^2)) + ((3*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-1)*X)/(2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2*a*b)/(2*Y*W)) + ((1*X^2*Z*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(2*W^2)) + (((-1)*X^2*a^2*b)/(2*W)) + ((1*X^2*Z*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*Z*a)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)))*v 435=rhsPivot407 X Y Z W a b r := by
  have h:=hv 440
  change ((1))*v 44 + ((((-1)*a)/(Y)))*v 132 + ((1))*v 214 + ((1))*v 384 + (((1)/(Y^2)))*v 396=r 440 at h
  have p341:=pivot_341 X Y Z W a b hX hY hZ hW v r hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v r hv
  have p359:=pivot_359 X Y Z W a b hX hY hZ hW v r hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot407
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p341 - (((1)/(Y^2)))*p345 - ((1))*p359 - ((((-1)*a)/(Y)))*p402)*(1/((1)))

def rhsPivot408 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 484 - ((1))*rhsPivot125 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot201 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot224 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot274 X Y Z W a b r - ((1))*rhsPivot278 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot310 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot319 X Y Z W a b r - ((1*X))*rhsPivot320 X Y Z W a b r - (((1*a)/(X*Y)))*rhsPivot345 X Y Z W a b r - (((1*a)/(Y)))*rhsPivot352 X Y Z W a b r - ((((-1))/(X^3*Y^2)))*rhsPivot354 X Y Z W a b r - ((((-1))/(X^3*W^2)) + (((-1)*X)/(W^2)))*rhsPivot357 X Y Z W a b r - ((((-1))/(X)))*rhsPivot402 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_408 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 151 + ((((-1))/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + (((-1)*X)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 370 + (((1)/(X^4*Y^2)) + ((1)/(X^3*Y^2*W^2)) + (((-1)*Z)/(X^3*Y^2*W^2)) + (((-1)*a)/(X^3*Y*W^2)) + ((2)/(X^3*W^2)) + ((1)/(X^3)) + (((-1))/(X^2*Y^2*W^2)) + ((1*a)/(X^2*Y*W^2)) + ((2)/(X^2*W^2)) + (((-1)*Z)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + ((1*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + (((-1)*a^2)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + (((-1)*a)/(Y)) + ((2*X)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + ((2*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 390 + ((((-1))/(2*X^3*Y^2*W^2)) + (((-1)*a)/(2*X^3*Y*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^2)/(2*X^3*W^2)) + (((-1))/(X^2*Y^2*W^2)) + (((-1)*a)/(X^2*Y*W^2)) + ((3)/(2*X^2*W^2)) + (((-1)*a^2)/(X^2*W^2)) + (((-3)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-7))/(2*X*Y^2*W^2)) + ((1*Z)/(X*Y^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*a^2)/(2*X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((3*Y^2)/(2*X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1))/(Y^2*W^2)) + ((1*Z)/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1)*a*b)/(Y*W)) + ((1*Z*a)/(2*Y*W^2)) + (((-2))/(W^2)) + (((-1)*a^2)/(W^2)) + (((-1)*b)/(W)) + ((3*Z)/(2*W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y*a^3)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*b)/(2*W)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2*b)/(2*W)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^3*a^3)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-3)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-7)*X^3)/(2*Y^2*W^2)) + ((1*X^3*Z)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((1*X^4*Z*a)/(2*Y*W^2)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y^2)/(2*W^2)))*v 435=rhsPivot408 X Y Z W a b r := by
  have h:=hv 484
  change ((1))*v 151 + ((1))*v 321 + (((1)/(Y^2)))*v 339 + ((((-1)*a)/(Y)))*v 453 + ((1))*v 491=r 484 at h
  have p125:=pivot_125 X Y Z W a b hX hY hZ hW v r hv
  have p201:=pivot_201 X Y Z W a b hX hY hZ hW v r hv
  have p224:=pivot_224 X Y Z W a b hX hY hZ hW v r hv
  have p274:=pivot_274 X Y Z W a b hX hY hZ hW v r hv
  have p278:=pivot_278 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p319:=pivot_319 X Y Z W a b hX hY hZ hW v r hv
  have p320:=pivot_320 X Y Z W a b hX hY hZ hW v r hv
  have p345:=pivot_345 X Y Z W a b hX hY hZ hW v r hv
  have p352:=pivot_352 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p402:=pivot_402 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot408
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p125 - (((1)/(Y^2)))*p201 - (((1)/(X*Y^2)))*p224 - ((((-1))/(Y^2)))*p274 - ((1))*p278 - ((((-1))/(X*Y^2)))*p310 - ((((-1)*a)/(Y)))*p319 - ((1*X))*p320 - (((1*a)/(X*Y)))*p345 - (((1*a)/(Y)))*p352 - ((((-1))/(X^3*Y^2)))*p354 - ((((-1))/(X^3*W^2)) + (((-1)*X)/(W^2)))*p357 - ((((-1))/(X)))*p402)*(1/((1)))

def rhsPivot409 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 511 - ((1))*rhsPivot42 X Y Z W a b r - ((1))*rhsPivot90 X Y Z W a b r - (((1)/(W^2)))*rhsPivot105 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot195 X Y Z W a b r - ((1))*rhsPivot218 X Y Z W a b r - ((((-1))/(X*Y^2*W^2)))*rhsPivot230 X Y Z W a b r - (((-1)))*rhsPivot245 X Y Z W a b r - ((1))*rhsPivot266 X Y Z W a b r - ((1))*rhsPivot289 X Y Z W a b r - ((((-1)*b)/(W)))*rhsPivot316 X Y Z W a b r - (((1*b)/(W)))*rhsPivot328 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot334 X Y Z W a b r - (((-1)))*rhsPivot349 X Y Z W a b r - (((1*Y^2)/(X*W^2)))*rhsPivot357 X Y Z W a b r - ((((-1))/(X)))*rhsPivot369 X Y Z W a b r - ((((-1))/(X)))*rhsPivot380 X Y Z W a b r - (((-1)))*rhsPivot391 X Y Z W a b r)/(((1)/(X)))

compact_elimination_proof
theorem pivot_409 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 346 + (((1*b)/(W)) + (((-1)*X*Y*a)/(W^2)))*v 370 + (((1)/(Y^2*W^2)) + (((-1))/(Y^2)) + ((1*a)/(Y*W^2)) + ((2*a)/(Y)) + ((-1)) + ((1*X*b)/(Y^2*W)) + ((2*X*a)/(Y*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + (((-1)*X*a^2)/(W^2)) + ((2*X*Y*a)/(W^2)) + ((1*X^2*b)/(Y^2*W)) + (((-1)*X^2*a)/(Y*W^2)) + ((1*X^2*b)/(W)) + ((1*X^2*Y*a)/(W^2)))*v 390 + (((1*X)/(Y^2*W^2)) + ((3*X)/(2*W^2)) + (((-1)*X*a^2)/(2*W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2)/(Y^2)) + (((-2)*X^2*a)/(Y*W^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + (1*X^2) + ((5*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-9)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(Y*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*a^2)/(2*W^2)) + ((1*X^3*b)/(W)) + ((1*X^3)/(2)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a^3)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*b)/(Y^2*W)) + (((-3)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a*b)/(2*Y*W)) + ((1*X^4*Z*a)/(2*Y*W^2)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*a^2*b)/(2*W)) + ((1*X^4*Z*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*a^3)/(2*W^2)) + (((-1)*X^4*Y*a*b)/(2*W)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 435=rhsPivot409 X Y Z W a b r := by
  have h:=hv 511
  change ((1))*v 37 + ((1))*v 139 + ((((-1)*b)/(W)))*v 185 + ((1))*v 241 + ((1))*v 343 + (((1)/(W^2)))*v 415 + ((1))*v 445=r 511 at h
  have p42:=pivot_42 X Y Z W a b hX hY hZ hW v r hv
  have p90:=pivot_90 X Y Z W a b hX hY hZ hW v r hv
  have p105:=pivot_105 X Y Z W a b hX hY hZ hW v r hv
  have p195:=pivot_195 X Y Z W a b hX hY hZ hW v r hv
  have p218:=pivot_218 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p245:=pivot_245 X Y Z W a b hX hY hZ hW v r hv
  have p266:=pivot_266 X Y Z W a b hX hY hZ hW v r hv
  have p289:=pivot_289 X Y Z W a b hX hY hZ hW v r hv
  have p316:=pivot_316 X Y Z W a b hX hY hZ hW v r hv
  have p328:=pivot_328 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  have p349:=pivot_349 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p369:=pivot_369 X Y Z W a b hX hY hZ hW v r hv
  have p380:=pivot_380 X Y Z W a b hX hY hZ hW v r hv
  have p391:=pivot_391 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot409
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p42 - ((1))*p90 - (((1)/(W^2)))*p105 - (((1)/(X*Y^2*W^2)))*p195 - ((1))*p218 - ((((-1))/(X*Y^2*W^2)))*p230 - (((-1)))*p245 - ((1))*p266 - ((1))*p289 - ((((-1)*b)/(W)))*p316 - (((1*b)/(W)))*p328 - (((1*W^2)/(X*Y^2)))*p334 - (((-1)))*p349 - (((1*Y^2)/(X*W^2)))*p357 - ((((-1))/(X)))*p369 - ((((-1))/(X)))*p380 - (((-1)))*p391)*(1/(((1)/(X))))

def rhsPivot410 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  (r 419 - ((1))*rhsPivot70 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot127 X Y Z W a b r - ((((-1)*X*a)/(Y*W^2)))*rhsPivot198 X Y Z W a b r - ((1))*rhsPivot203 X Y Z W a b r - (((1*a)/(Y*W^2)))*rhsPivot230 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot302 X Y Z W a b r - ((((-1)*X)/(W^2)))*rhsPivot357 X Y Z W a b r - (((-1)*X))*rhsPivot409 X Y Z W a b r)/((1))

compact_elimination_proof
theorem pivot_410 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) :
    ((1))*v 352 + ((((-1)*X)/(W^2)) + ((1*X*b)/(W)) + (((-1)*X^2*Y*a)/(W^2)))*v 370 + (((3*X)/(Y^2*W^2)) + (((-1)*X)/(Y^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((2*X*a)/(Y)) + ((2*X)/(W^2)) + ((-1)*X) + (((-1)*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((2*X^2*a)/(Y*W^2)) + (((-1)*X^2*Z*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^3*b)/(Y^2*W)) + (((-1)*X^3*a)/(Y*W^2)) + ((1*X^3*b)/(W)) + ((1*X^3*Y*a)/(W^2)))*v 390 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + ((5*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-9)*X^3)/(2*Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3)/(Y^2)) + ((1*X^3*Z)/(Y^2*W^2)) + (((-2)*X^3*a)/(Y*W^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3)/(2*W^2)) + (((-3)*X^3*a^2)/(2*W^2)) + (1*X^3) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a^3)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-3)*X^4)/(2*Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + (((-5)*X^4*a)/(Y*W^2)) + (((-1)*X^4*a)/(2*Y)) + ((3*X^4*Z*a)/(2*Y*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*a^2)/(W^2)) + ((1*X^4*b)/(W)) + ((1*X^4)/(2)) + (((-1)*X^4*a^2)/(2)) + ((1*X^4*Z)/(2*W^2)) + (((-3)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*a^3)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2)/(2)) + (((-1)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^5)/(2*Y^2*W^2)) + (((-1)*X^5*b)/(Y^2*W)) + (((-3)*X^5*a)/(2*Y*W^2)) + (((-1)*X^5*a*b)/(2*Y*W)) + ((1*X^5*Z*a)/(2*Y*W^2)) + (((-1)*X^5)/(2*W^2)) + (((-1)*X^5*a^2)/(2*W^2)) + (((-1)*X^5*a^2*b)/(2*W)) + ((1*X^5*Z*a^2)/(2*W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y*a^3)/(2*W^2)) + (((-1)*X^5*Y*a*b)/(2*W)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 435=rhsPivot410 X Y Z W a b r := by
  have h:=hv 419
  change ((1))*v 12 + ((((-1)*a)/(Y)))*v 36 + (((1)/(Y^2)))*v 108 + ((1))*v 182 + ((1))*v 352=r 419 at h
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v r hv
  have p127:=pivot_127 X Y Z W a b hX hY hZ hW v r hv
  have p198:=pivot_198 X Y Z W a b hX hY hZ hW v r hv
  have p203:=pivot_203 X Y Z W a b hX hY hZ hW v r hv
  have p230:=pivot_230 X Y Z W a b hX hY hZ hW v r hv
  have p302:=pivot_302 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p409:=pivot_409 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsPivot410
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) (h - ((1))*p70 - ((((-1)*a)/(Y)))*p127 - ((((-1)*X*a)/(Y*W^2)))*p198 - ((1))*p203 - (((1*a)/(Y*W^2)))*p230 - (((1)/(Y^2)))*p302 - ((((-1)*X)/(W^2)))*p357 - (((-1)*X))*p409)*(1/((1)))

#print axioms pivot_410

end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## SmallLevelThirtyFourUnitMMPInhomogeneousZeroBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex SmallLevelThirtyFourUnitMMP

def rhsZero0 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 265 - ((1))*rhsPivot70 X Y Z W a b r - ((1))*rhsPivot110 X Y Z W a b r - (((1)/(X)))*rhsPivot126 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot235 X Y Z W a b r - (((1)/(W^2)))*rhsPivot236 X Y Z W a b r - ((((-1)*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r

compact_elimination_proof
theorem zero_row_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero0 X Y Z W a b r=0 := by
  have h:=hv 265
  change ((1))*v 12 + (((1)/(X)))*v 24 + ((1))*v 267=r 265 at h
  have p70:=pivot_70 X Y Z W a b hX hY hZ hW v r hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero0
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p70 - ((1))*p110 - (((1)/(X)))*p126 - (((1)/(X*W^2)))*p235 - (((1)/(W^2)))*p236 - ((((-1)*Y^2)/(X*W^2)))*p256)

#print axioms zero_row_0

def rhsZero1 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 293 - ((1))*rhsPivot77 X Y Z W a b r - (((1)/(X)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot236 X Y Z W a b r - ((((-1)*Y^2)/(X)))*rhsPivot256 X Y Z W a b r

compact_elimination_proof
theorem zero_row_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero1 X Y Z W a b r=0 := by
  have h:=hv 293
  change ((1))*v 60 + (((1)/(X)))*v 120 + ((1))*v 315=r 293 at h
  have p77:=pivot_77 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero1
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p77 - (((1)/(X)))*p235 - ((1))*p236 - ((((-1)*Y^2)/(X)))*p256)

#print axioms zero_row_1

def rhsZero2 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 351 - (((1)/(X)))*rhsPivot164 X Y Z W a b r - ((1))*rhsPivot239 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot252 X Y Z W a b r - ((1))*rhsPivot255 X Y Z W a b r - (((1*Y^2)/(X)))*rhsPivot256 X Y Z W a b r

compact_elimination_proof
theorem zero_row_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero2 X Y Z W a b r=0 := by
  have h:=hv 351
  change ((1))*v 145 + (((1)/(X)))*v 290 + ((1))*v 400=r 351 at h
  have p164:=pivot_164 X Y Z W a b hX hY hZ hW v r hv
  have p239:=pivot_239 X Y Z W a b hX hY hZ hW v r hv
  have p252:=pivot_252 X Y Z W a b hX hY hZ hW v r hv
  have p255:=pivot_255 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero2
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - (((1)/(X)))*p164 - ((1))*p239 - (((1*W^2)/(X*Y^2)))*p252 - ((1))*p255 - (((1*Y^2)/(X)))*p256)

#print axioms zero_row_2

def rhsZero3 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 406 - ((1))*rhsPivot60 X Y Z W a b r - (((1)/(X)))*rhsPivot93 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot126 X Y Z W a b r - ((1))*rhsPivot141 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot235 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(X)))*rhsPivot256 X Y Z W a b r

compact_elimination_proof
theorem zero_row_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero3 X Y Z W a b r=0 := by
  have h:=hv 406
  change ((1))*v 235 + (((1)/(X)))*v 470 + ((1))*v 490=r 406 at h
  have p60:=pivot_60 X Y Z W a b hX hY hZ hW v r hv
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero3
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p60 - (((1)/(X)))*p93 - (((1*W^2)/(X*Y^2)))*p126 - ((1))*p141 - (((1)/(X*Y^2)))*p235 - (((1)/(Y^2)))*p236 - ((((-1))/(X)))*p256)

#print axioms zero_row_3

def rhsZero4 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 412 - (((1)/(X)))*rhsPivot86 X Y Z W a b r - (((1)/(W^2)))*rhsPivot141 X Y Z W a b r - ((1))*rhsPivot184 X Y Z W a b r - ((1))*rhsPivot186 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot235 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(X*W^2)))*rhsPivot256 X Y Z W a b r

compact_elimination_proof
theorem zero_row_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero4 X Y Z W a b r=0 := by
  have h:=hv 412
  change ((1))*v 251 + (((1)/(X)))*v 502 + ((1))*v 506=r 412 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v r hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v r hv
  have p184:=pivot_184 X Y Z W a b hX hY hZ hW v r hv
  have p186:=pivot_186 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero4
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - (((1)/(X)))*p86 - (((1)/(W^2)))*p141 - ((1))*p184 - ((1))*p186 - (((1)/(X*Y^2*W^2)))*p235 - (((1)/(Y^2*W^2)))*p236 - ((((-1))/(X*W^2)))*p256)

#print axioms zero_row_4

def rhsZero5 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 354 - ((1))*rhsPivot102 X Y Z W a b r - (((1)/(X)))*rhsPivot150 X Y Z W a b r - ((1))*rhsPivot189 X Y Z W a b r - ((1))*rhsPivot233 X Y Z W a b r - (((1)/(X)))*rhsPivot235 X Y Z W a b r - (((-1)))*rhsPivot257 X Y Z W a b r

compact_elimination_proof
theorem zero_row_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero5 X Y Z W a b r=0 := by
  have h:=hv 354
  change ((1))*v 150 + (((1)/(X)))*v 300 + ((1))*v 405=r 354 at h
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero5
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p102 - (((1)/(X)))*p150 - ((1))*p189 - ((1))*p233 - (((1)/(X)))*p235 - (((-1)))*p257)

#print axioms zero_row_5

def rhsZero6 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 411 - ((1))*rhsPivot177 X Y Z W a b r - (((1)/(X)))*rhsPivot178 X Y Z W a b r - ((1))*rhsPivot179 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot189 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot233 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot235 X Y Z W a b r - ((((-1))/(Y^2*W^2)))*rhsPivot257 X Y Z W a b r

compact_elimination_proof
theorem zero_row_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero6 X Y Z W a b r=0 := by
  have h:=hv 411
  change ((1))*v 248 + (((1)/(X)))*v 496 + ((1))*v 503=r 411 at h
  have p177:=pivot_177 X Y Z W a b hX hY hZ hW v r hv
  have p178:=pivot_178 X Y Z W a b hX hY hZ hW v r hv
  have p179:=pivot_179 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero6
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p177 - (((1)/(X)))*p178 - ((1))*p179 - (((1)/(Y^2*W^2)))*p189 - (((1)/(Y^2*W^2)))*p233 - (((1)/(X*Y^2*W^2)))*p235 - ((((-1))/(Y^2*W^2)))*p257)

#print axioms zero_row_6

def rhsZero7 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 436 - ((1))*rhsPivot121 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot235 X Y Z W a b r - ((1))*rhsPivot256 X Y Z W a b r - ((1*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot317 X Y Z W a b r - ((((-1)*W^2)/(Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero7 X Y Z W a b r=0 := by
  have h:=hv 436
  change ((1))*v 40 + ((((-1)*a)/(Y)))*v 120 + ((1))*v 210 + (((1)/(Y^2)))*v 360 + ((1))*v 380=r 436 at h
  have p121:=pivot_121 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p317:=pivot_317 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero7
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p121 - (((1)/(Y^2)))*p232 - ((((-1)*a)/(Y)))*p235 - ((1))*p256 - ((1*X))*p257 - ((1))*p317 - ((((-1)*W^2)/(Y^2)))*p334)

#print axioms zero_row_7

def rhsZero8 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 447 - ((1))*rhsPivot89 X Y Z W a b r - ((1))*rhsPivot102 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot131 X Y Z W a b r - ((1))*rhsPivot141 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot194 X Y Z W a b r - (((1)/(X*Y^2)) + ((1)/(X)))*rhsPivot235 X Y Z W a b r - ((((-1)*Y*a)/(X)))*rhsPivot256 X Y Z W a b r - (((1*W^2)/(X*Y^2)))*rhsPivot277 X Y Z W a b r - ((((-1))/(X)))*rhsPivot329 X Y Z W a b r - ((((-1)*W^2)/(X*Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero8 X Y Z W a b r=0 := by
  have h:=hv 447
  change ((1))*v 65 + (((1)/(Y^2)))*v 75 + ((((-1)*a)/(Y)))*v 195 + ((1))*v 235 + ((1))*v 405=r 447 at h
  have p89:=pivot_89 X Y Z W a b hX hY hZ hW v r hv
  have p102:=pivot_102 X Y Z W a b hX hY hZ hW v r hv
  have p131:=pivot_131 X Y Z W a b hX hY hZ hW v r hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v r hv
  have p194:=pivot_194 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero8
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p89 - ((1))*p102 - ((((-1)*a)/(Y)))*p131 - ((1))*p141 - (((1)/(Y^2)))*p194 - (((1)/(X*Y^2)) + ((1)/(X)))*p235 - ((((-1)*Y*a)/(X)))*p256 - (((1*W^2)/(X*Y^2)))*p277 - ((((-1))/(X)))*p329 - ((((-1)*W^2)/(X*Y^2)))*p334)

#print axioms zero_row_8

def rhsZero9 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 458 - ((1))*rhsPivot66 X Y Z W a b r - ((1))*rhsPivot107 X Y Z W a b r - (((1)/(X)))*rhsPivot126 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot161 X Y Z W a b r - ((1))*rhsPivot186 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot233 X Y Z W a b r - (((1)/(Y^2*W^2)) + ((1)/(W^2)))*rhsPivot236 X Y Z W a b r - ((((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot327 X Y Z W a b r - (((1)/(X*W^2)))*rhsPivot329 X Y Z W a b r - (((1)/(X*Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero9 X Y Z W a b r=0 := by
  have h:=hv 458
  change ((1))*v 81 + (((1)/(Y^2)))*v 219 + ((((-1)*a)/(Y)))*v 243 + ((1))*v 251 + ((1))*v 421=r 458 at h
  have p66:=pivot_66 X Y Z W a b hX hY hZ hW v r hv
  have p107:=pivot_107 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p161:=pivot_161 X Y Z W a b hX hY hZ hW v r hv
  have p186:=pivot_186 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p327:=pivot_327 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero9
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p66 - ((1))*p107 - (((1)/(X)))*p126 - ((((-1)*a)/(Y)))*p161 - ((1))*p186 - (((1)/(X*Y^2*W^2)))*p233 - (((1)/(Y^2*W^2)) + ((1)/(W^2)))*p236 - ((((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)))*p256 - (((1)/(Y^2)))*p327 - (((1)/(X*W^2)))*p329 - (((1)/(X*Y^2)))*p334)

#print axioms zero_row_9

def rhsZero10 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 461 - ((1))*rhsPivot79 X Y Z W a b r - ((1))*rhsPivot87 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot110 X Y Z W a b r - ((1))*rhsPivot174 X Y Z W a b r - (((1)/(X*Y^2*W^2)))*rhsPivot232 X Y Z W a b r - ((((-1)*a)/(X*Y*W^2)))*rhsPivot235 X Y Z W a b r - (((1)/(X*W^2)) + ((1*Y^2)/(X*W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot265 X Y Z W a b r - ((((-1))/(X*Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero10 X Y Z W a b r=0 := by
  have h:=hv 461
  change ((1))*v 89 + ((1))*v 259 + ((((-1)*a)/(Y)))*v 267 + (((1)/(Y^2)))*v 291 + ((1))*v 429=r 461 at h
  have p79:=pivot_79 X Y Z W a b hX hY hZ hW v r hv
  have p87:=pivot_87 X Y Z W a b hX hY hZ hW v r hv
  have p110:=pivot_110 X Y Z W a b hX hY hZ hW v r hv
  have p174:=pivot_174 X Y Z W a b hX hY hZ hW v r hv
  have p232:=pivot_232 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p265:=pivot_265 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero10
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p79 - ((1))*p87 - ((((-1)*a)/(Y)))*p110 - ((1))*p174 - (((1)/(X*Y^2*W^2)))*p232 - ((((-1)*a)/(X*Y*W^2)))*p235 - (((1)/(X*W^2)) + ((1*Y^2)/(X*W^2)))*p256 - (((1)/(Y^2)))*p265 - ((((-1))/(X*Y^2)))*p334)

#print axioms zero_row_10

def rhsZero11 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 474 - ((1))*rhsPivot93 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot126 X Y Z W a b r - ((1))*rhsPivot150 X Y Z W a b r - ((1*X))*rhsPivot189 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot233 X Y Z W a b r - (((1*X)/(Y^2)))*rhsPivot236 X Y Z W a b r - (((-1)))*rhsPivot256 X Y Z W a b r - (((-1)*X))*rhsPivot257 X Y Z W a b r - ((1))*rhsPivot329 X Y Z W a b r - (((1*W^2)/(Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero11 X Y Z W a b r=0 := by
  have h:=hv 474
  change ((1))*v 130 + (((1)/(Y^2)))*v 150 + ((1))*v 300 + ((((-1)*a)/(Y)))*v 390 + ((1))*v 470=r 474 at h
  have p93:=pivot_93 X Y Z W a b hX hY hZ hW v r hv
  have p126:=pivot_126 X Y Z W a b hX hY hZ hW v r hv
  have p150:=pivot_150 X Y Z W a b hX hY hZ hW v r hv
  have p189:=pivot_189 X Y Z W a b hX hY hZ hW v r hv
  have p233:=pivot_233 X Y Z W a b hX hY hZ hW v r hv
  have p236:=pivot_236 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p257:=pivot_257 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero11
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p93 - (((1*W^2)/(Y^2)))*p126 - ((1))*p150 - ((1*X))*p189 - (((1)/(Y^2)))*p233 - (((1*X)/(Y^2)))*p236 - (((-1)))*p256 - (((-1)*X))*p257 - ((1))*p329 - (((1*W^2)/(Y^2)))*p334)

#print axioms zero_row_11

def rhsZero12 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 490 - ((1))*rhsPivot86 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot115 X Y Z W a b r - (((1*X)/(W^2)))*rhsPivot141 X Y Z W a b r - (((1)/(Y^2*W^2)))*rhsPivot235 X Y Z W a b r - ((((-1)*Y*a)/(W^2)))*rhsPivot256 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot277 X Y Z W a b r - ((1))*rhsPivot307 X Y Z W a b r - (((-1)*X^2))*rhsPivot310 X Y Z W a b r - ((((-1))/(W^2)))*rhsPivot329 X Y Z W a b r - ((((-1))/(Y^2)))*rhsPivot334 X Y Z W a b r

compact_elimination_proof
theorem zero_row_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero12 X Y Z W a b r=0 := by
  have h:=hv 490
  change ((1))*v 162 + ((1))*v 332 + (((1)/(Y^2)))*v 438 + ((((-1)*a)/(Y)))*v 486 + ((1))*v 502=r 490 at h
  have p86:=pivot_86 X Y Z W a b hX hY hZ hW v r hv
  have p115:=pivot_115 X Y Z W a b hX hY hZ hW v r hv
  have p141:=pivot_141 X Y Z W a b hX hY hZ hW v r hv
  have p235:=pivot_235 X Y Z W a b hX hY hZ hW v r hv
  have p256:=pivot_256 X Y Z W a b hX hY hZ hW v r hv
  have p277:=pivot_277 X Y Z W a b hX hY hZ hW v r hv
  have p307:=pivot_307 X Y Z W a b hX hY hZ hW v r hv
  have p310:=pivot_310 X Y Z W a b hX hY hZ hW v r hv
  have p329:=pivot_329 X Y Z W a b hX hY hZ hW v r hv
  have p334:=pivot_334 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero12
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p86 - ((((-1)*a)/(Y)))*p115 - (((1*X)/(W^2)))*p141 - (((1)/(Y^2*W^2)))*p235 - ((((-1)*Y*a)/(W^2)))*p256 - (((1)/(Y^2)))*p277 - ((1))*p307 - (((-1)*X^2))*p310 - ((((-1))/(W^2)))*p329 - ((((-1))/(Y^2)))*p334)

#print axioms zero_row_12

def rhsZero13 (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : ℂ :=
  r 485 - ((1))*rhsPivot25 X Y Z W a b r - ((1))*rhsPivot220 X Y Z W a b r - ((((-1)*a)/(Y)))*rhsPivot268 X Y Z W a b r - (((-1)*X))*rhsPivot354 X Y Z W a b r - (((1)/(Y^2)))*rhsPivot355 X Y Z W a b r - ((((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*rhsPivot357 X Y Z W a b r - ((1))*rhsPivot382 X Y Z W a b r

compact_elimination_proof
theorem zero_row_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (r : Fin 546→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=r i) : rhsZero13 X Y Z W a b r=0 := by
  have h:=hv 485
  change ((1))*v 154 + ((1))*v 324 + (((1)/(Y^2)))*v 366 + ((((-1)*a)/(Y)))*v 462 + ((1))*v 494=r 485 at h
  have p25:=pivot_25 X Y Z W a b hX hY hZ hW v r hv
  have p220:=pivot_220 X Y Z W a b hX hY hZ hW v r hv
  have p268:=pivot_268 X Y Z W a b hX hY hZ hW v r hv
  have p354:=pivot_354 X Y Z W a b hX hY hZ hW v r hv
  have p355:=pivot_355 X Y Z W a b hX hY hZ hW v r hv
  have p357:=pivot_357 X Y Z W a b hX hY hZ hW v r hv
  have p382:=pivot_382 X Y Z W a b hX hY hZ hW v r hv
  unfold rhsZero13
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ,hW]; all_goals ring)) -(h - ((1))*p25 - ((1))*p220 - ((((-1)*a)/(Y)))*p268 - (((-1)*X))*p354 - (((1)/(Y^2)))*p355 - ((((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*p357 - ((1))*p382)

#print axioms zero_row_13

end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## SmallLevelThirtyFourUnitMMPInhomogeneousV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex SmallLevelThirtyFourUnitMMP

end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end
