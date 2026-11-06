module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveChiFour. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveChiFourCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour

/-- Selected original 420-grid Laurent rows, signs [-1, -1, -1].
The comments record the exact row-builder labels; analytic realization
is a separate obligation. This definition asserts no modularity. -/
def selectedRows0 (X Y Z W : ℂ) (v : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*v 0,
    -- ['g', 0, 1, -35, 0, -1, 24]
    ((1))*v 24 + ((X^2)/(Z*W))*v 210,
    -- ['g', 0, 1, -35, 0, -1, 36]
    ((1))*v 36 + ((Y^2)/(Z*W))*v 280,
    -- ['g', 0, 1, -35, 0, -1, 40]
    ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294,
    -- ['g', 0, 1, -35, 0, -1, 42]
    ((1))*v 42 + ((W)/(X^2*Z))*v 300,
    -- ['g', 0, 1, -35, 0, -1, 48]
    ((1))*v 48 + ((X^4)/(Z*W))*v 315,
    -- ['g', 0, 1, -35, 0, -1, 60]
    ((1))*v 60 + ((Z)/(W))*v 336,
    -- ['g', 0, 1, -35, 0, -1, 80]
    ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357,
    -- ['g', 0, 1, -35, 0, -1, 120]
    ((1))*v 120 + ((X^2*Z)/(W))*v 378,
    -- ['g', 0, 1, -35, 0, -1, 168]
    ((1))*v 168 + ((X^2*W)/(Z))*v 390,
    -- ['g', 0, 1, -35, 0, -1, 180]
    ((1))*v 180 + ((Y^2*Z)/(W))*v 392,
    -- ['g', 0, 1, -35, 0, -1, 240]
    ((1))*v 240 + ((X^4*Z)/(W))*v 399,
    -- ['g', 0, 1, -35, 0, -1, 252]
    ((1))*v 252 + ((Y^2*W)/(Z))*v 400,
    -- ['g', 0, 1, -35, 35, -1, 414]
    (((1))/(X^2*Z*W))*v 0 + ((1))*v 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*v 204 + ((-1)*X^2)*v 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*v 0 + ((1))*v 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*v 168 + ((-1)*X^4)*v 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*v 180 + ((-1)*Y^2)*v 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*v 40 + ((1))*v 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*v 42 + ((1))*v 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*v 60 + ((1))*v 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*v 84 + ((1))*v 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*v 0 + ((1))*v 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*v 24 + ((1))*v 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*v 120 + ((-1)*X^2)*v 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*v 84 + ((1))*v 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*v 240 + ((-1)*Y^2)*v 400,
    -- ['g', 35, -18, 70, -35, -1, 189]
    ((1))*v 189 + ((W)/(X^2*Z))*v 270,
    -- ['R', 4]
    ((1))*v 105 + ((1))*v 315,
    -- ['F', 4, 15]
    ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330,
    -- ['R', 5]
    ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336,
    -- ['F', 5, 21]
    ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357,
    -- ['R', 10]
    ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378]

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem target_case0 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows0 X Y Z W v=0) :
    v 105-v 315=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h23 : ((1))*v 24 + ((X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h27 : ((1))*v 36 + ((Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h28 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h29 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h31 : ((1))*v 48 + ((X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h33 : ((1))*v 60 + ((Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h37 : ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h42 : ((1))*v 120 + ((X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h46 : ((1))*v 168 + ((X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h47 : ((1))*v 180 + ((Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h49 : ((1))*v 240 + ((X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h50 : ((1))*v 252 + ((Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h99 : (((1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h912 : ((1))*v 189 + ((W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1771 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1810 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3415 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3420 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3415
  have h3553 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3420
  have h3576 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-((W)/(X^4))*h3553
  have h3673 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3676 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-((X^2)/(Z*W))*h3673
  have h3955 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3676
  have h3963 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3955
  have h4566 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4568 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-((Y^2)/(Z*W))*h4566
  have h4714 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4568
  have h4766 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3576-((W)/(X^4))*h4714
  have h5031 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3963
  have h5049 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4766-((W)/(X^4))*h5031
  have h8032 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h8035 : ((1))*v 240 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h8032
  have h8095 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h8099 : ((1))*v 252 + ((W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h8095
  have h8129 : ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h8095
  have h8232 : ((Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z*W)/(X^4))*h31
  have h8253 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8232
  have h8357 : ((W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h33
  have h8367 : (((-1)*W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8357
  have h8398 : (((-1)*W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8357
  have h8576 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Y^2*W)/(X^4*Z))*h37
  have h8586 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5049-((1))*h8576
  have h8959 : ((W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h42
  have h8990 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8129-((1))*h8959
  have h9115 : ((Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(X^2*W))*h46
  have h9120 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h9115
  have h9213 : ((W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Y^2*Z))*h47
  have h9218 : ((1))*v 126 + ((W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9213
  have h9280 : ((W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^4*Z))*h49
  have h9284 : ((1))*v 168 + ((W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9280
  have h9326 : ((Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(Y^2*W))*h50
  have h9330 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9326
  have h9333 : ((1))*v 240 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9326
  have h9710 : ((Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h9284
  have h9714 : (((-1)*Z)/(W))*v 168 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8035-((1))*h9710
  have h9719 : (((-1)*Z)/(W))*v 168 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9333-((1))*h9710
  have h9930 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9330
  have h9935 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9218-((W)/(X^2*Z))*h9930
  have h10811 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h9714
  have h10825 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-((Z)/(W))*h10811
  have h10843 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8990-((1))*h10811
  have h10959 : ((Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8099
  have h11030 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10843-(((-1)*W)/(X^2*Z))*h10959
  have h11450 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11453 : ((W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-((W)/(X^2*Z))*h11450
  have h11536 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11547 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8586-((1))*h11536
  have h12057 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9120
  have h12085 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10825-((1))*h12057
  have h12092 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11547-((W)/(X^4))*h12057
  have h12129 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11030-(((-1)*W)/(X^2*Z))*h12057
  have h12297 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9935
  have h12334 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12129-((1))*h12297
  have h13088 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h13099 : (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12092-(((-1)*Y^2*W)/(X^4*Z))*h13088
  have h13196 : ((1))*v 60 + ((Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8367
  have h13213 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11453-((W)/(X^4*Z))*h13196
  have h13234 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8398-(((-1)*W)/(Z))*h13196
  have h14149 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h9719
  have h14175 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12085-(((-1)*X^2*Z + Z)/(X^2*W))*h14149
  have h14178 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13234-((1))*h14149
  have h14196 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*Z)/(X^4))*v 252 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13099-(((-1)*Z)/(X^4))*h14149
  have h14270 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12334-(((2))/(X^2))*h14149
  have h14612 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14270
  have h14617 : ((Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14175-(((-1)*X^2*Z + Z)/(X^2*W))*h14612
  have h14623 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14178-((2))*h14612
  have h14646 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14196-(((-1)*Z)/(X^4))*h14612
  have h15188 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14623
  have h15189 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13213-(((-1))/(X^4))*h15188
  have h15201 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14617-((Z)/(W))*h15188
  have h15225 : ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14646-(((1))/(X^4))*h15188
  have h15663 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15189
  have h15668 : ((1))*v 105 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15225-((1))*h15663
  have h15744 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15201
  have h15749 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15668-(((-1)*W)/(X^2*Z))*h15744
  have h16066 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15749
  have h16075 : (((-1)*Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8253-((1))*h16066
  have h16357 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^4)/(Z*W))*h16075
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((-1))*h8232 + ((1))*h16066 + ((Z*W)/(X^4))*h16357

#print axioms target_case0

/-- Selected original 420-grid Laurent rows, signs [-1, 1, -1].
The comments record the exact row-builder labels; analytic realization
is a separate obligation. This definition asserts no modularity. -/
def selectedRows2 (X Y Z W : ℂ) (v : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*v 0,
    -- ['g', 0, 1, -35, 0, -1, 24]
    ((1))*v 24 + ((X^2)/(Z*W))*v 210,
    -- ['g', 0, 1, -35, 0, -1, 36]
    ((1))*v 36 + ((Y^2)/(Z*W))*v 280,
    -- ['g', 0, 1, -35, 0, -1, 40]
    ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294,
    -- ['g', 0, 1, -35, 0, -1, 42]
    ((1))*v 42 + ((W)/(X^2*Z))*v 300,
    -- ['g', 0, 1, -35, 0, -1, 48]
    ((1))*v 48 + ((X^4)/(Z*W))*v 315,
    -- ['g', 0, 1, -35, 0, -1, 60]
    ((1))*v 60 + ((Z)/(W))*v 336,
    -- ['g', 0, 1, -35, 0, -1, 80]
    ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357,
    -- ['g', 0, 1, -35, 0, -1, 120]
    ((1))*v 120 + ((X^2*Z)/(W))*v 378,
    -- ['g', 0, 1, -35, 0, -1, 168]
    ((1))*v 168 + ((X^2*W)/(Z))*v 390,
    -- ['g', 0, 1, -35, 0, -1, 180]
    ((1))*v 180 + ((Y^2*Z)/(W))*v 392,
    -- ['g', 0, 1, -35, 0, -1, 240]
    ((1))*v 240 + ((X^4*Z)/(W))*v 399,
    -- ['g', 0, 1, -35, 0, -1, 252]
    ((1))*v 252 + ((Y^2*W)/(Z))*v 400,
    -- ['g', 0, 1, -35, 35, -1, 414]
    (((1))/(X^2*Z*W))*v 0 + ((1))*v 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*v 204 + ((-1)*X^2)*v 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*v 0 + ((1))*v 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*v 168 + ((-1)*X^4)*v 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*v 180 + ((-1)*Y^2)*v 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*v 40 + ((1))*v 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*v 42 + ((1))*v 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*v 60 + ((1))*v 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*v 84 + ((1))*v 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*v 0 + ((1))*v 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*v 24 + ((1))*v 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*v 120 + ((-1)*X^2)*v 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*v 84 + ((1))*v 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*v 240 + ((-1)*Y^2)*v 400,
    -- ['g', 35, -18, 70, -35, -1, 189]
    ((1))*v 189 + ((W)/(X^2*Z))*v 270,
    -- ['R', 4]
    ((1))*v 105 + ((1))*v 315,
    -- ['F', 4, 15]
    ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330,
    -- ['R', 5]
    ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336,
    -- ['F', 5, 21]
    (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357,
    -- ['R', 10]
    ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378]

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem target_case2 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows2 X Y Z W v=0) :
    v 105-v 315=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h23 : ((1))*v 24 + ((X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h27 : ((1))*v 36 + ((Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h28 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h29 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h31 : ((1))*v 48 + ((X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h33 : ((1))*v 60 + ((Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h37 : ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h42 : ((1))*v 120 + ((X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h46 : ((1))*v 168 + ((X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h47 : ((1))*v 180 + ((Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h49 : ((1))*v 240 + ((X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h50 : ((1))*v 252 + ((Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h99 : (((1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h912 : ((1))*v 189 + ((W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1771 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1810 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3389 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3394 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3389
  have h3525 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3394
  have h3548 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-(((-1)*W)/(X^4))*h3525
  have h3639 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3642 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-((X^2)/(Z*W))*h3639
  have h3917 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3642
  have h3925 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3917
  have h4510 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4512 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-((Y^2)/(Z*W))*h4510
  have h4658 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4512
  have h4710 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3548-(((-1)*W)/(X^4))*h4658
  have h4961 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3925
  have h4979 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4710-(((-1)*W)/(X^4))*h4961
  have h7920 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h7923 : ((1))*v 240 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h7920
  have h7983 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h7987 : ((1))*v 252 + ((W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h7983
  have h8017 : ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h7983
  have h8118 : ((Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z*W)/(X^4))*h31
  have h8139 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8118
  have h8243 : ((W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h33
  have h8253 : (((-1)*W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8243
  have h8284 : (((-1)*W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8243
  have h8456 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Y^2*W)/(X^4*Z))*h37
  have h8466 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4979-((1))*h8456
  have h8829 : ((W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h42
  have h8860 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8017-((1))*h8829
  have h8983 : ((Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(X^2*W))*h46
  have h8988 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h8983
  have h9077 : ((W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Y^2*Z))*h47
  have h9082 : ((1))*v 126 + ((W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9077
  have h9144 : ((W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^4*Z))*h49
  have h9148 : ((1))*v 168 + ((W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9144
  have h9190 : ((Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(Y^2*W))*h50
  have h9194 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9190
  have h9197 : ((1))*v 240 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9190
  have h9574 : ((Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h9148
  have h9578 : (((-1)*Z)/(W))*v 168 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7923-((1))*h9574
  have h9583 : (((-1)*Z)/(W))*v 168 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9197-((1))*h9574
  have h9788 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9194
  have h9793 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9082-((W)/(X^2*Z))*h9788
  have h10659 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h9578
  have h10673 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-((Z)/(W))*h10659
  have h10691 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8860-((1))*h10659
  have h10803 : ((Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h7987
  have h10874 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10691-(((-1)*W)/(X^2*Z))*h10803
  have h11278 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11281 : ((W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-((W)/(X^2*Z))*h11278
  have h11362 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11373 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8466-((1))*h11362
  have h11873 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h8988
  have h11901 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10673-((1))*h11873
  have h11908 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11373-(((-1)*W)/(X^4))*h11873
  have h11945 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10874-(((-1)*W)/(X^2*Z))*h11873
  have h12103 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9793
  have h12140 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11945-((1))*h12103
  have h12880 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h12891 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11908-(((-1)*Y^2*W)/(X^4*Z))*h12880
  have h12988 : ((1))*v 60 + ((Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8253
  have h13005 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11281-((W)/(X^4*Z))*h12988
  have h13026 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8284-(((-1)*W)/(Z))*h12988
  have h13925 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h9583
  have h13951 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11901-(((-1)*X^2*Z + Z)/(X^2*W))*h13925
  have h13954 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13026-((1))*h13925
  have h13972 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((Z)/(X^4))*v 252 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12891-((Z)/(X^4))*h13925
  have h14046 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12140-(((2))/(X^2))*h13925
  have h14374 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14046
  have h14379 : ((Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13951-(((-1)*X^2*Z + Z)/(X^2*W))*h14374
  have h14385 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13954-((2))*h14374
  have h14408 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13972-((Z)/(X^4))*h14374
  have h14932 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14385
  have h14933 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13005-(((-1))/(X^4))*h14932
  have h14945 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14379-((Z)/(W))*h14932
  have h14969 : ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14408-(((1))/(X^4))*h14932
  have h15389 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14933
  have h15394 : ((1))*v 105 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14969-((1))*h15389
  have h15470 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14945
  have h15475 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15394-(((-1)*W)/(X^2*Z))*h15470
  have h15788 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15475
  have h15797 : (((-1)*Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8139-((1))*h15788
  have h16051 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^4)/(Z*W))*h15797
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((-1))*h8118 + ((1))*h15788 + ((Z*W)/(X^4))*h16051

#print axioms target_case2

/-- Selected original 420-grid Laurent rows, signs [1, -1, -1].
The comments record the exact row-builder labels; analytic realization
is a separate obligation. This definition asserts no modularity. -/
def selectedRows4 (X Y Z W : ℂ) (v : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*v 0,
    -- ['g', 0, 1, -35, 0, 1, 24]
    ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210,
    -- ['g', 0, 1, -35, 0, 1, 36]
    ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280,
    -- ['g', 0, 1, -35, 0, 1, 40]
    ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294,
    -- ['g', 0, 1, -35, 0, 1, 42]
    ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300,
    -- ['g', 0, 1, -35, 0, 1, 48]
    ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315,
    -- ['g', 0, 1, -35, 0, 1, 60]
    ((1))*v 60 + (((-1)*Z)/(W))*v 336,
    -- ['g', 0, 1, -35, 0, 1, 80]
    ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357,
    -- ['g', 0, 1, -35, 0, 1, 120]
    ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378,
    -- ['g', 0, 1, -35, 0, 1, 168]
    ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390,
    -- ['g', 0, 1, -35, 0, 1, 180]
    ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392,
    -- ['g', 0, 1, -35, 0, 1, 240]
    ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399,
    -- ['g', 0, 1, -35, 0, 1, 252]
    ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400,
    -- ['g', 0, 1, -35, 35, 1, 414]
    (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*v 204 + ((-1)*X^2)*v 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*v 0 + ((1))*v 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*v 168 + ((-1)*X^4)*v 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*v 180 + ((-1)*Y^2)*v 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*v 40 + ((1))*v 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*v 42 + ((1))*v 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*v 60 + ((1))*v 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*v 84 + ((1))*v 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*v 0 + ((1))*v 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*v 24 + ((1))*v 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*v 120 + ((-1)*X^2)*v 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*v 84 + ((1))*v 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*v 240 + ((-1)*Y^2)*v 400,
    -- ['g', 35, -18, 70, -35, 1, 189]
    ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270,
    -- ['R', 4]
    ((1))*v 105 + ((1))*v 315,
    -- ['F', 4, 15]
    (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330,
    -- ['R', 5]
    ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336,
    -- ['F', 5, 21]
    (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357,
    -- ['R', 10]
    ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378]

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem target_case4 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows4 X Y Z W v=0) :
    v 105-v 315=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h23 : ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h27 : ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h28 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h29 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h31 : ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h33 : ((1))*v 60 + (((-1)*Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h37 : ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h42 : ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h46 : ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h47 : ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h49 : ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h50 : ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h99 : (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h912 : ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1771 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1810 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((-1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3389 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3394 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3389
  have h3525 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3394
  have h3548 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-(((-1)*W)/(X^4))*h3525
  have h3639 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3642 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-(((-1)*X^2)/(Z*W))*h3639
  have h3917 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3642
  have h3925 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3917
  have h4510 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4512 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-(((-1)*Y^2)/(Z*W))*h4510
  have h4658 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4512
  have h4710 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3548-(((-1)*W)/(X^4))*h4658
  have h4961 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3925
  have h4979 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4710-(((-1)*W)/(X^4))*h4961
  have h7920 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h7923 : ((1))*v 240 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h7920
  have h7983 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h7987 : ((1))*v 252 + (((-1)*W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h7983
  have h8017 : ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h7983
  have h8118 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z*W)/(X^4))*h31
  have h8139 : ((Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8118
  have h8243 : (((-1)*W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h33
  have h8253 : ((W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8243
  have h8284 : ((W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8243
  have h8456 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Y^2*W)/(X^4*Z))*h37
  have h8466 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4979-((1))*h8456
  have h8829 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h42
  have h8860 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8017-((1))*h8829
  have h8983 : (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(X^2*W))*h46
  have h8988 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h8983
  have h9077 : (((-1)*W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Y^2*Z))*h47
  have h9082 : ((1))*v 126 + (((-1)*W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9077
  have h9144 : (((-1)*W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^4*Z))*h49
  have h9148 : ((1))*v 168 + (((-1)*W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9144
  have h9190 : (((-1)*Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(Y^2*W))*h50
  have h9194 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9190
  have h9197 : ((1))*v 240 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9190
  have h9574 : (((-1)*Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h9148
  have h9578 : ((Z)/(W))*v 168 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7923-((1))*h9574
  have h9583 : ((Z)/(W))*v 168 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9197-((1))*h9574
  have h9788 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9194
  have h9793 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9082-(((-1)*W)/(X^2*Z))*h9788
  have h10659 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h9578
  have h10673 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-(((-1)*Z)/(W))*h10659
  have h10691 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8860-((1))*h10659
  have h10803 : (((-1)*Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h7987
  have h10874 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10691-((W)/(X^2*Z))*h10803
  have h11278 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11281 : (((-1)*W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-(((-1)*W)/(X^2*Z))*h11278
  have h11362 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11373 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8466-((1))*h11362
  have h11873 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h8988
  have h11901 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10673-((1))*h11873
  have h11908 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11373-(((-1)*W)/(X^4))*h11873
  have h11945 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10874-((W)/(X^2*Z))*h11873
  have h12103 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9793
  have h12140 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11945-((1))*h12103
  have h12880 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h12891 : (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11908-((Y^2*W)/(X^4*Z))*h12880
  have h12988 : ((1))*v 60 + (((-1)*Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8253
  have h13005 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11281-(((-1)*W)/(X^4*Z))*h12988
  have h13026 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8284-((W)/(Z))*h12988
  have h13925 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h9583
  have h13951 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11901-((X^2*Z + (-1)*Z)/(X^2*W))*h13925
  have h13954 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13026-((1))*h13925
  have h13972 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*Z)/(X^4))*v 252 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12891-(((-1)*Z)/(X^4))*h13925
  have h14046 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12140-(((2))/(X^2))*h13925
  have h14374 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14046
  have h14379 : (((-1)*Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13951-((X^2*Z + (-1)*Z)/(X^2*W))*h14374
  have h14385 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13954-((2))*h14374
  have h14408 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13972-(((-1)*Z)/(X^4))*h14374
  have h14932 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14385
  have h14933 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13005-(((-1))/(X^4))*h14932
  have h14945 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14379-(((-1)*Z)/(W))*h14932
  have h14969 : ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14408-(((1))/(X^4))*h14932
  have h15389 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14933
  have h15394 : ((1))*v 105 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14969-((1))*h15389
  have h15470 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14945
  have h15475 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15394-((W)/(X^2*Z))*h15470
  have h15788 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15475
  have h15797 : ((Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8139-((1))*h15788
  have h16051 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^4)/(Z*W))*h15797
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((-1))*h8118 + ((1))*h15788 + (((-1)*Z*W)/(X^4))*h16051

#print axioms target_case4

/-- Selected original 420-grid Laurent rows, signs [1, 1, -1].
The comments record the exact row-builder labels; analytic realization
is a separate obligation. This definition asserts no modularity. -/
def selectedRows6 (X Y Z W : ℂ) (v : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*v 0,
    -- ['g', 0, 1, -35, 0, 1, 24]
    ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210,
    -- ['g', 0, 1, -35, 0, 1, 36]
    ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280,
    -- ['g', 0, 1, -35, 0, 1, 40]
    ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294,
    -- ['g', 0, 1, -35, 0, 1, 42]
    ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300,
    -- ['g', 0, 1, -35, 0, 1, 48]
    ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315,
    -- ['g', 0, 1, -35, 0, 1, 60]
    ((1))*v 60 + (((-1)*Z)/(W))*v 336,
    -- ['g', 0, 1, -35, 0, 1, 80]
    ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357,
    -- ['g', 0, 1, -35, 0, 1, 120]
    ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378,
    -- ['g', 0, 1, -35, 0, 1, 168]
    ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390,
    -- ['g', 0, 1, -35, 0, 1, 180]
    ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392,
    -- ['g', 0, 1, -35, 0, 1, 240]
    ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399,
    -- ['g', 0, 1, -35, 0, 1, 252]
    ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400,
    -- ['g', 0, 1, -35, 35, 1, 414]
    (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*v 204 + ((-1)*X^2)*v 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*v 0 + ((1))*v 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*v 168 + ((-1)*X^4)*v 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*v 180 + ((-1)*Y^2)*v 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*v 40 + ((1))*v 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*v 42 + ((1))*v 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*v 60 + ((1))*v 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*v 84 + ((1))*v 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*v 0 + ((1))*v 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*v 24 + ((1))*v 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*v 120 + ((-1)*X^2)*v 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*v 84 + ((1))*v 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*v 240 + ((-1)*Y^2)*v 400,
    -- ['g', 35, -18, 70, -35, 1, 189]
    ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270,
    -- ['R', 4]
    ((1))*v 105 + ((1))*v 315,
    -- ['F', 4, 15]
    (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330,
    -- ['R', 5]
    ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336,
    -- ['F', 5, 21]
    ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357,
    -- ['R', 10]
    ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378]

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem target_case6 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows6 X Y Z W v=0) :
    v 105-v 315=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h23 : ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h27 : ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h28 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h29 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h31 : ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h33 : ((1))*v 60 + (((-1)*Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h37 : ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h42 : ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h46 : ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h47 : ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h49 : ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h50 : ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h99 : (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h912 : ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1771 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1810 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((-1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3415 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3420 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3415
  have h3553 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3420
  have h3576 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-((W)/(X^4))*h3553
  have h3673 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3676 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-(((-1)*X^2)/(Z*W))*h3673
  have h3955 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3676
  have h3963 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3955
  have h4566 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4568 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-(((-1)*Y^2)/(Z*W))*h4566
  have h4714 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4568
  have h4766 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3576-((W)/(X^4))*h4714
  have h5031 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3963
  have h5049 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4766-((W)/(X^4))*h5031
  have h8032 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h8035 : ((1))*v 240 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h8032
  have h8095 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h8099 : ((1))*v 252 + (((-1)*W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h8095
  have h8129 : ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h8095
  have h8232 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z*W)/(X^4))*h31
  have h8253 : ((Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8232
  have h8357 : (((-1)*W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h33
  have h8367 : ((W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8357
  have h8398 : ((W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8357
  have h8576 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Y^2*W)/(X^4*Z))*h37
  have h8586 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5049-((1))*h8576
  have h8959 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h42
  have h8990 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8129-((1))*h8959
  have h9115 : (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(X^2*W))*h46
  have h9120 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h9115
  have h9213 : (((-1)*W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Y^2*Z))*h47
  have h9218 : ((1))*v 126 + (((-1)*W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9213
  have h9280 : (((-1)*W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^4*Z))*h49
  have h9284 : ((1))*v 168 + (((-1)*W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9280
  have h9326 : (((-1)*Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(Y^2*W))*h50
  have h9330 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9326
  have h9333 : ((1))*v 240 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9326
  have h9710 : (((-1)*Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h9284
  have h9714 : ((Z)/(W))*v 168 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8035-((1))*h9710
  have h9719 : ((Z)/(W))*v 168 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9333-((1))*h9710
  have h9930 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9330
  have h9935 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9218-(((-1)*W)/(X^2*Z))*h9930
  have h10811 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h9714
  have h10825 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-(((-1)*Z)/(W))*h10811
  have h10843 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8990-((1))*h10811
  have h10959 : (((-1)*Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8099
  have h11030 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10843-((W)/(X^2*Z))*h10959
  have h11450 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11453 : (((-1)*W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-(((-1)*W)/(X^2*Z))*h11450
  have h11536 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11547 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8586-((1))*h11536
  have h12057 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9120
  have h12085 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10825-((1))*h12057
  have h12092 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11547-((W)/(X^4))*h12057
  have h12129 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11030-((W)/(X^2*Z))*h12057
  have h12297 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9935
  have h12334 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12129-((1))*h12297
  have h13088 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h13099 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12092-((Y^2*W)/(X^4*Z))*h13088
  have h13196 : ((1))*v 60 + (((-1)*Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8367
  have h13213 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11453-(((-1)*W)/(X^4*Z))*h13196
  have h13234 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8398-((W)/(Z))*h13196
  have h14149 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h9719
  have h14175 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12085-((X^2*Z + (-1)*Z)/(X^2*W))*h14149
  have h14178 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13234-((1))*h14149
  have h14196 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((Z)/(X^4))*v 252 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13099-((Z)/(X^4))*h14149
  have h14270 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12334-(((2))/(X^2))*h14149
  have h14612 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14270
  have h14617 : (((-1)*Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14175-((X^2*Z + (-1)*Z)/(X^2*W))*h14612
  have h14623 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14178-((2))*h14612
  have h14646 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14196-((Z)/(X^4))*h14612
  have h15188 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14623
  have h15189 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13213-(((-1))/(X^4))*h15188
  have h15201 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14617-(((-1)*Z)/(W))*h15188
  have h15225 : ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14646-(((1))/(X^4))*h15188
  have h15663 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15189
  have h15668 : ((1))*v 105 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15225-((1))*h15663
  have h15744 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15201
  have h15749 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15668-((W)/(X^2*Z))*h15744
  have h16066 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15749
  have h16075 : ((Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8253-((1))*h16066
  have h16357 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^4)/(Z*W))*h16075
  linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((-1))*h8232 + ((1))*h16066 + (((-1)*Z*W)/(X^4))*h16357

#print axioms target_case6

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveChiFourCoordinatesV1 -/
section
@[expose] public section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
def coordinate : Fin 35 → Fin 420 :=
  ![0,24,36,40,42,48,60,80,84,105,120,126,168,180,189,204,210,240,252,270,273,280,288,294,300,315,330,336,357,378,390,392,399,400,414]

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveChiFourKernelBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem selected_kernel_case0 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows0 X Y Z W v=0) :
    ∀ i : Fin 35, v (coordinate i)=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h23 : ((1))*v 24 + ((X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h27 : ((1))*v 36 + ((Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h28 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h29 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h31 : ((1))*v 48 + ((X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h33 : ((1))*v 60 + ((Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h37 : ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h42 : ((1))*v 120 + ((X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h46 : ((1))*v 168 + ((X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h47 : ((1))*v 180 + ((Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h49 : ((1))*v 240 + ((X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h50 : ((1))*v 252 + ((Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h99 : (((1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h912 : ((1))*v 189 + ((W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1771 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1810 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows0] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3415 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3420 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3415
  have h3553 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3420
  have h3576 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-((W)/(X^4))*h3553
  have h3673 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3676 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-((X^2)/(Z*W))*h3673
  have h3955 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3676
  have h3963 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3955
  have h4566 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4568 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-((Y^2)/(Z*W))*h4566
  have h4714 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4568
  have h4766 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3576-((W)/(X^4))*h4714
  have h5031 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3963
  have h5049 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4766-((W)/(X^4))*h5031
  have h8032 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h8035 : ((1))*v 240 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h8032
  have h8095 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h8099 : ((1))*v 252 + ((W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h8095
  have h8129 : ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h8095
  have h8232 : ((Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z*W)/(X^4))*h31
  have h8253 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8232
  have h8357 : ((W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h33
  have h8367 : (((-1)*W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8357
  have h8398 : (((-1)*W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8357
  have h8576 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Y^2*W)/(X^4*Z))*h37
  have h8586 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5049-((1))*h8576
  have h8959 : ((W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h42
  have h8990 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8129-((1))*h8959
  have h9115 : ((Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(X^2*W))*h46
  have h9120 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h9115
  have h9213 : ((W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Y^2*Z))*h47
  have h9218 : ((1))*v 126 + ((W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9213
  have h9280 : ((W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^4*Z))*h49
  have h9284 : ((1))*v 168 + ((W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9280
  have h9326 : ((Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(Y^2*W))*h50
  have h9330 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9326
  have h9333 : ((1))*v 240 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9326
  have h9710 : ((Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h9284
  have h9714 : (((-1)*Z)/(W))*v 168 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8035-((1))*h9710
  have h9719 : (((-1)*Z)/(W))*v 168 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9333-((1))*h9710
  have h9930 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9330
  have h9935 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9218-((W)/(X^2*Z))*h9930
  have h10811 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h9714
  have h10825 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-((Z)/(W))*h10811
  have h10843 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8990-((1))*h10811
  have h10959 : ((Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8099
  have h11030 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10843-(((-1)*W)/(X^2*Z))*h10959
  have h11450 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11453 : ((W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-((W)/(X^2*Z))*h11450
  have h11536 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11547 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8586-((1))*h11536
  have h12057 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9120
  have h12085 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10825-((1))*h12057
  have h12092 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11547-((W)/(X^4))*h12057
  have h12129 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11030-(((-1)*W)/(X^2*Z))*h12057
  have h12297 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9935
  have h12334 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12129-((1))*h12297
  have h13088 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h13099 : (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12092-(((-1)*Y^2*W)/(X^4*Z))*h13088
  have h13196 : ((1))*v 60 + ((Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8367
  have h13213 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11453-((W)/(X^4*Z))*h13196
  have h13234 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8398-(((-1)*W)/(Z))*h13196
  have h14149 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h9719
  have h14175 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12085-(((-1)*X^2*Z + Z)/(X^2*W))*h14149
  have h14178 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13234-((1))*h14149
  have h14196 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*Z)/(X^4))*v 252 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13099-(((-1)*Z)/(X^4))*h14149
  have h14270 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12334-(((2))/(X^2))*h14149
  have h14612 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14270
  have h14617 : ((Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14175-(((-1)*X^2*Z + Z)/(X^2*W))*h14612
  have h14623 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14178-((2))*h14612
  have h14646 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14196-(((-1)*Z)/(X^4))*h14612
  have h15188 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14623
  have h15189 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13213-(((-1))/(X^4))*h15188
  have h15201 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14617-((Z)/(W))*h15188
  have h15225 : ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14646-(((1))/(X^4))*h15188
  have h15663 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15189
  have h15668 : ((1))*v 105 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15225-((1))*h15663
  have h15744 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15201
  have h15749 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15668-(((-1)*W)/(X^2*Z))*h15744
  have h16066 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15749
  have h16075 : (((-1)*Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8253-((1))*h16066
  have h16357 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^4)/(Z*W))*h16075
  have hz48 : v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16357
  have hz105 : v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16066
  have hz330 : v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15744
  have hz189 : v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15663
  have hz84 : v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15188
  have hz252 : v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14612
  have hz168 : v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14149 - ((-1))*hz252
  have hz60 : v 60=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13196 - ((Z)/(W))*hz84
  have hz80 : v 80=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13088 - (((-1)*X^2)/(Y^2))*hz330
  have hz126 : v 126=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12297 - (((-1))/(X^2))*hz252
  have hz120 : v 120=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12057 - ((Z)/(W))*hz168
  have hz273 : v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11536 - (((-1))/(X^4))*hz84
  have hz270 : v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11450 - (((-1))/(X^2))*hz60
  have hz300 : v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10959 - ((Z)/(W))*hz252
  have hz294 : v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10811 - (((-1))/(X^2))*hz168
  have hz180 : v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9930 - ((Z)/(W))*hz252
  have hz240 : v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9710 - ((Z)/(W))*hz168
  have hz400 : v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9326 - ((Z)/(Y^2*W))*hz252
  have hz399 : v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9280 - ((W)/(X^4*Z))*hz240
  have hz392 : v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9213 - ((W)/(Y^2*Z))*hz180
  have hz390 : v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9115 - ((Z)/(X^2*W))*hz168
  have hz378 : v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8959 - ((W)/(X^2*Z))*hz120
  have hz357 : v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8576 - ((Y^2*W)/(X^4*Z))*hz80
  have hz336 : v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8357 - ((W)/(Z))*hz60
  have hz315 : v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8232 - ((Z*W)/(X^4))*hz48
  have hz42 : v 42=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8095 - ((W)/(X^2*Z))*hz300
  have hz40 : v 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8032 - ((X^2*Z)/(Y^2*W))*hz294
  have hz288 : v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5031
  have hz36 : v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4714
  have hz280 : v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4566
  have hz24 : v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3955
  have hz210 : v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3673
  have hz204 : v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3553
  have hz414 : v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3415
  have hz0 : v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h2691
  intro i
  fin_cases i <;> dsimp [coordinate] <;> assumption

#print axioms selected_kernel_case0

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem selected_kernel_case2 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows2 X Y Z W v=0) :
    ∀ i : Fin 35, v (coordinate i)=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h23 : ((1))*v 24 + ((X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h27 : ((1))*v 36 + ((Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h28 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h29 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h31 : ((1))*v 48 + ((X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h33 : ((1))*v 60 + ((Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h37 : ((1))*v 80 + ((X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h42 : ((1))*v 120 + ((X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h46 : ((1))*v 168 + ((X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h47 : ((1))*v 180 + ((Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h49 : ((1))*v 240 + ((X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h50 : ((1))*v 252 + ((Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h99 : (((1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h912 : ((1))*v 189 + ((W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1771 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1810 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows2] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3389 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3394 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3389
  have h3525 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3394
  have h3548 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-(((-1)*W)/(X^4))*h3525
  have h3639 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3642 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-((X^2)/(Z*W))*h3639
  have h3917 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3642
  have h3925 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3917
  have h4510 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4512 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-((Y^2)/(Z*W))*h4510
  have h4658 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4512
  have h4710 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3548-(((-1)*W)/(X^4))*h4658
  have h4961 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3925
  have h4979 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4710-(((-1)*W)/(X^4))*h4961
  have h7920 : ((1))*v 40 + ((X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h7923 : ((1))*v 240 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h7920
  have h7983 : ((1))*v 42 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h7987 : ((1))*v 252 + ((W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h7983
  have h8017 : ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h7983
  have h8118 : ((Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z*W)/(X^4))*h31
  have h8139 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8118
  have h8243 : ((W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h33
  have h8253 : (((-1)*W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8243
  have h8284 : (((-1)*W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8243
  have h8456 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Y^2*W)/(X^4*Z))*h37
  have h8466 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4979-((1))*h8456
  have h8829 : ((W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h42
  have h8860 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8017-((1))*h8829
  have h8983 : ((Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(X^2*W))*h46
  have h8988 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h8983
  have h9077 : ((W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Y^2*Z))*h47
  have h9082 : ((1))*v 126 + ((W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9077
  have h9144 : ((W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^4*Z))*h49
  have h9148 : ((1))*v 168 + ((W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9144
  have h9190 : ((Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(Y^2*W))*h50
  have h9194 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9190
  have h9197 : ((1))*v 240 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9190
  have h9574 : ((Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h9148
  have h9578 : (((-1)*Z)/(W))*v 168 + ((X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7923-((1))*h9574
  have h9583 : (((-1)*Z)/(W))*v 168 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9197-((1))*h9574
  have h9788 : ((1))*v 180 + ((Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9194
  have h9793 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9082-((W)/(X^2*Z))*h9788
  have h10659 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(X^2*Z))*h9578
  have h10673 : ((Z)/(W))*v 84 + ((1))*v 120 + ((Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-((Z)/(W))*h10659
  have h10691 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8860-((1))*h10659
  have h10803 : ((Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h7987
  have h10874 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10691-(((-1)*W)/(X^2*Z))*h10803
  have h11278 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11281 : ((W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-((W)/(X^2*Z))*h11278
  have h11362 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11373 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8466-((1))*h11362
  have h11873 : ((1))*v 120 + ((Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h8988
  have h11901 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10673-((1))*h11873
  have h11908 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11373-(((-1)*W)/(X^4))*h11873
  have h11945 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10874-(((-1)*W)/(X^2*Z))*h11873
  have h12103 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9793
  have h12140 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11945-((1))*h12103
  have h12880 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h12891 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11908-(((-1)*Y^2*W)/(X^4*Z))*h12880
  have h12988 : ((1))*v 60 + ((Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8253
  have h13005 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11281-((W)/(X^4*Z))*h12988
  have h13026 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8284-(((-1)*W)/(Z))*h12988
  have h13925 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h9583
  have h13951 : ((Z)/(W))*v 84 + (((-1)*X^2*Z + Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11901-(((-1)*X^2*Z + Z)/(X^2*W))*h13925
  have h13954 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13026-((1))*h13925
  have h13972 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((Z)/(X^4))*v 252 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12891-((Z)/(X^4))*h13925
  have h14046 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12140-(((2))/(X^2))*h13925
  have h14374 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14046
  have h14379 : ((Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13951-(((-1)*X^2*Z + Z)/(X^2*W))*h14374
  have h14385 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13954-((2))*h14374
  have h14408 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13972-((Z)/(X^4))*h14374
  have h14932 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14385
  have h14933 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13005-(((-1))/(X^4))*h14932
  have h14945 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14379-((Z)/(W))*h14932
  have h14969 : ((1))*v 105 + ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14408-(((1))/(X^4))*h14932
  have h15389 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14933
  have h15394 : ((1))*v 105 + (((-1)*W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14969-((1))*h15389
  have h15470 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14945
  have h15475 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15394-(((-1)*W)/(X^2*Z))*h15470
  have h15788 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15475
  have h15797 : (((-1)*Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8139-((1))*h15788
  have h16051 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^4)/(Z*W))*h15797
  have hz48 : v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16051
  have hz105 : v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15788
  have hz330 : v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15470
  have hz189 : v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15389
  have hz84 : v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14932
  have hz252 : v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14374
  have hz168 : v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13925 - ((-1))*hz252
  have hz60 : v 60=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12988 - ((Z)/(W))*hz84
  have hz80 : v 80=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12880 - (((-1)*X^2)/(Y^2))*hz330
  have hz126 : v 126=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12103 - (((-1))/(X^2))*hz252
  have hz120 : v 120=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11873 - ((Z)/(W))*hz168
  have hz273 : v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11362 - (((-1))/(X^4))*hz84
  have hz270 : v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11278 - (((-1))/(X^2))*hz60
  have hz300 : v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10803 - ((Z)/(W))*hz252
  have hz294 : v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10659 - (((-1))/(X^2))*hz168
  have hz180 : v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9788 - ((Z)/(W))*hz252
  have hz240 : v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9574 - ((Z)/(W))*hz168
  have hz400 : v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9190 - ((Z)/(Y^2*W))*hz252
  have hz399 : v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9144 - ((W)/(X^4*Z))*hz240
  have hz392 : v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9077 - ((W)/(Y^2*Z))*hz180
  have hz390 : v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8983 - ((Z)/(X^2*W))*hz168
  have hz378 : v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8829 - ((W)/(X^2*Z))*hz120
  have hz357 : v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8456 - ((Y^2*W)/(X^4*Z))*hz80
  have hz336 : v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8243 - ((W)/(Z))*hz60
  have hz315 : v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8118 - ((Z*W)/(X^4))*hz48
  have hz42 : v 42=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7983 - ((W)/(X^2*Z))*hz300
  have hz40 : v 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7920 - ((X^2*Z)/(Y^2*W))*hz294
  have hz288 : v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4961
  have hz36 : v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4658
  have hz280 : v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4510
  have hz24 : v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3917
  have hz210 : v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3639
  have hz204 : v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3525
  have hz414 : v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3389
  have hz0 : v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h2691
  intro i
  fin_cases i <;> dsimp [coordinate] <;> assumption

#print axioms selected_kernel_case2

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem selected_kernel_case4 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows4 X Y Z W v=0) :
    ∀ i : Fin 35, v (coordinate i)=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h23 : ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h27 : ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h28 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h29 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h31 : ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h33 : ((1))*v 60 + (((-1)*Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h37 : ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h42 : ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h46 : ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h47 : ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h49 : ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h50 : ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h99 : (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h912 : ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1771 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1810 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + (((-1)*W)/(X^4))*v 204 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows4] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((-1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3389 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3394 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3389
  have h3525 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3394
  have h3548 : (((-1)*W)/(X^4))*v 36 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-(((-1)*W)/(X^4))*h3525
  have h3639 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3642 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-(((-1)*X^2)/(Z*W))*h3639
  have h3917 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3642
  have h3925 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3917
  have h4510 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4512 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-(((-1)*Y^2)/(Z*W))*h4510
  have h4658 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4512
  have h4710 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + (((-1)*W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3548-(((-1)*W)/(X^4))*h4658
  have h4961 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3925
  have h4979 : ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4710-(((-1)*W)/(X^4))*h4961
  have h7920 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h7923 : ((1))*v 240 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h7920
  have h7983 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h7987 : ((1))*v 252 + (((-1)*W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h7983
  have h8017 : ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h7983
  have h8118 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z*W)/(X^4))*h31
  have h8139 : ((Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8118
  have h8243 : (((-1)*W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h33
  have h8253 : ((W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8243
  have h8284 : ((W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8243
  have h8456 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Y^2*W)/(X^4*Z))*h37
  have h8466 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4979-((1))*h8456
  have h8829 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h42
  have h8860 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8017-((1))*h8829
  have h8983 : (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(X^2*W))*h46
  have h8988 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h8983
  have h9077 : (((-1)*W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Y^2*Z))*h47
  have h9082 : ((1))*v 126 + (((-1)*W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9077
  have h9144 : (((-1)*W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^4*Z))*h49
  have h9148 : ((1))*v 168 + (((-1)*W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9144
  have h9190 : (((-1)*Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(Y^2*W))*h50
  have h9194 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9190
  have h9197 : ((1))*v 240 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9190
  have h9574 : (((-1)*Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h9148
  have h9578 : ((Z)/(W))*v 168 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7923-((1))*h9574
  have h9583 : ((Z)/(W))*v 168 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9197-((1))*h9574
  have h9788 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9194
  have h9793 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9082-(((-1)*W)/(X^2*Z))*h9788
  have h10659 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h9578
  have h10673 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-(((-1)*Z)/(W))*h10659
  have h10691 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8860-((1))*h10659
  have h10803 : (((-1)*Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h7987
  have h10874 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10691-((W)/(X^2*Z))*h10803
  have h11278 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11281 : (((-1)*W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-(((-1)*W)/(X^2*Z))*h11278
  have h11362 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11373 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8466-((1))*h11362
  have h11873 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h8988
  have h11901 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10673-((1))*h11873
  have h11908 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11373-(((-1)*W)/(X^4))*h11873
  have h11945 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10874-((W)/(X^2*Z))*h11873
  have h12103 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9793
  have h12140 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11945-((1))*h12103
  have h12880 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h12891 : (((1))/(X^4))*v 84 + ((1))*v 105 + (((-1)*Z)/(X^4))*v 168 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11908-((Y^2*W)/(X^4*Z))*h12880
  have h12988 : ((1))*v 60 + (((-1)*Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8253
  have h13005 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11281-(((-1)*W)/(X^4*Z))*h12988
  have h13026 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8284-((W)/(Z))*h12988
  have h13925 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h9583
  have h13951 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11901-((X^2*Z + (-1)*Z)/(X^2*W))*h13925
  have h13954 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13026-((1))*h13925
  have h13972 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + (((-1)*Z)/(X^4))*v 252 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12891-(((-1)*Z)/(X^4))*h13925
  have h14046 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12140-(((2))/(X^2))*h13925
  have h14374 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14046
  have h14379 : (((-1)*Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13951-((X^2*Z + (-1)*Z)/(X^2*W))*h14374
  have h14385 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13954-((2))*h14374
  have h14408 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13972-(((-1)*Z)/(X^4))*h14374
  have h14932 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14385
  have h14933 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13005-(((-1))/(X^4))*h14932
  have h14945 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14379-(((-1)*Z)/(W))*h14932
  have h14969 : ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14408-(((1))/(X^4))*h14932
  have h15389 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14933
  have h15394 : ((1))*v 105 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14969-((1))*h15389
  have h15470 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h14945
  have h15475 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15394-((W)/(X^2*Z))*h15470
  have h15788 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15475
  have h15797 : ((Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8139-((1))*h15788
  have h16051 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^4)/(Z*W))*h15797
  have hz48 : v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16051
  have hz105 : v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15788
  have hz330 : v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15470
  have hz189 : v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15389
  have hz84 : v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14932
  have hz252 : v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14374
  have hz168 : v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13925 - ((-1))*hz252
  have hz60 : v 60=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12988 - (((-1)*Z)/(W))*hz84
  have hz80 : v 80=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12880 - (((-1)*X^2)/(Y^2))*hz330
  have hz126 : v 126=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12103 - (((-1))/(X^2))*hz252
  have hz120 : v 120=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11873 - (((-1)*Z)/(W))*hz168
  have hz273 : v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11362 - (((-1))/(X^4))*hz84
  have hz270 : v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11278 - (((-1))/(X^2))*hz60
  have hz300 : v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10803 - (((-1)*Z)/(W))*hz252
  have hz294 : v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10659 - (((-1))/(X^2))*hz168
  have hz180 : v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9788 - (((-1)*Z)/(W))*hz252
  have hz240 : v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9574 - (((-1)*Z)/(W))*hz168
  have hz400 : v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9190 - (((-1)*Z)/(Y^2*W))*hz252
  have hz399 : v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9144 - (((-1)*W)/(X^4*Z))*hz240
  have hz392 : v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9077 - (((-1)*W)/(Y^2*Z))*hz180
  have hz390 : v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8983 - (((-1)*Z)/(X^2*W))*hz168
  have hz378 : v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8829 - (((-1)*W)/(X^2*Z))*hz120
  have hz357 : v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8456 - (((-1)*Y^2*W)/(X^4*Z))*hz80
  have hz336 : v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8243 - (((-1)*W)/(Z))*hz60
  have hz315 : v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8118 - (((-1)*Z*W)/(X^4))*hz48
  have hz42 : v 42=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7983 - (((-1)*W)/(X^2*Z))*hz300
  have hz40 : v 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h7920 - (((-1)*X^2*Z)/(Y^2*W))*hz294
  have hz288 : v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4961
  have hz36 : v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4658
  have hz280 : v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4510
  have hz24 : v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3917
  have hz210 : v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3639
  have hz204 : v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3525
  have hz414 : v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3389
  have hz0 : v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h2691
  intro i
  fin_cases i <;> dsimp [coordinate] <;> assumption

#print axioms selected_kernel_case4

/-- Kernel-checked target consequence of the selected rows.
All denominators are powers of the nonzero geometric variables; no
nonvanishing Hecke eigenvalue or residual determinant is assumed. -/
theorem selected_kernel_case6 (X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 420 → ℂ) (hv : selectedRows6 X Y Z W v=0) :
    ∀ i : Fin 35, v (coordinate i)=0 := by
  have h5 : ((1))*v 0=0 := by
    have h := congrFun hv (0:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h23 : ((1))*v 24 + (((-1)*X^2)/(Z*W))*v 210=0 := by
    have h := congrFun hv (1:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h27 : ((1))*v 36 + (((-1)*Y^2)/(Z*W))*v 280=0 := by
    have h := congrFun hv (2:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h28 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    have h := congrFun hv (3:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h29 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    have h := congrFun hv (4:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h31 : ((1))*v 48 + (((-1)*X^4)/(Z*W))*v 315=0 := by
    have h := congrFun hv (5:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h33 : ((1))*v 60 + (((-1)*Z)/(W))*v 336=0 := by
    have h := congrFun hv (6:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h37 : ((1))*v 80 + (((-1)*X^4*Z)/(Y^2*W))*v 357=0 := by
    have h := congrFun hv (7:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h42 : ((1))*v 120 + (((-1)*X^2*Z)/(W))*v 378=0 := by
    have h := congrFun hv (8:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h46 : ((1))*v 168 + (((-1)*X^2*W)/(Z))*v 390=0 := by
    have h := congrFun hv (9:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h47 : ((1))*v 180 + (((-1)*Y^2*Z)/(W))*v 392=0 := by
    have h := congrFun hv (10:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h49 : ((1))*v 240 + (((-1)*X^4*Z)/(W))*v 399=0 := by
    have h := congrFun hv (11:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h50 : ((1))*v 252 + (((-1)*Y^2*W)/(Z))*v 400=0 := by
    have h := congrFun hv (12:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h99 : (((-1))/(X^2*Z*W))*v 0 + ((1))*v 414=0 := by
    have h := congrFun hv (13:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h184 : ((1))*v 204 + ((-1)*X^2)*v 414=0 := by
    have h := congrFun hv (14:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h186 : (((-1))/(X^2))*v 0 + ((1))*v 210=0 := by
    have h := congrFun hv (15:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h196 : ((1))*v 168 + ((-1)*X^4)*v 399=0 := by
    have h := congrFun hv (16:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h197 : ((1))*v 180 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (17:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h259 : ((-1)*Y^2)*v 40 + ((1))*v 240=0 := by
    have h := congrFun hv (18:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h260 : ((-1)*X^2)*v 42 + ((1))*v 252=0 := by
    have h := congrFun hv (19:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h266 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    have h := congrFun hv (20:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h268 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    have h := congrFun hv (21:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h275 : (((-1))/(Y^2))*v 0 + ((1))*v 280=0 := by
    have h := congrFun hv (22:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h279 : ((-1))*v 24 + ((1))*v 288=0 := by
    have h := congrFun hv (23:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h297 : ((1))*v 120 + ((-1)*X^2)*v 390=0 := by
    have h := congrFun hv (24:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h298 : ((1))*v 126 + (((-1)*Y^2)/(X^2))*v 392=0 := by
    have h := congrFun hv (25:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h350 : (((-1)*Y^2)/(X^2))*v 80 + ((1))*v 330=0 := by
    have h := congrFun hv (26:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h352 : ((-1))*v 84 + ((1))*v 336=0 := by
    have h := congrFun hv (27:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h479 : ((1))*v 240 + ((-1)*Y^2)*v 400=0 := by
    have h := congrFun hv (28:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h912 : ((1))*v 189 + (((-1)*W)/(X^2*Z))*v 270=0 := by
    have h := congrFun hv (29:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1760 : ((1))*v 105 + ((1))*v 315=0 := by
    have h := congrFun hv (30:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1771 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(W))*v 294 + ((1))*v 330=0 := by
    have h := congrFun hv (31:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1785 : ((1))*v 84 + ((1))*v 168 + ((1))*v 252 + ((1))*v 336=0 := by
    have h := congrFun hv (32:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1810 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((W)/(X^4))*v 204 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    have h := congrFun hv (33:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h1932 : ((1))*v 42 + ((1))*v 126 + ((1))*v 294 + ((1))*v 378=0 := by
    have h := congrFun hv (34:Fin 35)
    norm_num [selectedRows6] at h ⊢
    exact h
  have h2691 : ((1))*v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h5
  have h2701 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h99-(((-1))/(X^2*Z*W))*h2691
  have h2706 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h186-(((-1))/(X^2))*h2691
  have h2709 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h275-(((-1))/(Y^2))*h2691
  have h3415 : ((1))*v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2701
  have h3420 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h184-((-1)*X^2)*h3415
  have h3553 : ((1))*v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3420
  have h3576 : ((W)/(X^4))*v 36 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1810-((W)/(X^4))*h3553
  have h3673 : ((1))*v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2706
  have h3676 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h23-(((-1)*X^2)/(Z*W))*h3673
  have h3955 : ((1))*v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3676
  have h3963 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h279-((-1))*h3955
  have h4566 : ((1))*v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h2709
  have h4568 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h27-(((-1)*Y^2)/(Z*W))*h4566
  have h4714 : ((1))*v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h4568
  have h4766 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((W)/(X^4))*v 288 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3576-((W)/(X^4))*h4714
  have h5031 : ((1))*v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h3963
  have h5049 : ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4766-((W)/(X^4))*h5031
  have h8032 : ((1))*v 40 + (((-1)*X^2*Z)/(Y^2*W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h28
  have h8035 : ((1))*v 240 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h259-((-1)*Y^2)*h8032
  have h8095 : ((1))*v 42 + (((-1)*W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h29
  have h8099 : ((1))*v 252 + (((-1)*W)/(Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h260-((-1)*X^2)*h8095
  have h8129 : ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1932-((1))*h8095
  have h8232 : (((-1)*Z*W)/(X^4))*v 48 + ((1))*v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z*W)/(X^4))*h31
  have h8253 : ((Z*W)/(X^4))*v 48 + ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1760-((1))*h8232
  have h8357 : (((-1)*W)/(Z))*v 60 + ((1))*v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Z))*h33
  have h8367 : ((W)/(Z))*v 60 + ((-1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h352-((1))*h8357
  have h8398 : ((W)/(Z))*v 60 + ((1))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1785-((1))*h8357
  have h8576 : (((-1)*Y^2*W)/(X^4*Z))*v 80 + ((1))*v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Y^2*W)/(X^4*Z))*h37
  have h8586 : ((Y^2*W)/(X^4*Z))*v 80 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5049-((1))*h8576
  have h8959 : (((-1)*W)/(X^2*Z))*v 120 + ((1))*v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h42
  have h8990 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + ((1))*v 294 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8129-((1))*h8959
  have h9115 : (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(X^2*W))*h46
  have h9120 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h297-((-1)*X^2)*h9115
  have h9213 : (((-1)*W)/(Y^2*Z))*v 180 + ((1))*v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(Y^2*Z))*h47
  have h9218 : ((1))*v 126 + (((-1)*W)/(X^2*Z))*v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h298-(((-1)*Y^2)/(X^2))*h9213
  have h9280 : (((-1)*W)/(X^4*Z))*v 240 + ((1))*v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^4*Z))*h49
  have h9284 : ((1))*v 168 + (((-1)*W)/(Z))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h196-((-1)*X^4)*h9280
  have h9326 : (((-1)*Z)/(Y^2*W))*v 252 + ((1))*v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(Y^2*W))*h50
  have h9330 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h197-((-1)*Y^2)*h9326
  have h9333 : ((1))*v 240 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h479-((-1)*Y^2)*h9326
  have h9710 : (((-1)*Z)/(W))*v 168 + ((1))*v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h9284
  have h9714 : ((Z)/(W))*v 168 + (((-1)*X^2*Z)/(W))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8035-((1))*h9710
  have h9719 : ((Z)/(W))*v 168 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9333-((1))*h9710
  have h9930 : ((1))*v 180 + (((-1)*Z)/(W))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9330
  have h9935 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9218-(((-1)*W)/(X^2*Z))*h9930
  have h10811 : (((-1))/(X^2))*v 168 + ((1))*v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*W)/(X^2*Z))*h9714
  have h10825 : (((-1)*Z)/(W))*v 84 + ((1))*v 120 + (((-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h1771-(((-1)*Z)/(W))*h10811
  have h10843 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + ((W)/(X^2*Z))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8990-((1))*h10811
  have h10959 : (((-1)*Z)/(W))*v 252 + ((1))*v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*Z)/(W))*h8099
  have h11030 : ((W)/(X^2*Z))*v 120 + ((1))*v 126 + (((1))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10843-((W)/(X^2*Z))*h10959
  have h11450 : (((-1))/(X^2))*v 60 + ((1))*v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h266
  have h11453 : (((-1)*W)/(X^4*Z))*v 60 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h912-(((-1)*W)/(X^2*Z))*h11450
  have h11536 : (((-1))/(X^4))*v 84 + ((1))*v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h268
  have h11547 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((W)/(X^4))*v 120 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8586-((1))*h11536
  have h12057 : ((1))*v 120 + (((-1)*Z)/(W))*v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9120
  have h12085 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 168 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10825-((1))*h12057
  have h12092 : ((Y^2*W)/(X^4*Z))*v 80 + (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11547-((W)/(X^4))*h12057
  have h12129 : ((1))*v 126 + (((2))/(X^2))*v 168 + (((1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11030-((W)/(X^2*Z))*h12057
  have h12297 : ((1))*v 126 + (((-1))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h9935
  have h12334 : (((2))/(X^2))*v 168 + (((2))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12129-((1))*h12297
  have h13088 : ((1))*v 80 + (((-1)*X^2)/(Y^2))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((-1)*X^2)/(Y^2))*h350
  have h13099 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((Z)/(X^4))*v 168 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12092-((Y^2*W)/(X^4*Z))*h13088
  have h13196 : ((1))*v 60 + (((-1)*Z)/(W))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((Z)/(W))*h8367
  have h13213 : (((-1))/(X^4))*v 84 + ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11453-(((-1)*W)/(X^4*Z))*h13196
  have h13234 : ((2))*v 84 + ((1))*v 168 + ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8398-((W)/(Z))*h13196
  have h14149 : ((1))*v 168 + ((-1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((W)/(Z))*h9719
  have h14175 : (((-1)*Z)/(W))*v 84 + ((X^2*Z + (-1)*Z)/(X^2*W))*v 252 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12085-((X^2*Z + (-1)*Z)/(X^2*W))*h14149
  have h14178 : ((2))*v 84 + ((2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13234-((1))*h14149
  have h14196 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((Z)/(X^4))*v 252 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13099-((Z)/(X^4))*h14149
  have h14270 : (((4))/(X^2))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12334-(((2))/(X^2))*h14149
  have h14612 : ((1))*v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^2)/((4)))*h14270
  have h14617 : (((-1)*Z)/(W))*v 84 + ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14175-((X^2*Z + (-1)*Z)/(X^2*W))*h14612
  have h14623 : ((2))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14178-((2))*h14612
  have h14646 : (((1))/(X^4))*v 84 + ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14196-((Z)/(X^4))*h14612
  have h15188 : ((1))*v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) (((1))/((2)))*h14623
  have h15189 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13213-(((-1))/(X^4))*h15188
  have h15201 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14617-(((-1)*Z)/(W))*h15188
  have h15225 : ((1))*v 105 + ((1))*v 189 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14646-(((1))/(X^4))*h15188
  have h15663 : ((1))*v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15189
  have h15668 : ((1))*v 105 + ((W)/(X^2*Z))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15225-((1))*h15663
  have h15744 : ((1))*v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15201
  have h15749 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15668-((W)/(X^2*Z))*h15744
  have h16066 : ((1))*v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((1))*h15749
  have h16075 : ((Z*W)/(X^4))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8253-((1))*h16066
  have h16357 : ((1))*v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) ((X^4)/(Z*W))*h16075
  have hz48 : v 48=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16357
  have hz105 : v 105=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h16066
  have hz330 : v 330=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15744
  have hz189 : v 189=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15663
  have hz84 : v 84=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h15188
  have hz252 : v 252=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14612
  have hz168 : v 168=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h14149 - ((-1))*hz252
  have hz60 : v 60=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13196 - (((-1)*Z)/(W))*hz84
  have hz80 : v 80=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h13088 - (((-1)*X^2)/(Y^2))*hz330
  have hz126 : v 126=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12297 - (((-1))/(X^2))*hz252
  have hz120 : v 120=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h12057 - (((-1)*Z)/(W))*hz168
  have hz273 : v 273=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11536 - (((-1))/(X^4))*hz84
  have hz270 : v 270=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h11450 - (((-1))/(X^2))*hz60
  have hz300 : v 300=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10959 - (((-1)*Z)/(W))*hz252
  have hz294 : v 294=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h10811 - (((-1))/(X^2))*hz168
  have hz180 : v 180=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9930 - (((-1)*Z)/(W))*hz252
  have hz240 : v 240=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9710 - (((-1)*Z)/(W))*hz168
  have hz400 : v 400=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9326 - (((-1)*Z)/(Y^2*W))*hz252
  have hz399 : v 399=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9280 - (((-1)*W)/(X^4*Z))*hz240
  have hz392 : v 392=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9213 - (((-1)*W)/(Y^2*Z))*hz180
  have hz390 : v 390=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h9115 - (((-1)*Z)/(X^2*W))*hz168
  have hz378 : v 378=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8959 - (((-1)*W)/(X^2*Z))*hz120
  have hz357 : v 357=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8576 - (((-1)*Y^2*W)/(X^4*Z))*hz80
  have hz336 : v 336=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8357 - (((-1)*W)/(Z))*hz60
  have hz315 : v 315=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8232 - (((-1)*Z*W)/(X^4))*hz48
  have hz42 : v 42=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8095 - (((-1)*W)/(X^2*Z))*hz300
  have hz40 : v 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h8032 - (((-1)*X^2*Z)/(Y^2*W))*hz294
  have hz288 : v 288=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h5031
  have hz36 : v 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4714
  have hz280 : v 280=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h4566
  have hz24 : v 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3955
  have hz210 : v 210=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3673
  have hz204 : v 204=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3553
  have hz414 : v 414=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h3415
  have hz0 : v 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ,hW]; all_goals ring1)) h2691
  intro i
  fin_cases i <;> dsimp [coordinate] <;> assumption

#print axioms selected_kernel_case6

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end
