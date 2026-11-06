module
public import SmallLevelFiniteGridSupportV1
public import SmallLevelTwentySixContinuationMinorMMMV1
public import SmallLevelTwentySixUnitMMMRowsBundleV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 7000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentySixUnitMMM
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteGridSupport SmallLevelTwentySixContinuationMinorMMM

def partLinear0 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart0 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart0] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart0] <;> ring

theorem part_analytic_0 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart0 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart0]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_0

def partLinear1 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart1 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart1] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart1] <;> ring

theorem part_analytic_1 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart1 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart1]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_1

def partLinear2 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart2 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart2] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart2] <;> ring

theorem part_analytic_2 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart2 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart2]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_2

def partLinear3 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart3 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart3] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart3] <;> ring

theorem part_analytic_3 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart3 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart3]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_3

def partLinear4 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart4 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart4] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart4] <;> ring

theorem part_analytic_4 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart4 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart4]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_4

def partLinear5 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart5 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart5] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart5] <;> ring

theorem part_analytic_5 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart5 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart5]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_5

def partLinear6 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart6 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart6] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart6] <;> ring

theorem part_analytic_6 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart6 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart6]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_6

def partLinear7 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart7 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart7] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart7] <;> ring

theorem part_analytic_7 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart7 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart7]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_7

def partLinear8 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart8 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart8] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart8] <;> ring

theorem part_analytic_8 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart8 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart8]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_8

def partLinear9 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart9 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart9] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart9] <;> ring

theorem part_analytic_9 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart9 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart9]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_9

def partLinear10 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart10 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart10] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart10] <;> ring

theorem part_analytic_10 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart10 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart10]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_10

def partLinear11 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart11 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart11] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart11] <;> ring

theorem part_analytic_11 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart11 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart11]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_11

def partLinear12 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart12 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart12] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart12] <;> ring

theorem part_analytic_12 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart12 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart12]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_12

def partLinear13 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart13 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart13] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart13] <;> ring

theorem part_analytic_13 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart13 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart13]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_13

def partLinear14 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart14 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart14] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart14] <;> ring

theorem part_analytic_14 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart14 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart14]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_14

def partLinear15 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart15 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart15] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart15] <;> ring

theorem part_analytic_15 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart15 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart15]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_15

def partLinear16 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart16 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart16] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart16] <;> ring

theorem part_analytic_16 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart16 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart16]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_16

def partLinear17 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart17 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart17] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart17] <;> ring

theorem part_analytic_17 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart17 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart17]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_17

def partLinear18 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart18 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart18] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart18] <;> ring

theorem part_analytic_18 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart18 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart18]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_18

def partLinear19 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart19 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart19] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart19] <;> ring

theorem part_analytic_19 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart19 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart19]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_19

def partLinear20 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart20 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart20] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart20] <;> ring

theorem part_analytic_20 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart20 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart20]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_20

def partLinear21 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart21 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart21] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart21] <;> ring

theorem part_analytic_21 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart21 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart21]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_21

def partLinear22 (X Y Z W a b : ℂ) : (Fin 780→ℂ)→ₗ[ℂ](Fin 16→ℂ) where
  toFun := sourceRowsPart22 X Y Z W a b
  map_add' v w := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart22] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> norm_num [sourceRowsPart22] <;> ring

theorem part_analytic_22 (m : ℕ) (a b : ℂ) (v : Fin 780→ℂ) (i : Fin 16) (z : ℂ) :
    AnalyticAt ℂ (fun s => sourceRowsPart22 (parameter 2 m s) (parameter 3 m s)
      (parameter 13 m s) (parameter 5 m s) a b v i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZ:=parameter_ne_zero 13 m (by decide) z
  have hZa:=parameter_analytic 13 m (by decide) z
  have hW:=parameter_ne_zero 5 m (by decide) z
  have hWa:=parameter_analytic 5 m (by decide) z
  fin_cases i <;> norm_num [sourceRowsPart22]
  all_goals fun_prop (disch := simp [hX,hY,hZ,hW])

#print axioms part_analytic_22

end SmallLevelTwentySixUnitMMM
