module
public import SmallLevelTwentySixPairsV1
public import SmallLevelNormalizedEvenFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_two_ne : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
theorem sqrt_level_ne : Real.sqrt 26≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

def P : GL (Fin 2) ℝ :=
  matrix (4/Real.sqrt 2) (-1/Real.sqrt 2) (26/Real.sqrt 2) (-6/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem P_det : (GeneralLinearGroup.det P:ℝ)=1 := matrix_det _ _ _ _ _

def Q : GL (Fin 2) ℝ :=
  matrix (4/Real.sqrt 2) (1/Real.sqrt 2) (-26/Real.sqrt 2) (-6/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem Q_det : (GeneralLinearGroup.det Q:ℝ)=1 := matrix_det _ _ _ _ _

def Pi : GL (Fin 2) ℝ :=
  matrix (-6/Real.sqrt 2) (1/Real.sqrt 2) (-26/Real.sqrt 2) (4/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem Pi_det : (GeneralLinearGroup.det Pi:ℝ)=1 := matrix_det _ _ _ _ _

def Qi : GL (Fin 2) ℝ :=
  matrix (-6/Real.sqrt 2) (-1/Real.sqrt 2) (26/Real.sqrt 2) (4/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem Qi_det : (GeneralLinearGroup.det Qi:ℝ)=1 := matrix_det _ _ _ _ _

def P6 : GL (Fin 2) ℝ :=
  matrix (6/Real.sqrt 2) (-1/Real.sqrt 2) (26/Real.sqrt 2) (-4/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem P6_det : (GeneralLinearGroup.det P6:ℝ)=1 := matrix_det _ _ _ _ _

def Q6 : GL (Fin 2) ℝ :=
  matrix (6/Real.sqrt 2) (1/Real.sqrt 2) (-26/Real.sqrt 2) (-4/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem Q6_det : (GeneralLinearGroup.det Q6:ℝ)=1 := matrix_det _ _ _ _ _

theorem P_inverse : Pi=P⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,Pi,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem P6_inverse : P6=(-1 : GL (Fin 2) ℝ)*P⁻¹ := by
  rw [← P_inverse]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P6,Pi,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem Q_inverse : Qi=Q⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q,Qi,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem Q6_inverse : Q6=(-1 : GL (Fin 2) ℝ)*Q⁻¹ := by
  rw [← Q_inverse]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q6,Qi,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem sqrt_208 : Real.sqrt 208=2*Real.sqrt 26*Real.sqrt 2 := by
  rw [mul_assoc,← Real.sqrt_mul (by norm_num : (0:ℝ)≤26)]
  rw [show (208:ℝ)=4*(26*2) by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem P_factor4 : fricke 26 (by decide)*P*translation (-(-(1/4)))=
    translation (-(1/4))*fricke 208 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,P,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_208] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

theorem Q_factor4 : fricke 26 (by decide)*Q*translation (-(1/4))=
    translation (1/4)*fricke 208 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Q,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_208] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

theorem sqrt_468 : Real.sqrt 468=3*Real.sqrt 26*Real.sqrt 2 := by
  rw [mul_assoc,← Real.sqrt_mul (by norm_num : (0:ℝ)≤26)]
  rw [show (468:ℝ)=9*(26*2) by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem P_factor6 : fricke 26 (by decide)*P6*translation (-(-(1/6)))=
    translation (-(1/6))*fricke 468 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,P6,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_468] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

theorem Q_factor6 : fricke 26 (by decide)*Q6*translation (-(1/6))=
    translation (1/6)*fricke 468 (by decide) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Q6,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_468] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

#print axioms P_factor4
#print axioms P_factor6
end SmallLevelTwentySix
