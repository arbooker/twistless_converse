module

public import SmallLevelThirtyBRigidityV1
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelDoubleCosetDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section

namespace SmallLevelThirtyC

open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_2_ne : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
theorem sqrt_5_ne : Real.sqrt 5≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
theorem sqrt_10_ne : Real.sqrt 10≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
theorem sqrt_30_ne : Real.sqrt 30≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

def C : GL (Fin 2) ℝ := matrix (4/Real.sqrt 2) (-1/Real.sqrt 2)
    (-30/Real.sqrt 2) (8/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_2_ne]
  nlinarith)

theorem C_det : (GeneralLinearGroup.det C:ℝ)=1 := matrix_det _ _ _ _ _

def Cp : GL (Fin 2) ℝ := matrix (4/Real.sqrt 2) (1/Real.sqrt 2)
    (30/Real.sqrt 2) (8/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_2_ne]
  nlinarith)

theorem Cp_det : (GeneralLinearGroup.det Cp:ℝ)=1 := matrix_det _ _ _ _ _

def Ci : GL (Fin 2) ℝ := matrix (8/Real.sqrt 2) (1/Real.sqrt 2)
    (30/Real.sqrt 2) (4/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_2_ne]
  nlinarith)

theorem Ci_det : (GeneralLinearGroup.det Ci:ℝ)=1 := matrix_det _ _ _ _ _

def L : GL (Fin 2) ℝ := matrix (-5/Real.sqrt 5) (1/Real.sqrt 5)
    (-30/Real.sqrt 5) (5/Real.sqrt 5) (by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_5_ne]
  nlinarith)

theorem L_det : (GeneralLinearGroup.det L:ℝ)=1 := matrix_det _ _ _ _ _

def R : GL (Fin 2) ℝ := matrix (-5/Real.sqrt 5) (-1/Real.sqrt 5)
    (30/Real.sqrt 5) (5/Real.sqrt 5) (by
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_5_ne]
  nlinarith)

theorem R_det : (GeneralLinearGroup.det R:ℝ)=1 := matrix_det _ _ _ _ _

def E : GL (Fin 2) ℝ := matrix (-10/Real.sqrt 10) (2/Real.sqrt 10)
    (-30/Real.sqrt 10) (5/Real.sqrt 10) (by
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_10_ne]
  nlinarith)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem C_Ci : C*Ci=1 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C,Ci,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_2_ne] <;> nlinarith

theorem Ci_inverse : Ci=C⁻¹ := by
  have h := congrArg (fun x : GL (Fin 2) ℝ => C⁻¹*x) C_Ci
  simpa only [← mul_assoc,inv_mul_cancel,one_mul,mul_one] using h

theorem sqrt_product : Real.sqrt 30*Real.sqrt 6=6*Real.sqrt 5 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤30)]
  rw [show (30:ℝ)*6=36*5 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem L_relation : L=(-1)*fricke 30 (by decide)*SmallLevelThirtyB.B := by
  have hs2 : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hs30 : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hp := sqrt_product
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [L,fricke,SmallLevelThirtyB.B,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_5_ne,sqrt_30_ne,SmallLevelThirtyB.sqrt_six_ne] <;> nlinarith

theorem R_relation : R=fricke 30 (by decide)*SmallLevelThirtyB.A := by
  have hs2 : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hs6 : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  have hs30 : (Real.sqrt 30)^2=30 := Real.sq_sqrt (by norm_num)
  have hp := sqrt_product
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [R,fricke,SmallLevelThirtyB.A,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_5_ne,sqrt_30_ne,SmallLevelThirtyB.sqrt_six_ne] <;> nlinarith

theorem double_coset : Cp=L*C⁻¹*R := by
  rw [← Ci_inverse]
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs5 : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Cp,L,Ci,R,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_2_ne,sqrt_5_ne] <;> nlinarith

theorem E_branch : E*translation (1/4)=C⁻¹*R*translation (-(1/4)) := by
  rw [← Ci_inverse]
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hs5 : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hp : Real.sqrt 10=Real.sqrt 2*Real.sqrt 5 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,Ci,R,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,hp] <;>
    field_simp [sqrt_2_ne,sqrt_5_ne] <;> norm_num [hs2,hs5]

#print axioms L_relation
#print axioms R_relation
#print axioms double_coset
#print axioms E_branch

end SmallLevelThirtyC
