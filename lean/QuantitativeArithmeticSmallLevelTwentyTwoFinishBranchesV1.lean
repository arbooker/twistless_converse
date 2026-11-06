module

public import QuantitativeArithmeticSmallLevelTwentyTwoGroupHeckeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def A5 : SL(2,ℤ) := ⟨!![5,-2;-22,9],by decide⟩
def B5 : SL(2,ℤ) := ⟨!![5,2;22,9],by decide⟩
def C5 : SL(2,ℤ) := ⟨!![5,-1;-44,9],by decide⟩
def P : GL (Fin 2) ℝ := matrix (4/Real.sqrt 2) (1/Real.sqrt 2)
    (22/Real.sqrt 2) (6/Real.sqrt 2) (by
      have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith)
theorem P_det : (GeneralLinearGroup.det P:ℝ)=1 := matrix_det _ _ _ _ _

private theorem inverse_E : E⁻¹=SmallLevelRamifiedTwo.Q 22 12 (by decide) := inv_inv _

theorem M0_X : M 0*SpecialLinearGroup.mapGL ℝ X=(-1:GL (Fin 2) ℝ)*W*translation (-1)*W*SpecialLinearGroup.mapGL ℝ Y*translation (-1)*M 1 := by
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

theorem M1_X : M 1*SpecialLinearGroup.mapGL ℝ X=(-1:GL (Fin 2) ℝ)*E⁻¹*translation (-1)*E⁻¹*SpecialLinearGroup.mapGL ℝ C5*M 0 := by
  rw [inverse_E]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

theorem M0_Y : M 0*SpecialLinearGroup.mapGL ℝ Y=(-1:GL (Fin 2) ℝ)*W*translation 1*W*SpecialLinearGroup.mapGL ℝ X*M 1 := by
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

theorem M1_Y : M 1*SpecialLinearGroup.mapGL ℝ Y=W*E*translation 1*W*SpecialLinearGroup.mapGL ℝ B5*translation (-1)*E⁻¹*M 0 := by
  rw [inverse_E]
  rw [E_explicit]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

theorem A5_factor : SpecialLinearGroup.mapGL ℝ A5=W*P*R := by
  rw [R,E_explicit]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

theorem C5_factor : SpecialLinearGroup.mapGL ℝ C5=E*translation 1*W*P*W := by
  rw [E_explicit]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,X,Y,A5,B5,C5,P,R,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 22)^2) ht]

def J1 : GL (Fin 2) ℝ := translation (-2/3)*(M 0)⁻¹*W⁻¹
def J2 : GL (Fin 2) ℝ := translation (-1)*M 1*(M 0)⁻¹*W⁻¹
def Z0 : GL (Fin 2) ℝ := R*translation (4/5)*translation (-1)*E⁻¹*M 0

private theorem M0_inverse : (M 0)⁻¹=matrix (Real.sqrt 2) 0 0 (1/Real.sqrt 2) (by field_simp; ring) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

theorem branch_A0 : translation (-2/3)*M 1=A0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,A0,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

theorem branch_B0 : J1*Z0=B0 := by
  rw [J1,Z0,R,inverse_E,E_explicit,M0_inverse,W_inverse]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,B0,B0rat,C0,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    norm_num [show (Real.sqrt 2)^4=((Real.sqrt 2)^2)^2 by ring,ht,hs]

theorem branch_C0 : J2*Z0=C0 := by
  rw [J2,Z0,R,inverse_E,E_explicit,M0_inverse,W_inverse]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [M,B0,B0rat,C0,W,fricke,translation,SmallLevelRamifiedTwo.Q,
      matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    norm_num [show (Real.sqrt 2)^4=((Real.sqrt 2)^2)^2 by ring,ht,hs]

#print axioms M0_X
#print axioms M1_X
#print axioms M0_Y
#print axioms M1_Y
#print axioms A5_factor
#print axioms C5_factor
#print axioms branch_A0
#print axioms branch_B0
#print axioms branch_C0
end QuantitativeArithmeticSmallLevelTwentyTwo
