module

public import QuantitativeArithmeticSmallLevelTwentyTwoEllipticSignsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

def A0 : GL (Fin 2) ℝ := matrix (1/Real.sqrt 2) (-1/(3*Real.sqrt 2)) 0 (Real.sqrt 2)
  (by field_simp; ring)
def B0rat : SL(2,ℚ) := ⟨!![27/5,22/15;-66/5,-17/5],by norm_num [det_fin_two]⟩
def B0 : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ B0rat
def C0 : GL (Fin 2) ℝ := matrix (49/(5*Real.sqrt 2)) (13/(5*Real.sqrt 2))
    (-132/(5*Real.sqrt 2)) (-34/(5*Real.sqrt 2)) (by
      have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith)

theorem A0_det : (GeneralLinearGroup.det A0:ℝ)=1 := matrix_det _ _ _ _ _
theorem B0_det : (GeneralLinearGroup.det B0:ℝ)=1 := by simp [B0]
theorem C0_det : (GeneralLinearGroup.det C0:ℝ)=1 := matrix_det _ _ _ _ _

private theorem sqrt_twenty_two : Real.sqrt 22=Real.sqrt 2*Real.sqrt 11 := by
  rw [show (22:ℝ)=2*11 by norm_num,Real.sqrt_mul (by norm_num)]

/-- The exact normalized K coordinates. -/
theorem K_explicit : K=matrix (Real.sqrt 22) (23/(3*Real.sqrt 22))
    (-3*Real.sqrt 22) (-Real.sqrt 22) (by
      have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith) := by
  rw [K,W_inverse]
  have hy : Y⁻¹=(⟨!![-7,-1;22,3],by decide⟩:SL(2,ℤ)) := by decide
  rw [hy]
  have hs : (Real.sqrt 22)^2=22 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 22≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

/-- The actual product R*t(2/3) is the negative normalized raw L matrix. -/
theorem L_explicit : L=matrix (-Real.sqrt 11) (-7/(3*Real.sqrt 11))
    (2*Real.sqrt 11) (Real.sqrt 11/3) (by
      have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith) := by
  rw [L,R,E_explicit]
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 11≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W,fricke,translation,sqrt_twenty_two,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 11)^2) ht]

theorem K_C0 : K*C0=Z := by
  rw [K_explicit]
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 11≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C0,Z,sqrt_twenty_two,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 11)^2) ht]

theorem A0_Z : A0*Z=K*B0 := by
  rw [K_explicit]
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 11≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A0,Z,B0,B0rat,sqrt_twenty_two,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 11)^2) ht]

theorem K_L_A0 : K*L*A0=V := by
  rw [K_explicit,L_explicit]
  have hs : (Real.sqrt 11)^2=11 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 11≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A0,V,Vrat,sqrt_twenty_two,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 11)^2) ht]

#print axioms K_C0
#print axioms A0_Z
#print axioms K_L_A0
end QuantitativeArithmeticSmallLevelTwentyTwo
