module

public import SmallLevelTwentyOneChiFiveRigidityV1
public import SmallLevelSixPairV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFiveGroup
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def A : SL(2,ℤ) := ⟨!![5,1;-21,-4],by decide⟩
def B : SL(2,ℤ) := ⟨!![5,-1;21,-4],by decide⟩
def C : SL(2,ℤ) := ⟨!![5,-2;-42,17],by decide⟩
def D : SL(2,ℤ) := ⟨!![5,2;42,17],by decide⟩
def E : SL(2,ℤ) := ⟨!![2,-1;-21,11],by decide⟩

theorem E_known : E=(oddMatrix 21 11 (by decide))⁻¹ := by decide
theorem C_inv : C⁻¹=(⟨!![17,2;42,5],by decide⟩ : SL(2,ℤ)) := by decide
theorem D_factor : D=lower 21*E*C⁻¹*E*ModularGroup.T := by decide

theorem sqrt_conductor : Real.sqrt 525=5*Real.sqrt 21 := by
  rw [show (525:ℝ)=25*21 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem C_branch : fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ C*translation (2/5)=
    translation (2/5)*fricke 525 (by decide) := by
  have ht : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,C,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem D_branch : fricke 21 (by decide)*SpecialLinearGroup.mapGL ℝ D*translation (-2/5)=
    translation (-2/5)*fricke 525 (by decide) := by
  have ht : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,D,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem elliptic_factor : SmallLevelTwentyOneChiFiveRigidity.ellipticReal=
    SpecialLinearGroup.mapGL ℝ C⁻¹*SpecialLinearGroup.mapGL ℝ E*translation (1/5) := by
  rw [C_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SmallLevelTwentyOneChiFiveRigidity.ellipticReal,
      SmallLevelTwentyOneChiFiveRigidity.elliptic,E,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,dotProduct,Fin.sum_univ_two]

#print axioms D_factor
#print axioms C_branch
#print axioms D_branch
#print axioms elliptic_factor
end SmallLevelTwentyOneChiFiveGroup
