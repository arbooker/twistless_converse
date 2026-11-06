module

public import SmallLevelThirtyTwoPairV1
public import SmallLevelThirtyTwoEllipticV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtyTwo

open Matrix UpperHalfPlane SmallLevelThree SmallLevelEvenScale
open scoped MatrixGroups ModularForm

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem positive_branch : lowerBranch 8 1=SpecialLinearGroup.mapGL ℝ A*upperBranch (-1) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, A, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem negative_branch : lowerBranch 8 (-1)=SpecialLinearGroup.mapGL ℝ A⁻¹*upperBranch 1 := by
  have hi : A⁻¹=(⟨!![3,-1;-8,3],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerBranch, upperBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_branch : ellipticReal*upperBranch (-1)=SpecialLinearGroup.mapGL ℝ A⁻¹*upperBranch 1 := by
  have hi : A⁻¹=(⟨!![3,-1;-8,3],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ellipticReal, elliptic, upperBranch, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem actual_defect_elliptic {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 32 k f) :
    ((scaledFunction k f ∣[(k:ℤ)] A)-scaledFunction k f) ∣[(k:ℤ)] ellipticReal=
      (scaledFunction k f ∣[(k:ℤ)] A)-scaledFunction k f := by
  let g := scaledFunction k f
  have he := actual_pair hf
  rw [positive_branch, negative_branch, SlashAction.slash_mul, SlashAction.slash_mul] at he
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] (upperBranch (-1))⁻¹) he
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one] at hh
  simp only [mul_inv_cancel_right] at hh
  have hm : ellipticReal=SpecialLinearGroup.mapGL ℝ A⁻¹*upperBranch 1*(upperBranch (-1))⁻¹ := by
    rw [← elliptic_branch, mul_assoc, mul_inv_cancel, mul_one]
  have hAE : SpecialLinearGroup.mapGL ℝ A*ellipticReal=upperBranch 1*(upperBranch (-1))⁻¹ := by
    rw [hm, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  change ((g ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A)-g) ∣[(k:ℤ)] ellipticReal=
    (g ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A)-g
  simp only [SmallLevelEleven.sub_slash, ← SlashAction.slash_mul]
  rw [hAE, hm]
  dsimp only [g]
  linear_combination hh

#print axioms actual_defect_elliptic

end SmallLevelThirtyTwo
