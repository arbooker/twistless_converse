module

public import SmallLevelRamifiedTwoActionV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelFourteen

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelRamifiedTwo
open scoped MatrixGroups ModularForm

def kernel : Fin 6 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![55,-32;98,-57],by decide⟩
  | 2 => ⟨!![39,5;70,9],by decide⟩
  | 3 => ⟨!![1,0;-14,1],by decide⟩
  | 4 => ⟨!![9,-5;-70,39],by decide⟩
  | 5 => ⟨!![13,-7;28,-15],by decide⟩

theorem square_matrix : Q 14 8 (by decide)*Q 14 8 (by decide)=
    SpecialLinearGroup.mapGL ℝ (kernel 2) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, kernel, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem conjugate_T : SpecialLinearGroup.mapGL ℝ (kernel 1)*Q 14 8 (by decide)=
    Q 14 8 (by decide)*SpecialLinearGroup.mapGL ℝ ((-1)*T) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, kernel, ModularGroup.T, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem conjugate_U : SpecialLinearGroup.mapGL ℝ (kernel 5)*Q 14 8 (by decide)=
    Q 14 8 (by decide)*SpecialLinearGroup.mapGL ℝ ((-1)*(lower 14)⁻¹) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (-1)*(lower 14)⁻¹=(⟨!![-1,0;14,-1],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, kernel, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

/-- Every Schreier kernel matrix actually fixes every original even-weight
level-fourteen Fourier function. -/
theorem original_kernel (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 14 (2*m) f) (i : Fin 6) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  obtain ⟨δ,hδ,hQ⟩ := original_eigen (by decide : 0<14) (by decide : 2*8=14+2) (by decide) hf
  have hsq : F ∣[((2*m:ℕ):ℤ)] kernel 2=F := by
    have h := eigen_square 14 8 (by decide) F ((2*m:ℕ):ℤ) δ hδ hQ
    rw [square_matrix] at h
    exact h
  have hu : F ∣[((2*m:ℕ):ℤ)] (lower 14)⁻¹=F := by
    have h := congrArg (fun g : ℍ → ℂ => g ∣[((2*m:ℕ):ℤ)] (lower 14)⁻¹)
      (original_lower (by decide : 0<14) hf)
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm
  fin_cases i
  · exact original_T _ _
  · apply invariant_conjugate 14 8 (by decide) F _ δ hQ ((-1)*T) _ conjugate_T
    rw [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even]
    exact original_T _ _
  · exact hsq
  · change F ∣[((2*m:ℕ):ℤ)] kernel 3=F
    rw [show kernel 3=(lower 14)⁻¹ by decide]
    exact hu
  · have h := congrArg (fun g : ℍ → ℂ => g ∣[((2*m:ℕ):ℤ)] (kernel 2)⁻¹) hsq
    change F ∣[((2*m:ℕ):ℤ)] kernel 4=F
    rw [show kernel 4=(kernel 2)⁻¹ by decide]
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm
  · apply invariant_conjugate 14 8 (by decide) F _ δ hQ ((-1)*(lower 14)⁻¹) _ conjugate_U
    rw [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even]
    exact hu

#print axioms square_matrix
#print axioms conjugate_T
#print axioms conjugate_U
#print axioms original_kernel

end SmallLevelFourteen
