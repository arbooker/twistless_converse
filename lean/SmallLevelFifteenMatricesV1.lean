module

public import SmallLevelFifteenRigidityV1
public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelFifteen

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

def kernel : Fin 7 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![14,-3;75,-16],by decide⟩
  | 2 => ⟨!![8,3;45,17],by decide⟩
  | 3 => ⟨!![1,0;-15,1],by decide⟩
  | 4 => ⟨!![17,-3;-45,8],by decide⟩
  | 5 => ⟨!![29,-5;180,-31],by decide⟩

  | 6 => ⟨!![8,1;15,2],by decide⟩

theorem square_matrix : A*A=
    SpecialLinearGroup.mapGL ℝ (kernel 2) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, matrix, kernel, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem conjugate_T : SpecialLinearGroup.mapGL ℝ (kernel 1)*A=
    A*SpecialLinearGroup.mapGL ℝ ((-1)*T) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, matrix, kernel, ModularGroup.T, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem conjugate_U : SpecialLinearGroup.mapGL ℝ (kernel 5)*A=
    A*SpecialLinearGroup.mapGL ℝ ((-1)*(lower 15)⁻¹) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hi : (-1)*(lower 15)⁻¹=(⟨!![-1,0;15,-1],by decide⟩ : SL(2,ℤ)) := by decide
  rw [hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, matrix, kernel, GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem eigen_square (F : ℍ → ℂ) (k : ℤ) (δ : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hA : F ∣[k] A=δ • F) :
    F ∣[k] (A*A)=F := by
  rw [SlashAction.slash_mul, hA, det_one_smul _ A_det, hA, smul_smul]
  rcases hδ with rfl | rfl <;> simp

theorem invariant_conjugate (F : ℍ → ℂ) (k : ℤ) (δ : ℂ)
    (hA : F ∣[k] A=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*A=A*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] A=F ∣[k] A := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] A=F ∣[k] A
    rw [← SlashAction.slash_mul, hκ, SlashAction.slash_mul]
    change (F ∣[k] A) ∣[k] γ=F ∣[k] A
    rw [hA, ModularForm.SL_smul_slash, hγ]
  have h := congrArg (fun g : ℍ → ℂ => g ∣[k] A⁻¹) hh
  simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h

/-- Every Schreier kernel matrix actually fixes every original even-weight
level-fifteen Fourier function. -/
theorem original_kernel (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 15 (2*m) f) (i : Fin 7) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  obtain ⟨δ,hδ,hQ⟩ := original_A m hm hf
  have hsq : F ∣[((2*m:ℕ):ℤ)] kernel 2=F := by
    have h := eigen_square F ((2*m:ℕ):ℤ) δ hδ hQ
    rw [square_matrix] at h
    exact h
  have hu : F ∣[((2*m:ℕ):ℤ)] (lower 15)⁻¹=F := by
    have h := congrArg (fun g : ℍ → ℂ => g ∣[((2*m:ℕ):ℤ)] (lower 15)⁻¹)
      (original_lower (by decide : 0<15) hf)
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm
  fin_cases i
  · exact original_T _ _
  · apply invariant_conjugate F _ δ hQ ((-1)*T) _ conjugate_T
    rw [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even]
    exact original_T _ _
  · exact hsq
  · change F ∣[((2*m:ℕ):ℤ)] kernel 3=F
    rw [show kernel 3=(lower 15)⁻¹ by decide]
    exact hu
  · have h := congrArg (fun g : ℍ → ℂ => g ∣[((2*m:ℕ):ℤ)] (kernel 2)⁻¹) hsq
    change F ∣[((2*m:ℕ):ℤ)] kernel 4=F
    rw [show kernel 4=(kernel 2)⁻¹ by decide]
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using h.symm
  · apply invariant_conjugate F _ δ hQ ((-1)*(lower 15)⁻¹) _ conjugate_U
    rw [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even]
    exact hu

  · exact original_odd (by decide : 0<15) (by decide : 2*8=15+1) (by decide) hf

#print axioms square_matrix
#print axioms conjugate_T
#print axioms conjugate_U
#print axioms original_kernel

end SmallLevelFifteen
