module

public import SmallLevelThirtyBBranchesV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirtyB

open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def E : GL (Fin 2) ℝ := matrix (6/Real.sqrt 6) (1/Real.sqrt 6)
    (-30/Real.sqrt 6) (-4/Real.sqrt 6) (by
  have hs : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_six_ne]
  nlinarith)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem B_A : B*A=1 := by
  have hs : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, B, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_six_ne] <;> nlinarith

theorem A_E : A*E=translation (2/6) := by
  have hs : (Real.sqrt 6)^2=6 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, E, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_six_ne] <;> nlinarith

theorem E_branch : E*translation (-(1/6))=A⁻¹*translation (1/6) := by
  apply mul_left_cancel (a:=A)
  rw [← mul_assoc, A_E, translation_mul]
  rw [← mul_assoc, mul_inv_cancel, one_mul]
  norm_num

theorem B_inverse : B=A⁻¹ := by
  have h := congrArg (fun x : GL (Fin 2) ℝ => x*A⁻¹) B_A
  simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using h

theorem defect_eigen (g : ℍ → ℂ) (k : ℤ) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hb : g ∣[k] B=g ∣[k] A⁻¹)
    (hp : ((g ∣[k] B) ∣[k] translation (1/6))+((g ∣[k] A) ∣[k] translation (-(1/6)))=
      δ • ((g ∣[k] translation (1/6))+(g ∣[k] translation (-(1/6))))) :
    ((g ∣[k] A)-δ • g) ∣[k] E=δ • ((g ∣[k] A)-δ • g) := by
  rw [hb] at hp
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[k] (translation (-(1/6)))⁻¹) hp
  rw [det_one_smul _ (det_one_inv _ (translation_det _))] at hh
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one, mul_inv_cancel_right] at hh
  have hm : E=A⁻¹*translation (1/6)*(translation (-(1/6)))⁻¹ := by
    rw [← E_branch, mul_assoc, mul_inv_cancel, mul_one]
  have hAE : A*E=translation (1/6)*(translation (-(1/6)))⁻¹ := by
    rw [hm, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rcases hδ with rfl | rfl
  · simp only [one_smul] at hh ⊢
    rw [SmallLevelEleven.sub_slash]
    simp only [← SlashAction.slash_mul]
    rw [hAE, hm]
    linear_combination -hh
  · simp only [neg_one_smul, sub_neg_eq_add] at hh ⊢
    rw [SlashAction.add_slash]
    simp only [← SlashAction.slash_mul]
    rw [hAE, hm]
    linear_combination hh

theorem actual_defect_square (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 (2*m) f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
      ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
        δ • SmallLevelOriginal.fourierFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] (E*E)=
      (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
        δ • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨δ,hδ,hp⟩ := original_pair hf
  have he := defect_eigen _ _ δ hδ (by rw [B_inverse]) hp
  refine ⟨δ,hδ,?_⟩
  rw [SlashAction.slash_mul, he, det_one_smul _ E_det, he, smul_smul]
  rcases hδ with rfl | rfl <;> simp

#print axioms B_inverse
#print axioms defect_eigen
#print axioms actual_defect_square

end SmallLevelThirtyB
