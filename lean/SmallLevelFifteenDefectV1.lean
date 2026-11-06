module

public import SmallLevelFifteenBranchesV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelFifteen

open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

def L : SL(2,ℤ) := ⟨!![-2,-1;15,7], by decide⟩

theorem L_relation : L=(-1)*(oddMatrix 15 8 (by decide))⁻¹*T := by decide

def E : GL (Fin 2) ℝ := matrix (6/Real.sqrt 3) (3/Real.sqrt 3)
    (-15/Real.sqrt 3) (-7/Real.sqrt 3) (by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_three_ne]
  nlinarith)

theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem B_A : B*A=SpecialLinearGroup.mapGL ℝ L := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, B, L, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem A_E : A*E=translation (2/3) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, E, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [sqrt_three_ne] <;> nlinarith

theorem E_branch : E*translation (-(1/3))=A⁻¹*translation (1/3) := by
  apply mul_left_cancel (a:=A)
  rw [← mul_assoc, A_E, translation_mul]
  rw [← mul_assoc, mul_inv_cancel, one_mul]
  norm_num

theorem actual_B_action (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 15 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] B=
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A⁻¹ := by
  let g := SmallLevelOriginal.fourierFunction (2*m) f
  have h2 := original_odd (by decide : 0<15) (by decide : 2*8=15+1) (by decide) hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] (oddMatrix 15 8 (by decide))⁻¹) h2
  simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hi
  have hL : g ∣[((2*m:ℕ):ℤ)] L=g := by
    dsimp only [g]
    rw [L_relation]
    simp only [SlashAction.slash_mul, SmallLevelThirtySix.slash_neg_one_even, ← hi,
      original_T]
  have hh : (g ∣[((2*m:ℕ):ℤ)] B) ∣[((2*m:ℕ):ℤ)] A=g := by
    rw [← SlashAction.slash_mul, B_A]
    exact hL
  have h := congrArg (fun F : ℍ → ℂ => F ∣[((2*m:ℕ):ℤ)] A⁻¹) hh
  simpa only [← SlashAction.slash_mul, mul_assoc, mul_inv_cancel, mul_one] using h

theorem defect_eigen (g : ℍ → ℂ) (k : ℤ) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hb : g ∣[k] B=g ∣[k] A⁻¹)
    (hp : ((g ∣[k] B) ∣[k] translation (1/3))+((g ∣[k] A) ∣[k] translation (-(1/3)))=
      δ • ((g ∣[k] translation (1/3))+(g ∣[k] translation (-(1/3))))) :
    ((g ∣[k] A)-δ • g) ∣[k] E=δ • ((g ∣[k] A)-δ • g) := by
  rw [hb] at hp
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[k] (translation (-(1/3)))⁻¹) hp
  rw [det_one_smul _ (det_one_inv _ (translation_det _))] at hh
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one, mul_inv_cancel_right] at hh
  have hm : E=A⁻¹*translation (1/3)*(translation (-(1/3)))⁻¹ := by
    rw [← E_branch, mul_assoc, mul_inv_cancel, mul_one]
  have hAE : A*E=translation (1/3)*(translation (-(1/3)))⁻¹ := by
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
    (hf : FinitenessOriginalInput.IsSolution 15 (2*m) f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
      ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
        δ • SmallLevelOriginal.fourierFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] (E*E)=
      (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)-
        δ • SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨δ,hδ,hp⟩ := original_pair hf
  have he := defect_eigen _ _ δ hδ (actual_B_action m hf) hp
  refine ⟨δ,hδ,?_⟩
  rw [SlashAction.slash_mul, he, det_one_smul _ E_det, he, smul_smul]
  rcases hδ with rfl | rfl <;> simp

#print axioms actual_B_action
#print axioms defect_eigen
#print axioms actual_defect_square

end SmallLevelFifteen
