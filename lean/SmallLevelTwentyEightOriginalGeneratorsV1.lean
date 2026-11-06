module
public import SmallLevelEvenHalfTranslationV1
public import SmallLevelSixRootsV1
public import SmallLevelNormalizedEvenFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGenerators
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelSixEigen
open scoped MatrixGroups ModularForm

def W : GL (Fin 2) ℝ := fricke 28 (by decide)
def U : GL (Fin 2) ℝ := matrix 1 0 14 1 (by norm_num)
def Ui : GL (Fin 2) ℝ := matrix 1 0 (-14) 1 (by norm_num)
def E : GL (Fin 2) ℝ := matrix 1 (-1/2) (-14) 8 (by norm_num)

theorem U_det : (GeneralLinearGroup.det U:ℝ)=1 := matrix_det _ _ _ _ _
theorem Ui_det : (GeneralLinearGroup.det Ui:ℝ)=1 := matrix_det _ _ _ _ _
theorem E_det : (GeneralLinearGroup.det E:ℝ)=1 := matrix_det _ _ _ _ _

theorem Ui_inverse : Ui=U⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ui,U,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

theorem U_conjugate : U=W*translation (-1/2)*W⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  have hs : (Real.sqrt 28)^2=28 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 28≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [U,W,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem E_factor : E=Ui*translation (-1/2) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,Ui,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem half_inverse : translation (-1/2)=(translation (1/2))⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  rw [translation_mul]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]

/-- All non-Fricke base transformations used in the 84-grid follow from
original input; the known map has eigenvalue +1. -/
theorem original_generators (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] U=
      -SmallLevelOriginal.fourierFunction (2*m) f ∧
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] E=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k:ℤ:=((2*m:ℕ):ℤ)
  change F ∣[k] W=η • F at hW
  have hWdet : (GeneralLinearGroup.det W:ℝ)=1 := fricke_det 28 (by decide)
  have hhalf : F ∣[k] translation (1/2)=(-1:ℂ) • F := by
    simpa only [neg_one_smul] using SmallLevelEvenScale.original_half_translation (L:=7) hf.toEulerData (2*m)
  have hminus : F ∣[k] translation (-1/2)=(-1:ℂ) • F := by
    rw [half_inverse]
    exact eigen_inverse F k _ (translation_det _) (-1) (Or.inr rfl) hhalf
  have hWi : F ∣[k] W⁻¹=η • F :=
    eigen_inverse F k W hWdet η hη hW
  have hU : F ∣[k] U=(-1:ℂ) • F := by
    rw [U_conjugate,SlashAction.slash_mul,SlashAction.slash_mul,hW,
      det_one_smul _ (translation_det _),hminus,
      det_one_smul (W⁻¹) (det_one_inv W hWdet),
      det_one_smul (W⁻¹) (det_one_inv W hWdet),hWi]
    rcases hη with rfl|rfl <;> simp
  have hUi : F ∣[k] Ui=(-1:ℂ) • F := by
    rw [Ui_inverse]
    exact eigen_inverse F k _ U_det (-1) (Or.inr rfl) hU
  refine ⟨by simpa only [neg_one_smul] using hU,?_⟩
  change F ∣[k] E=F
  rw [E_factor,SlashAction.slash_mul,hUi,det_one_smul _ (translation_det _),hminus]
  simp

#print axioms U_conjugate
#print axioms original_generators
end SmallLevelTwentyEightGenerators
