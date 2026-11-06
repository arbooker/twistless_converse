module

public import QuantitativeArithmeticSmallLevelThirteenDiagonalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

def axisP : GL (Fin 2) ℝ :=
  matrix ((13+Real.sqrt 13)/(2*Real.sqrt 13)) ((13-Real.sqrt 13)/39)
    (39/(2*Real.sqrt 13)) 1 (by
      have hs : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp
      ring)

def hyperX : GL (Fin 2) ℝ := matrix (23/3) (-16/9) (52/3) (-35/9) (by norm_num)
def hyperY : GL (Fin 2) ℝ := matrix (-1) (2/3) (-13/2) (10/3) (by norm_num)

theorem hyperX_product : hyperX=
    (SpecialLinearGroup.mapGL ℝ D₂*D₁)*(SpecialLinearGroup.mapGL ℝ D₂*D₁) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperX,D₂,D₁,B₃,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem hyperY_product : hyperY=
    SpecialLinearGroup.mapGL ℝ (-1:SL(2,ℤ))*D₃*D₁ := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hi : (SpecialLinearGroup.mapGL ℝ A)⁻¹=matrix (-4) 1 (-13) 3 (by norm_num) := by
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,matrix,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
        SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]
  rw [D₃,map_inv,hi]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperY,D₄,A,D₁,B₃,B₄,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem hyperX_axis : hyperX*axisP=axisP*diagScale scaleA scaleA_pos.ne' := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ha : 17+4*Real.sqrt 13≠0 := by positivity
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperX,axisP,diagScale,scaleA,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,ha] <;> nlinarith

theorem hyperY_axis : hyperY*axisP=axisP*diagScale scaleB scaleB_pos.ne' := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hb : 7-Real.sqrt 13≠0 := by have hh:=scaleB_pos; dsimp [scaleB] at hh; linarith
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperY,axisP,diagScale,scaleB,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn,hb] <;> nlinarith

private theorem D₁_det : (GeneralLinearGroup.det D₁:ℝ)=1 := by
  change (GeneralLinearGroup.det (fricke 13 (by decide)*B₃):ℝ)=1
  simp only [map_mul,Units.val_mul,fricke_det,matrix_det,B₃,one_mul]

/-- The original defect is invariant under both independent positive
hyperbolic transformations. -/
theorem original_hyperbolic (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    let g:=F-F ∣[((2*m:ℕ):ℤ)] A
    (g ∣[((2*m:ℕ):ℤ)] hyperX=g) ∧ (g ∣[((2*m:ℕ):ℤ)] hyperY=g) := by
  obtain ⟨χ,hχ,h1,h2,h3⟩ := original_defect_laws m hf
  let k : ℤ := ((2*m:ℕ):ℤ)
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let g:=F-F ∣[k] A
  change g ∣[k] D₁=χ • g at h1
  change g ∣[k] D₂= -g at h2
  change g ∣[k] D₃=χ • g at h3
  have hZ : g ∣[k] SpecialLinearGroup.mapGL ℝ (-1:SL(2,ℤ))=g :=
    SmallLevelThirtySix.slash_neg_one_even g m
  change (g ∣[k] hyperX=g) ∧ (g ∣[k] hyperY=g)
  constructor
  · rw [hyperX_product]
    simp only [SlashAction.slash_mul]
    change (((g ∣[k] D₂) ∣[k] D₁) ∣[k] D₂) ∣[k] D₁=g
    rw [h2,SlashAction.neg_slash,h1]
    rcases hχ with rfl|rfl <;>
      simp only [one_smul,neg_one_smul,neg_neg,SlashAction.neg_slash,h2,h1]
  · rw [hyperY_product,SlashAction.slash_mul,SlashAction.slash_mul,hZ,h3,
      det_one_smul _ D₁_det,h1,smul_smul]
    rcases hχ with rfl|rfl <;> simp

/-- Explicit common-axis classification of the defect coming from the
original Euler data. -/
theorem original_defect_classification (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f) :
    let F:=SmallLevelOriginal.fourierFunction (2*m) f
    let g:=F-F ∣[((2*m:ℕ):ℤ)] A
    ∃ C : ℂ, ∀ z : ℍ, (z:ℂ)^m*(g ∣[((2*m:ℕ):ℤ)] axisP) z=C := by
  obtain ⟨hx,hy⟩ := original_hyperbolic m hf
  apply diagonal_classification
  · exact (original_defect_holomorphic m hf).slash _ axisP
  · rw [← SlashAction.slash_mul,← hyperX_axis,SlashAction.slash_mul,hx]
  · rw [← SlashAction.slash_mul,← hyperY_axis,SlashAction.slash_mul,hy]

#print axioms original_hyperbolic
#print axioms original_defect_classification
end QuantitativeArithmeticSmallLevelThirteen
