module

public import QuantitativeArithmeticSmallLevelThirteenPairsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open FinitenessOriginalInput
open scoped MatrixGroups ModularForm Manifold

private theorem sub_slash (g h : ℍ → ℂ) (k : ℤ) (M : GL (Fin 2) ℝ) :
    (g-h) ∣[k] M=(g ∣[k] M)-(h ∣[k] M) := by
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash]

private theorem A_D₁ : SpecialLinearGroup.mapGL ℝ A*D₁=
    fricke 13 (by decide)*translation (-2/3) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D₁,B₃,A,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem A₄_D₄ : SpecialLinearGroup.mapGL ℝ A₄*D₄=
    fricke 13 (by decide)*translation (-2/4) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D₄,B₄,A₄,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem row_defect (k : ℤ) (F : ℍ → ℂ) (χ : ℂ)
    (hH : F ∣[k] fricke 13 (by decide)=χ • F)
    (A : SL(2,ℤ)) (B D : GL (Fin 2) ℝ) (r : ℝ)
    (hB : (GeneralLinearGroup.det B:ℝ)=1)
    (hD : D=fricke 13 (by decide)*B)
    (hAD : SpecialLinearGroup.mapGL ℝ A*D=fricke 13 (by decide)*translation r)
    (hrow : (F ∣[k] B)+(F ∣[k] A)=F+(F ∣[k] translation r)) :
    (F-(F ∣[k] A)) ∣[k] D=χ • (F-(F ∣[k] A)) := by
  rw [sub_slash]
  change (F ∣[k] D)-((F ∣[k] SpecialLinearGroup.mapGL ℝ A) ∣[k] D)=_
  rw [← SlashAction.slash_mul,hAD,hD,SlashAction.slash_mul,SlashAction.slash_mul,
    hH,det_one_smul _ hB,det_one_smul _ (translation_det _),← smul_sub]
  congr 1
  linear_combination hrow

theorem original_G₂ {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 13 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] G₂=
      SmallLevelOriginal.fourierFunction k f := by
  have hM := original_odd (by decide : 0<13) (by decide : 2*7=13+1) (by decide) hf
  have hi := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)]
    (oddMatrix 13 7 (by decide))⁻¹) hM
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hi
  rw [show G₂=lower 13*(oddMatrix 13 7 (by decide))⁻¹ by decide,
    SlashAction.slash_mul, original_lower (by decide) hf]
  exact hi.symm

private theorem defect_D₂ (m : ℕ) (F : ℍ → ℂ)
    (hG : F ∣[((2*m:ℕ):ℤ)] G₂=F) :
    (F-(F ∣[((2*m:ℕ):ℤ)] A)) ∣[((2*m:ℕ):ℤ)] D₂=
      -(F-(F ∣[((2*m:ℕ):ℤ)] A)) := by
  have hi := congrArg (fun G : ℍ → ℂ => G ∣[((2*m:ℕ):ℤ)] G₂⁻¹) hG
  simp only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hi
  have hd : F ∣[((2*m:ℕ):ℤ)] D₂=F ∣[((2*m:ℕ):ℤ)] A := by
    rw [show D₂=(-1)*G₂⁻¹*A by decide,SlashAction.slash_mul,
      SlashAction.slash_mul,SmallLevelThirtySix.slash_neg_one_even,← hi]
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,
    ← SlashAction.slash_mul]
  rw [show A*D₂=G₂ by decide,hd,hG]
  abel

/-- All three CFOS defect eigenlaws hold for the literal original input,
with one common Fricke sign and without restricting the Hecke eigenvalues. -/
theorem original_defect_laws (m : ℕ) {f : ℕ → ℂ}
    (hf : IsSolution 13 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      let F := SmallLevelOriginal.fourierFunction (2*m) f
      let g := F-(F ∣[((2*m:ℕ):ℤ)] A)
      (g ∣[((2*m:ℕ):ℤ)] D₁=χ • g) ∧
      (g ∣[((2*m:ℕ):ℤ)] D₂= -g) ∧
      (g ∣[((2*m:ℕ):ℤ)] D₃=χ • g) := by
  obtain ⟨χ,hχ,hH⟩ := original_fricke_sign (by decide : 0<13) m hf
  refine ⟨χ,hχ,?_⟩
  let k : ℤ := ((2*m:ℕ):ℤ)
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let g := F-(F ∣[k] A)
  have h1 : g ∣[k] D₁=χ • g :=
    row_defect k F χ hH A B₃ D₁ (-2/3) (matrix_det _ _ _ _ _) rfl A_D₁
      (original_row_3 hf)
  have h4 : (F-(F ∣[k] A₄)) ∣[k] D₄=χ • (F-(F ∣[k] A₄)) :=
    row_defect k F χ hH A₄ B₄ D₄ (-2/4) (matrix_det _ _ _ _ _) rfl A₄_D₄
      (original_row_4 hf)
  refine ⟨h1,defect_D₂ m F (original_G₂ hf),?_⟩
  have hi : g ∣[k] A⁻¹= -(F-(F ∣[k] A₄)) := by
    dsimp only [g]
    rw [show A₄=(-1)*A⁻¹ by decide,SlashAction.slash_mul,
      SmallLevelThirtySix.slash_neg_one_even]
    simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,
      ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one]
    abel
  have hh : (g ∣[k] A⁻¹) ∣[k] D₄=χ • (g ∣[k] A⁻¹) := by
    rw [hi,SlashAction.neg_slash,h4,smul_neg]
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] A) hh
  rw [ModularForm.SL_smul_slash,← SlashAction.slash_mul,inv_mul_cancel,
    SlashAction.slash_one] at h
  change (g ∣[k] D₃)=χ • g
  rw [D₃,SlashAction.slash_mul,SlashAction.slash_mul]
  exact h

theorem original_defect_holomorphic (m : ℕ) {f : ℕ → ℂ}
    (hf : IsSolution 13 (2*m) f) :
    MDiff (SmallLevelOriginal.fourierFunction (2*m) f-
      (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A)) := by
  have h := SmallLevelOriginal.fourierFunction_holomorphic hf
  exact h.sub (h.slash ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ A))

/-- The defect has zero cyclic sum, because the missing generator has order three. -/
theorem defect_cyclic (k : ℤ) (F : ℍ → ℂ) :
    let g := F-(F ∣[k] A)
    g+(g ∣[k] A)+(g ∣[k] (A*A))=0 := by
  have hA : A*(A*A)=1 := by decide
  dsimp
  simp only [sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,
    ← SlashAction.slash_mul,hA,SlashAction.slash_one]
  abel

#print axioms original_G₂
#print axioms original_defect_laws
#print axioms original_defect_holomorphic
#print axioms defect_cyclic
end QuantitativeArithmeticSmallLevelThirteen
