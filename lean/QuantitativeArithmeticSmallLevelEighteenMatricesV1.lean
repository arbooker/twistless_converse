module

public import QuantitativeArithmeticSmallLevelEighteenAlgebraV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelEighteen
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelRamifiedTwo
open scoped MatrixGroups ModularForm

def kernel : Fin 10 → SL(2,ℤ)
  | 0 => T
  | 1 => lower 18
  | 2 => C
  | 3 => ⟨!![59,6;108,11],by decide⟩
  | 4 => ⟨!![-89,50;-162,91],by decide⟩
  | 5 => ⟨!![19,-9;36,-17],by decide⟩
  | 6 => ⟨!![5,-3;-18,11],by decide⟩
  | 7 => ⟨!![91,9;-900,-89],by decide⟩
  | 8 => ⟨!![11,-6;-108,59],by decide⟩
  | 9 => ⟨!![-17,-2;162,19],by decide⟩

private theorem square_matrix : Q₂*Q₂=SpecialLinearGroup.mapGL ℝ (kernel 3) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q₂,Q,kernel,GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

private theorem conjugate_Q (i : Fin 2) :
    SpecialLinearGroup.mapGL ℝ (kernel (if i=0 then 4 else 5))*Q₂=
      Q₂*SpecialLinearGroup.mapGL ℝ (kernel (if i=0 then 0 else 1)) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [Q₂,Q,kernel,lower,ModularGroup.T,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

private theorem conjugate_H (i : Fin 4) :
    SpecialLinearGroup.mapGL ℝ (kernel (match i with | 0=>6 | 1=>7 | 2=>8 | 3=>9))*fricke 18 (by decide)=
      fricke 18 (by decide)*SpecialLinearGroup.mapGL ℝ
        (kernel (match i with | 0=>2 | 1=>4 | 2=>3 | 3=>5)) := by
  have hs : (Real.sqrt 18)^2=18 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 18≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,kernel,C,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

private theorem conjugate_invariant (F : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ)
    (δ : ℂ) (hg : F ∣[k] g=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*g=g*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] g=F ∣[k] g := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] g=F ∣[k] g
    rw [← SlashAction.slash_mul,hκ,SlashAction.slash_mul]
    change (F ∣[k] g) ∣[k] γ=F ∣[k] g
    rw [hg,ModularForm.SL_smul_slash,hγ]
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] g⁻¹) hh
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

theorem original_kernel (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 18 (2*m) f) (i : Fin 10) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  obtain ⟨δ,hδ,hQ⟩ := original_eigen (by decide : 0<18)
    (by decide : 2*10=18+2) (by decide) hf
  obtain ⟨χ,_,hH⟩ := original_fricke_sign (by decide : 0<18) m hf
  have h0 : F ∣[k] kernel 0=F := original_T _ _
  have h1 : F ∣[k] kernel 1=F := original_lower (by decide) hf
  have h2 : F ∣[k] kernel 2=F := original_C m hf
  have h3 : F ∣[k] kernel 3=F := by
    have h := eigen_square 18 10 (by decide) F k δ hδ hQ
    rw [square_matrix] at h
    exact h
  have h4 : F ∣[k] kernel 4=F :=
    conjugate_invariant F k Q₂ δ hQ _ _ (conjugate_Q 0) h0
  have h5 : F ∣[k] kernel 5=F :=
    conjugate_invariant F k Q₂ δ hQ _ _ (conjugate_Q 1) h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact conjugate_invariant F k _ χ hH _ _ (conjugate_H 0) h2
  · exact conjugate_invariant F k _ χ hH _ _ (conjugate_H 1) h4
  · exact conjugate_invariant F k _ χ hH _ _ (conjugate_H 2) h3
  · exact conjugate_invariant F k _ χ hH _ _ (conjugate_H 3) h5

#print axioms original_kernel
end QuantitativeArithmeticSmallLevelEighteen
