module

public import SmallLevelThirtyPairsV1
public import SmallLevelNormalizedEvenFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- The actual modulus-3 normalized two-branch relation. -/
theorem original_pair_3 {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 13 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 13 (by decide))⁻¹*translation (1/3)*fricke 117 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 13 (by decide))⁻¹*translation (-(1/3))*fricke 117 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/3))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/3))) := by
  obtain ⟨ε,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws
    (by decide : 0<13) hf
  have hr : FinitenessNormalizedTwistProduct.root 13 f 3=1 := by
    unfold FinitenessNormalizedTwistProduct.root
    rw [(by decide : Nat.Prime 3).primeFactors]
    simp [FinitenessNormalizedTwistLocal.sign,show ¬3∣(13:ℕ) by decide]
  have h := pair_of_fricke 13 117 k (by decide) (by decide) (1/3)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) 1 (Or.inl rfl)
  simp only [one_smul] at h
  apply h
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have hh := hlaw 3 (by decide) z hz
    rw [show Nat.lcm 13 (3^2)=117 by decide, hr, one_mul,
      SmallLevelThree.twist_three _ (periodic _), SmallLevelThree.twist_three _ (periodic _)] at hh
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,one_mul] using hh

/-- The actual modulus-4 normalized two-branch relation. -/
theorem original_pair_4 {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 13 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 13 (by decide))⁻¹*translation (1/4)*fricke 208 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 13 (by decide))⁻¹*translation (-(1/4))*fricke 208 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4))) := by
  obtain ⟨ε,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws
    (by decide : 0<13) hf
  have hr : FinitenessNormalizedTwistProduct.root 13 f 4=1 := by
    unfold FinitenessNormalizedTwistProduct.root
    rw [show (4:ℕ).primeFactors={2} by
      simpa using Nat.primeFactors_prime_pow (by decide : (2:ℕ)≠0) Nat.prime_two]
    simp [FinitenessNormalizedTwistLocal.sign,show ¬2∣(13:ℕ) by decide]
  have h := pair_of_fricke 13 208 k (by decide) (by decide) (1/4)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) 1 (Or.inl rfl)
  simp only [one_smul] at h
  apply h
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have hh := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 13 (4^2)=208 by decide, hr, one_mul,
      SmallLevelThirty.twist_four _ (periodic _), SmallLevelThirty.twist_four _ (periodic _)] at hh
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,one_mul] using hh

def A : SL(2,ℤ) := ⟨!![3,-1;13,-4],by decide⟩
def G₂ : SL(2,ℤ) := ⟨!![2,-1;13,-6],by decide⟩
def D₂ : SL(2,ℤ) := ⟨!![5,-2;13,-5],by decide⟩
def A₄ : SL(2,ℤ) := ⟨!![4,-1;13,-3],by decide⟩

def B₃ : GL (Fin 2) ℝ := matrix 3 (-1) (-13) (14/3) (by norm_num)
def B₄ : GL (Fin 2) ℝ := matrix 4 (-1) (-13) (7/2) (by norm_num)
def D₁ : GL (Fin 2) ℝ := fricke 13 (by decide)*B₃
def D₄ : GL (Fin 2) ℝ := fricke 13 (by decide)*B₄
def D₃ : GL (Fin 2) ℝ :=
  SpecialLinearGroup.mapGL ℝ A⁻¹*D₄*SpecialLinearGroup.mapGL ℝ A

private theorem sqrt_117 : Real.sqrt 117=3*Real.sqrt 13 := by
  rw [show (117:ℝ)=9*13 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

private theorem branches_3 :
    fricke 13 (by decide)*B₃*translation (1/3)=
      translation (1/3)*fricke 117 (by decide) ∧
    fricke 13 (by decide)*SpecialLinearGroup.mapGL ℝ A*translation (1/3)=
      translation (-(1/3))*fricke 117 (by decide) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  constructor <;> apply Units.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fricke,matrix,B₃,A,translation,sqrt_117,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

/-- Original-input row after translation, with determinant-one matrices. -/
theorem original_row_3 {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 13 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B₃)+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A)=
    SmallLevelOriginal.fourierFunction k f+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-2/3)) := by
  have hp : (fricke 13 (by decide))⁻¹*translation (1/3)*fricke 117 (by decide)=
      B₃*translation (1/3) := by
    rw [mul_assoc,← branches_3.1]
    group
  have hn : (fricke 13 (by decide))⁻¹*translation (-(1/3))*fricke 117 (by decide)=
      SpecialLinearGroup.mapGL ℝ A*translation (1/3) := by
    rw [mul_assoc,← branches_3.2]
    group
  have hh := original_pair_3 hf
  rw [hp,hn] at hh
  have h := congrArg (fun G : ℍ → ℂ => G ∣[(k:ℤ)] (translation (1/3))⁻¹) hh
  simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_assoc,
    mul_inv_cancel,mul_one,SlashAction.slash_one] at h
  have ht : translation (-(1/3))*(translation (1/3))⁻¹=translation (-2/3) := by
    apply (mul_right_cancel (b:=translation (1/3)))
    rw [mul_assoc,inv_mul_cancel,mul_one,translation_mul]
    congr 1
    ring
  rw [ht] at h
  exact h

private theorem sqrt_208 : Real.sqrt 208=4*Real.sqrt 13 := by
  rw [show (208:ℝ)=16*13 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

private theorem branches_4 :
    fricke 13 (by decide)*B₄*translation (1/4)=
      translation (1/4)*fricke 208 (by decide) ∧
    fricke 13 (by decide)*SpecialLinearGroup.mapGL ℝ A₄*translation (1/4)=
      translation (-(1/4))*fricke 208 (by decide) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  constructor <;> apply Units.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [fricke,matrix,B₄,A₄,translation,sqrt_208,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

/-- Original-input row after translation, with determinant-one matrices. -/
theorem original_row_4 {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 13 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B₄)+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A₄)=
    SmallLevelOriginal.fourierFunction k f+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-2/4)) := by
  have hp : (fricke 13 (by decide))⁻¹*translation (1/4)*fricke 208 (by decide)=
      B₄*translation (1/4) := by
    rw [mul_assoc,← branches_4.1]
    group
  have hn : (fricke 13 (by decide))⁻¹*translation (-(1/4))*fricke 208 (by decide)=
      SpecialLinearGroup.mapGL ℝ A₄*translation (1/4) := by
    rw [mul_assoc,← branches_4.2]
    group
  have hh := original_pair_4 hf
  rw [hp,hn] at hh
  have h := congrArg (fun G : ℍ → ℂ => G ∣[(k:ℤ)] (translation (1/4))⁻¹) hh
  simp only [SlashAction.add_slash,← SlashAction.slash_mul,mul_assoc,
    mul_inv_cancel,mul_one,SlashAction.slash_one] at h
  have ht : translation (-(1/4))*(translation (1/4))⁻¹=translation (-2/4) := by
    apply (mul_right_cancel (b:=translation (1/4)))
    rw [mul_assoc,inv_mul_cancel,mul_one,translation_mul]
    congr 1
    ring
  rw [ht] at h
  exact h

#print axioms original_row_3
#print axioms original_row_4
end QuantitativeArithmeticSmallLevelThirteen
