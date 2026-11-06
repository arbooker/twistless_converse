module

public import SmallLevelThreeSlashV1
public import SmallLevelSixPairV1
public import SmallLevelElevenDefectV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelNineteen

open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelThree
open scoped MatrixGroups ModularForm

def A : SL(2,ℤ) := ⟨!![4,-1;-19,5], by decide⟩
def B : SL(2,ℤ) := ⟨!![5,-1;-19,4], by decide⟩

theorem A_inv : A⁻¹ = (⟨!![5,1;19,4], by decide⟩ : SL(2,ℤ)) := by decide
theorem B_inv : B⁻¹ = (⟨!![4,1;19,5], by decide⟩ : SL(2,ℤ)) := by decide

theorem root_four (f : ℕ → ℂ) : FinitenessNormalizedTwistProduct.root 19 f 4 = 1 := by
  have hp : Nat.primeFactors 4 = {2} := by
    rw [show (4:ℕ)=2*2 by norm_num, Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  simp [FinitenessNormalizedTwistProduct.root, hp, FinitenessNormalizedTwistLocal.sign]

theorem original_four_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 19 (by decide))⁻¹*translation (1/4)*fricke 304 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 19 (by decide))⁻¹*translation (-(1/4))*fricke 304 (by decide)))=
    FinitenessNormalizedTwistProduct.root 19 f 4 •
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<19) hf
  apply pair_of_fricke 19 304 k (by decide) (by decide) (1/4)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 19 (4^2)=304 by decide,
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _),
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

theorem sqrt_conductor_four : Real.sqrt 304 = 4 * Real.sqrt 19 := by
  rw [show (304:ℝ)=16*19 by norm_num, Real.sqrt_mul (by norm_num)]
  norm_num

theorem four_positive : fricke 19 (by decide) * SpecialLinearGroup.mapGL ℝ A *
    translation (1/4) = translation (1/4) * fricke 304 (by decide) := by
  have ht : (Real.sqrt 19)^2=19 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 19≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, A, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_four] <;>
    field_simp [hn] <;> norm_num [ht]

theorem four_negative : fricke 19 (by decide) * SpecialLinearGroup.mapGL ℝ B⁻¹ *
    translation (-(1/4)) = translation (-(1/4)) * fricke 304 (by decide) := by
  rw [B_inv]
  have ht : (Real.sqrt 19)^2=19 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 19≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke, translation, matrix, GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL, SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, sqrt_conductor_four] <;>
    field_simp [hn] <;> norm_num [ht]

theorem original_four_reduced {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] A) +
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] B⁻¹) ∣[(k:ℤ)] translation (-1/2)) =
    SmallLevelOriginal.fourierFunction k f +
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/2)) := by
  have h := original_four_pair hf
  have hp : (fricke 19 (by decide))⁻¹ * translation (1/4) * fricke 304 (by decide) =
      SpecialLinearGroup.mapGL ℝ A * translation (1/4) := by
    rw [mul_assoc, ← four_positive]
    group
  have hn : (fricke 19 (by decide))⁻¹ * translation (-(1/4)) * fricke 304 (by decide) =
      SpecialLinearGroup.mapGL ℝ B⁻¹ * translation (-(1/4)) := by
    rw [mul_assoc, ← four_negative]
    group
  rw [hp, hn, root_four, one_smul] at h
  have hh := congrArg (fun F : ℍ → ℂ => F ∣[(k:ℤ)] translation (-(1/4))) h
  simp only [SlashAction.add_slash, ← SlashAction.slash_mul, mul_assoc, translation_mul] at hh
  norm_num only [show (1/4:ℝ)+ -(1/4)=0 by ring,
    show (-(1/4):ℝ)+ -(1/4)= -1/2 by ring] at hh
  have ht : translation 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation, matrix, GeneralLinearGroup.mkOfDetNeZero]
  change (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ A) +
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] SpecialLinearGroup.mapGL ℝ B⁻¹) ∣[(k:ℤ)] translation (-1/2)) = _
  simpa only [ht, mul_one, SlashAction.slash_one, SlashAction.slash_mul, neg_div] using hh


#print axioms original_four_reduced
end QuantitativeArithmeticSmallLevelNineteen
