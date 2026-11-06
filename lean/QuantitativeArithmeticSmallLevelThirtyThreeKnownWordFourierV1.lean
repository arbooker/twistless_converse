module

public import QuantitativeArithmeticSmallLevelThirtyThreeKnownWordsV1
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

def coordA (w : Word) : ℝ := (value w).val 0 0
def coordB (w : Word) : ℝ := (value w).val 0 1
def coordC (w : Word) : ℝ := (value w).val 1 0
def coordD (w : Word) : ℝ := (value w).val 1 1

theorem coordinate_det (w : Word) : coordA w*coordD w-coordB w*coordC w=1 := by
  have h := value_det w
  change (value w).val.det=1 at h
  simpa only [Matrix.det_fin_two,coordA,coordB,coordC,coordD] using h

theorem word_fourier_of_slash (m : ℕ) (f : ℕ → ℂ) (χ δ : ℂ)
    (hχ : χ=1 ∨ χ= -1) (hδ : δ=1 ∨ δ= -1) (w : Word)
    (hw : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w=
      character χ δ w • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      character χ δ w/(((coordC w:ℂ)*z+(coordD w:ℂ))^(2*m))*
        fourier (fullCoefficients f (2*m))
          (((coordA w:ℂ)*z+(coordB w:ℂ))/((coordC w:ℂ)*z+(coordD w:ℂ))) := by
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      character χ δ w • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] value w) := by
    rcases character_sign hχ hδ w with hc|hc
    · simpa only [hc,one_smul] using hw.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hw.symm
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (value_det w),zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [value_det]; norm_num)] at h
  simpa only [num,denom,coordA,coordB,coordC,coordD,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using h

/-- Actual all-order Fourier/Taylor laws for every word used in the complete
row construction. The hypotheses on C and the source only exclude an affine
row or a source sent to infinity, which are treated separately. -/
theorem original_word_taylor {m : ℕ} (hm : 0 < m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ w : Word, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            character χ (FinitenessNormalizedTwistProduct.root 33 f 3) w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨χ,hχ,hwords⟩ := original_words hm hf
  refine ⟨χ,hχ,?_⟩
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := word_fourier_of_slash m f χ (FinitenessNormalizedTwistProduct.root 33 f 3) hχ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) w (hwords w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (character χ (FinitenessNormalizedTwistProduct.root 33 f 3) w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh

#print axioms coordinate_det
#print axioms word_fourier_of_slash
#print axioms original_word_taylor
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
