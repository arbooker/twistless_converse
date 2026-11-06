module
public import QuantitativeArithmeticSmallLevelNineteenTwoMellinTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridGroupRowsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex Set MeasureTheory SmallLevelAdditive SmallLevelTaylor SmallLevelOriginal
open FinitenessPolynomialSeries FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

def exceptionalCenter (k : ℕ) (f : ℕ → ℂ) (j : ℕ) : ℂ → ℂ :=
  mellin (fun t : ℝ => fourier (fullCoefficients f k) (((j:ℝ)/114:ℝ)+(t:ℂ)*I))

/-- The actual entire row at grid coordinate4. -/
theorem original_exceptional_center4 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    (∀ s : ℂ, AnalyticAt ℂ (exceptionalCenter (2*m) f 4) s) ∧
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      exceptionalCenter (2*m) f 4 s=original (2*m) f ((4:ℝ)/114) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := invariant_matrix_fourier (2*m) f continuationMatrix10
    (original_continuation_matrix10 m hf)
  have he := QuantitativeArithmeticSmallLevelNineteenTwoMellin.matrix_center_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (28) (-1) (57) (-2) (by norm_num) (by norm_num)
    3249 (by norm_num) (by norm_num)
    (by simpa [continuationMatrix10] using hF)
  norm_num only [show (-(-2:ℝ)/57)=(4:ℝ)/114 by norm_num] at he
  norm_num [exceptionalCenter,original] at he ⊢
  exact he

/-- The actual entire row at grid coordinate54. -/
theorem original_exceptional_center54 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    (∀ s : ℂ, AnalyticAt ℂ (exceptionalCenter (2*m) f 54) s) ∧
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      exceptionalCenter (2*m) f 54 s=original (2*m) f ((54:ℝ)/114) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := invariant_matrix_fourier (2*m) f continuationMatrix9
    (original_continuation_matrix9 m hf)
  have he := QuantitativeArithmeticSmallLevelNineteenTwoMellin.matrix_center_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (21) (-10) (19) (-9) (by norm_num) (by norm_num)
    361 (by norm_num) (by norm_num)
    (by simpa [continuationMatrix9] using hF)
  norm_num only [show (-(-9:ℝ)/19)=(54:ℝ)/114 by norm_num] at he
  norm_num [exceptionalCenter,original] at he ⊢
  exact he

/-- The actual entire row at grid coordinate111. -/
theorem original_exceptional_center111 (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    (∀ s : ℂ, AnalyticAt ℂ (exceptionalCenter (2*m) f 111) s) ∧
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      exceptionalCenter (2*m) f 111 s=original (2*m) f ((111:ℝ)/114) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := invariant_matrix_fourier (2*m) f continuationMatrix1
    (original_continuation_matrix1 m hf)
  have he := QuantitativeArithmeticSmallLevelNineteenTwoMellin.matrix_center_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (1) (-1) (38) (-37) (by norm_num) (by norm_num)
    1444 (by norm_num) (by norm_num)
    (by simpa [continuationMatrix1] using hF)
  norm_num only [show (-(-37:ℝ)/38)=(111:ℝ)/114 by norm_num] at he
  norm_num [exceptionalCenter,original] at he ⊢
  exact he
#print axioms original_exceptional_center4
#print axioms original_exceptional_center54
#print axioms original_exceptional_center111
end QuantitativeArithmeticSmallLevelNineteen
