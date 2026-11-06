module
public import QuantitativeArithmeticSmallLevelThirtyThreeRatesV1
public import QuantitativeArithmeticSmallLevelThirtyThreeParametersV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates
theorem matrixScalar_leading (m : ℕ) (f : ℕ→ℂ) (η s : ℂ) (i : Fin 588) :
    gridMatrixScalar m f η i 0 s=
      character η (-badParameter f 3) (sourceWord (groupSource i))*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 11 m s) := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one,root_three]
  rw [groupRate_complex]
  rfl

theorem taylorScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 72) :
    gridTaylorCoefficient m f ε i 0 s=
      (FinitenessNormalizedTwistProduct.root 33 f (gridTaylorQ i))*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 11 m s) := by
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  have hb : (((gridTaylorL i:ℝ)*((gridTaylorT i:ℝ)/66)^2:ℝ):ℂ)=(taylorRate i:ℂ) := by
    simp [taylorRate]
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Ring.choose_zero_right,mul_one,hm]
  rw [hb,taylorRate_complex]
  unfold phase parameter
  ring


#print axioms matrixScalar_leading
#print axioms taylorScalar_leading
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
