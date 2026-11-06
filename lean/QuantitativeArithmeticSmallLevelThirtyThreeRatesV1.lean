module
public import QuantitativeArithmeticSmallLevelThirtyThreeRatesDataV1
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open SmallLevelPrimeRates

theorem groupRate_factor (i : Fin 588) :
    groupRate i=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*(11:ℚ)^(groupPowers i).2.2 := by
  fin_cases i <;> decide +kernel

theorem groupRate_complex (i : Fin 588) (h : ℂ) :
    (groupRate i:ℂ)^h=monomial (groupPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((11:ℂ)^h) :=
  rational_power 2 3 11 (by decide) (by decide) (by decide) _ _ (groupRate_factor i) h

theorem taylorRate_factor (i : Fin 72) :
    taylorRate i=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*(11:ℚ)^(taylorPowers i).2.2 := by
  fin_cases i <;> decide +kernel

theorem taylorRate_complex (i : Fin 72) (h : ℂ) :
    (taylorRate i:ℂ)^h=monomial (taylorPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((11:ℂ)^h) :=
  rational_power 2 3 11 (by decide) (by decide) (by decide) _ _ (taylorRate_factor i) h

#print axioms groupRate_complex
#print axioms taylorRate_complex
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
