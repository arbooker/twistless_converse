module
public import SmallLevelFourPrimeRatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixContinuationRates
open Complex SmallLevelFourPrimeRates SmallLevelPrimeRates

def powers : Fin 27→ℤ×ℤ×ℤ×ℤ :=
  ![(0,0,0,0),(0,0,1,0),(0,2,0,0),(0,2,1,0),(0,3,0,0),(0,3,1,0),(0,4,0,0),(0,5,0,0),(0,6,0,0),(1,0,0,0),(1,0,1,0),(1,1,0,0),(1,1,1,0),(1,2,0,0),(1,2,1,0),(1,3,0,0),(1,4,0,0),(1,5,0,0),(1,6,0,0),(2,0,0,0),(2,2,0,0),(2,3,0,0),(2,4,0,0),(3,0,0,0),(3,3,0,0),(3,4,0,0),(5,0,0,0)]

def rates : Fin 27→ℚ :=
  ![1,13,9,117,27,351,81,243,729,2,26,6,78,18,234,54,162,486,1458,4,36,108,324,8,216,648,32]

theorem rates_injective : Function.Injective rates := by decide

theorem rates_factor (i : Fin 27) :
    rates i=(2:ℚ)^(powers i).1*(3:ℚ)^(powers i).2.1*
      (13:ℚ)^(powers i).2.2.1*(5:ℚ)^(powers i).2.2.2 := by
  fin_cases i <;> norm_num [rates,powers]

theorem sum_curve (c : Fin 27→ℂ) (m : ℕ) (s : ℂ) :
    (∑ i,c i*(rates i:ℂ)^(s-(m:ℂ)))=
      ∑ i,c i*SmallLevelFourPrimeRates.monomial (powers i)
        (parameter 2 m s) (parameter 3 m s) (parameter 13 m s) (parameter 5 m s) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [SmallLevelFourPrimeRates.rational_power 2 3 13 5
    (by decide) (by decide) (by decide) (by decide) _ _ (rates_factor i)]
  rfl

#print axioms rates_injective
#print axioms sum_curve

end SmallLevelTwentySixContinuationRates
