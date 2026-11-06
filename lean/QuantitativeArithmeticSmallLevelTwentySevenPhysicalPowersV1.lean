module
public import QuantitativeArithmeticSmallLevelTwentySevenPhysicalReconstructionV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open Complex

/-- Exact conversion from geometric Taylor dilation to the four exponential
variables in the checked reconstruction certificates. -/
theorem four_prime_power (e₂ e₃ e₅ e₇ : ℤ) (κ : ℝ) (s : ℂ) :
    (((2:ℝ)^e₂*3^e₃*5^e₅*7^e₇:ℝ):ℂ)^(s-(κ:ℂ))=
      primeRate 2 κ s^e₂*primeRate 3 κ s^e₃*
        primeRate 5 κ s^e₅*primeRate 7 κ s^e₇ := by
  have hp : 0<(2:ℝ)^e₂*3^e₃*5^e₅*7^e₇ := by positivity
  have hl : Real.log ((2:ℝ)^e₂*3^e₃*5^e₅*7^e₇)=
      (e₂:ℝ)*Real.log 2+(e₃:ℝ)*Real.log 3+(e₅:ℝ)*Real.log 5+(e₇:ℝ)*Real.log 7 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_zpow]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le,hl]
  push_cast
  simp only [primeRate,← Complex.exp_int_mul,← Complex.exp_add]
  congr 1
  ring

#print axioms four_prime_power
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
