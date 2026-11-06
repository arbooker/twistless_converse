module
public import QuantitativeArithmeticSmallLevelTwentySevenPrimeRateShiftV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

/-- The exact rate substitution in every lower Taylor layer, with the
Euler parameters held fixed. -/
theorem primeRate_sub_nat (p κ : ℝ) (hp : 0<p) (s : ℂ) (j : ℕ) :
    primeRate p κ (s-(j:ℂ))=primeRate p κ s/(p:ℂ)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show s-((j+1:ℕ):ℂ)=(s-(j:ℂ))-1 by push_cast; ring]
    rw [primeRate_sub_one p κ hp,ih,div_div,pow_succ]

theorem primeRate_resonance_layer (p : ℝ) (hp : 0<p) (m j : ℕ) :
    primeRate p m ((m:ℂ)+1-(j:ℂ))=(p:ℂ)/(p:ℂ)^j := by
  rw [primeRate_sub_nat p m hp]
  have h : primeRate p m ((m:ℂ)+1)=(p:ℂ) := by
    unfold primeRate
    simp only [Complex.ofReal_natCast,add_sub_cancel_left,mul_one]
    rw [← Complex.ofReal_exp,Real.exp_log hp]
  rw [h]

#print axioms primeRate_sub_nat
#print axioms primeRate_resonance_layer
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
