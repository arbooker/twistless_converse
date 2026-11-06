module
public import QuantitativeArithmeticSmallLevelTwentySevenSignedSourceV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages

theorem primeRate_sub_one (p κ : ℝ) (hp : 0<p) (s : ℂ) :
    primeRate p κ (s-1)=primeRate p κ s/(p:ℂ) := by
  unfold primeRate
  have he : (Real.log p:ℂ)*(s-1-(κ:ℂ))=(Real.log p:ℂ)*(s-(κ:ℂ))-(Real.log p:ℂ) := by ring
  rw [he,Complex.exp_sub,← Complex.ofReal_exp,Real.exp_log hp]

end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
namespace QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
open QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSmallLevelTwentySevenHeckeSource (point)
open QuantitativeArithmeticSevenLaurentRows

theorem lowerRates_physical (p : Poly) (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    eval (primeRate 2 m s) (primeRate 3 m s) (primeRate 5 m s) (primeRate 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 5:ℂ)*f 5) ((Real.sqrt 7:ℂ)*f 7)
      (fun j => SmallLevelAdditive.original (2*m) f (point j:ℝ) (s-1)) (lowerRates p)=
      physicalEval p m f (s-1) := by
  rw [eval_lowerRates]
  unfold physicalEval
  rw [primeRate_sub_one 2 m (by norm_num),primeRate_sub_one 3 m (by norm_num),
    primeRate_sub_one 5 m (by norm_num),primeRate_sub_one 7 m (by norm_num)]
  norm_num only [Complex.ofReal_ofNat]

#print axioms lowerRates_physical
end QuantitativeArithmeticSmallLevelTwentySevenSourceDispatch
