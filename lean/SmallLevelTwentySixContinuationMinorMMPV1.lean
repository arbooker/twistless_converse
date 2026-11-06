module
public import SmallLevelTwentySixContinuationRatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelTwentySixContinuationMinorMMP
open Complex SmallLevelFourPrimeRates SmallLevelPrimeRates

open SmallLevelTwentySixContinuationRates

def coefficients (a : ℂ) : Fin 27→ℂ :=
  ![0,((-1)),(2) + (2*a^2),((-1)) + (1*a^2),((-3)*a) + (2*a^3),(1*a),((-1)) + (1*a^2),((-2)*a),((-1)),((-3)),((-1)),((-2)*a),((-1)*a),((-1)),((-1)),(5*a) + ((-1)*a^3),(3) + ((-1)*a^2),(1*a),(1),(2),((-3)) + (2*a^2),(1*a),((-1)),((-2)),(2*a),(2),((-2))]

def minor (X Y Z a : ℂ) : ℂ :=
  ((-1)*Z) + (2*Y^2) + (2*Y^2*a^2) + ((-1)*Y^2*Z) + (1*Y^2*Z*a^2) + ((-3)*Y^3*a) + (2*Y^3*a^3) + (1*Y^3*Z*a) + ((-1)*Y^4) + (1*Y^4*a^2) + ((-2)*Y^5*a) + ((-1)*Y^6) + ((-3)*X) + ((-1)*X*Z) + ((-2)*X*Y*a) + ((-1)*X*Y*Z*a) + ((-1)*X*Y^2) + ((-1)*X*Y^2*Z) + (5*X*Y^3*a) + ((-1)*X*Y^3*a^3) + (3*X*Y^4) + ((-1)*X*Y^4*a^2) + (1*X*Y^5*a) + (1*X*Y^6) + (2*X^2) + ((-3)*X^2*Y^2) + (2*X^2*Y^2*a^2) + (1*X^2*Y^3*a) + ((-1)*X^2*Y^4) + ((-2)*X^3) + (2*X^3*Y^3*a) + (2*X^3*Y^4) + ((-2)*X^5)

theorem minor_sum (X Y Z W a : ℂ) :
    (∑ i,coefficients a i*SmallLevelFourPrimeRates.monomial (powers i) X Y Z W)=minor X Y Z a := by
  norm_num [Fin.sum_univ_succ,coefficients,powers,SmallLevelFourPrimeRates.monomial,minor] <;> ring

theorem minor_nonzero_on_curve (a : ℂ) (m : ℕ) :
    ∃ s : ℂ,minor (parameter 2 m s) (parameter 3 m s) (parameter 13 m s) a≠0 := by
  obtain ⟨s,hs⟩:=exponential_sum_nonzero rates rates_injective (coefficients a) 9 (by norm_num [coefficients]) m
  refine ⟨s,?_⟩
  rw [sum_curve,minor_sum] at hs
  exact hs

theorem minor_determinant (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) :
    minor X Y Z a=X^2*Y^2*Z*((((1)/(X^2*Z)) + ((1*Y*a)/(X^2*Z)) + (((-1)*Y^3*a)/(X^2*Z)) + (((-1)*Y^4)/(X^2*Z)) + ((1*Y^2)/(X*Z)) + ((1*Y^3*a)/(X*Z)) + ((1*Y^4)/(X*Z)) + ((1)/(Z)) + (((-1)*X)/(Z)))*(((1)/(X^2*Y^2)) + ((3)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-3)*Y*a)/(X^2)) + ((2)/(X*Y^2)) + ((1*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-1)*Y*a)/(X)) + ((4)/(Y^2)) + (2) + ((2*X)/(Y^2)) + ((2*X^2)/(Y^2)))-((((-1))/(X^2*Y^2)) + (((-1))/(X^2)) + ((1*a^2)/(X^2)) + ((1*Y*a)/(X^2)) + (((-1))/(X*Y^2)) + (((-1)*a)/(X*Y)) + (((-1))/(X)))*((((-1))/(X^2*Z)) + (((-1)*Y*a)/(X^2*Z)) + (((-2)*Y^2)/(X^2*Z)) + ((1*Y^3*a)/(X^2*Z)) + ((3*Y^4)/(X^2*Z)) + (((-1))/(X*Z)) + (((-1)*Y*a)/(X*Z)) + (((-1)*Y^2)/(X*Z)) + (((-2)*Y^4)/(X*Z)) + (((-4))/(Z)) + ((-1)) + (((-2)*Y*a)/(Z)) + ((1*Y^2)/(Z)) + (((-1)*Y^3*a)/(Z)) + (((-1)*Y^4)/(Z)) + (((-2)*X)/(Z)) + ((1*X*Y*a)/(Z)) + (((-1)*X*Y^2)/(Z)))) := by
  unfold minor
  field_simp [hX,hY,hZ,hW]
  ring

#print axioms minor_nonzero_on_curve
#print axioms minor_determinant

end SmallLevelTwentySixContinuationMinorMMP
