module
public import SmallLevelFourPrimeRatesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinor
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

def determinant (x y a : ℂ) : ℂ :=
  (a+x)*(a*x+x^2+1)*(-a*x*y+a*x+x^2*y+x^2-2)/x^5

def bases : Fin 11→ℚ := ![3,1,3/2,1/2,3/4,1/4,3/8,1/8,3/16,1/16,1/32]
def coefficients (a u : ℂ) : Fin 11→ℂ :=
  ![u,1,a*u,3*a,(1-a^2)*u,3*a^2-1,-a^3*u,a^3-2*a,-a^2*u,-a^2-2,-2*a]

theorem bases_injective : Function.Injective bases := by decide +kernel

theorem exponential_sum_exists (a u : ℂ) (hu : u≠0) (m : ℕ) :
    ∃ s : ℂ,(∑ j : Fin 11,coefficients a u j*(bases j:ℂ)^(s-(m:ℂ)))≠0 :=
  exponential_sum_nonzero bases bases_injective (coefficients a u) 0 hu m

def powers : Fin 11→ℤ×ℤ×ℤ :=
  ![(0,1,0),(0,0,0),(-1,1,0),(-1,0,0),(-2,1,0),(-2,0,0),
    (-3,1,0),(-3,0,0),(-4,1,0),(-4,0,0),(-5,0,0)]

theorem bases_factor (j : Fin 11) :
    bases j=(2:ℚ)^(powers j).1*(3:ℚ)^(powers j).2.1*(11:ℚ)^(powers j).2.2 := by
  fin_cases j <;> decide +kernel

theorem sum_identity (x y z a u : ℂ) (hx : x≠0) :
    (∑ j : Fin 11,coefficients a u j*SmallLevelPrimeRates.monomial (powers j) x y z)=
      determinant x (u*y) a := by
  norm_num [Fin.sum_univ_succ,coefficients,powers,SmallLevelPrimeRates.monomial,determinant]
  field_simp [hx]
  ring

theorem determinant_not_identically_zero (a u : ℂ) (hu : u≠0) (m : ℕ) :
    ∃ s : ℂ,determinant (parameter 2 m s) (u*parameter 3 m s) a≠0 := by
  obtain ⟨s,hs⟩ := exponential_sum_exists a u hu m
  refine ⟨s,?_⟩
  have hr (j : Fin 11) : (bases j:ℂ)^(s-(m:ℂ))=
      SmallLevelPrimeRates.monomial (powers j) (parameter 2 m s) (parameter 3 m s) (parameter 11 m s) :=
    SmallLevelPrimeRates.rational_power 2 3 11 (by decide) (by decide) (by decide) _ _ (bases_factor j) _
  simp_rw [hr] at hs
  rw [sum_identity _ _ _ _ _ (parameter_ne_zero 2 m (by decide) s)] at hs
  exact hs

#print axioms determinant_not_identically_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinor
