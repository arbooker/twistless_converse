module
public import SmallLevelThirtyFourContinuationMinorMMMTheoryV4
public import SmallLevelThirtyFourContinuationMinorMMPTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourScaledContinuationMinor
open Complex SmallLevelFourPrimeRates SmallLevelPrimeRates

section MMM
open SmallLevelThirtyFourContinuationMinorMMM

theorem mmm_scaled_sum_curve (c : Fin 167→ℂ) (u v : ℂ) (m : ℕ) (s : ℂ) :
    (∑ i,(c i*u^(powers i).1*v^(powers i).2.2.1)*(rates i:ℂ)^(s-(m:ℂ)))=
      ∑ i,c i*monomial (powers i) (u*parameter 2 m s) (parameter 3 m s)
        (v*parameter 17 m s) (parameter 5 m s) := by
  rw [sum_curve]
  apply Finset.sum_congr rfl
  intro i _
  simp only [SmallLevelFourPrimeRates.monomial,mul_zpow]
  ring

theorem mmm_nonzero_on_scaled_curve (a b u v : ℂ) (m : ℕ) :
    ∃ s : ℂ,minor (u*parameter 2 m s) (parameter 3 m s)
      (v*parameter 17 m s) (parameter 5 m s) a b≠0 := by
  obtain ⟨s,hs⟩:=exponential_sum_nonzero rates rates_injective
    (fun i => coefficients a b i*u^(powers i).1*v^(powers i).2.2.1) 0
    (by norm_num [coefficients,powers]) m
  rw [mmm_scaled_sum_curve,minor_sum] at hs
  exact ⟨s,hs⟩
end MMM

section MMP
open SmallLevelThirtyFourContinuationMinorMMP

theorem mmp_scaled_sum_curve (c : Fin 87→ℂ) (u v : ℂ) (m : ℕ) (s : ℂ) :
    (∑ i,(c i*u^(powers i).1*v^(powers i).2.2.1)*(rates i:ℂ)^(s-(m:ℂ)))=
      ∑ i,c i*monomial (powers i) (u*parameter 2 m s) (parameter 3 m s)
        (v*parameter 17 m s) (parameter 5 m s) := by
  rw [sum_curve]
  apply Finset.sum_congr rfl
  intro i _
  simp only [SmallLevelFourPrimeRates.monomial,mul_zpow]
  ring

theorem mmp_nonzero_on_scaled_curve (a b u v : ℂ) (hv : v≠0) (m : ℕ) :
    ∃ s : ℂ,minor (u*parameter 2 m s) (parameter 3 m s)
      (v*parameter 17 m s) (parameter 5 m s) a b≠0 := by
  obtain ⟨s,hs⟩:=exponential_sum_nonzero rates rates_injective
    (fun i => coefficients a b i*u^(powers i).1*v^(powers i).2.2.1) 0
    (by norm_num [coefficients,powers,hv]) m
  rw [mmp_scaled_sum_curve,minor_sum] at hs
  exact ⟨s,hs⟩
end MMP

#print axioms mmm_nonzero_on_scaled_curve
#print axioms mmp_nonzero_on_scaled_curve
end SmallLevelThirtyFourScaledContinuationMinor
