module
public import SmallLevelTwentySixContinuationMinorMMMV1
public import SmallLevelTwentySixContinuationMinorMMPV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixScaledContinuationMinor
open Complex SmallLevelFourPrimeRates SmallLevelPrimeRates SmallLevelTwentySixContinuationRates

/-- Constant rescalings of the2- and13-parameters preserve the distinct
exponential rates; only the finite coefficient vector changes. -/
theorem scaled_sum_curve (c : Fin 27→ℂ) (u v : ℂ) (m : ℕ) (s : ℂ) :
    (∑ i,(c i*u^(powers i).1*v^(powers i).2.2.1)*(rates i:ℂ)^(s-(m:ℂ)))=
      ∑ i,c i*monomial (powers i) (u*parameter 2 m s) (parameter 3 m s)
        (v*parameter 13 m s) (parameter 5 m s) := by
  rw [sum_curve]
  apply Finset.sum_congr rfl
  intro i _
  simp only [SmallLevelFourPrimeRates.monomial,mul_zpow]
  ring

theorem scaled_sum_nonzero (c : Fin 27→ℂ) (i : Fin 27) (u v : ℂ)
    (hc : c i*u^(powers i).1*v^(powers i).2.2.1≠0) (m : ℕ) :
    ∃ s : ℂ,(∑ i,c i*monomial (powers i) (u*parameter 2 m s) (parameter 3 m s)
      (v*parameter 13 m s) (parameter 5 m s))≠0 := by
  obtain ⟨s,hs⟩:=exponential_sum_nonzero rates rates_injective
    (fun i => c i*u^(powers i).1*v^(powers i).2.2.1) i hc m
  exact ⟨s,by simpa only [scaled_sum_curve] using hs⟩

theorem mmm_nonzero_on_scaled_curve (a u v : ℂ) (m : ℕ) :
    ∃ s : ℂ,SmallLevelTwentySixContinuationMinorMMM.minor
      (u*parameter 2 m s) (parameter 3 m s) (v*parameter 13 m s) a≠0 := by
  obtain ⟨s,hs⟩:=scaled_sum_nonzero (SmallLevelTwentySixContinuationMinorMMM.coefficients a) 0 u v
    (by norm_num [SmallLevelTwentySixContinuationMinorMMM.coefficients,powers]) m
  exact ⟨s,by simpa only [SmallLevelTwentySixContinuationMinorMMM.minor_sum] using hs⟩

theorem mmp_nonzero_on_scaled_curve (a u v : ℂ) (hu : u≠0) (m : ℕ) :
    ∃ s : ℂ,SmallLevelTwentySixContinuationMinorMMP.minor
      (u*parameter 2 m s) (parameter 3 m s) (v*parameter 13 m s) a≠0 := by
  obtain ⟨s,hs⟩:=scaled_sum_nonzero (SmallLevelTwentySixContinuationMinorMMP.coefficients a) 9 u v
    (by norm_num [SmallLevelTwentySixContinuationMinorMMP.coefficients,powers,hu]) m
  exact ⟨s,by simpa only [SmallLevelTwentySixContinuationMinorMMP.minor_sum] using hs⟩

#print axioms mmm_nonzero_on_scaled_curve
#print axioms mmp_nonzero_on_scaled_curve
end SmallLevelTwentySixScaledContinuationMinor
