module
public import QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticTheoryV4
public import SmallLevelTwentySixPariGenericBranchesV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPPhysical
open SmallLevelPrimeRates SmallLevelTwentySixPariFirstChart SmallLevelTwentySixPariFinalFactors

/-- Physical dispatch for the reduced MMP eliminant. The polynomial
eliminant and the two remaining branch implications must still be derived
from the original row equations; this helper does not assert them. -/
theorem no_signed_factored_system (m : ℕ) (s u : ℂ)
    (hu : u=1 ∨ u= -1)
    (hx2 : u*parameter 2 m s≠2)
    (hc : lowCurve (u*parameter 2 m s) ((parameter 3 m s)^2) 0 0 0 0 0=0)
    (he : (u*parameter 2 m s)^2*(u*parameter 2 m s-2)^7*
      (u*parameter 2 m s-1)^6*((u*parameter 2 m s)^2-5*(u*parameter 2 m s)+8)*
      (factor6 (u*parameter 2 m s))^2*(factor7 (u*parameter 2 m s))^2*
      factor21 (u*parameter 2 m s)=0)
    (hquad : (u*parameter 2 m s)^2-5*(u*parameter 2 m s)+8=0 →
      (parameter 3 m s)^2=9)
    (h21 : factor21 (u*parameter 2 m s)=0 →
      SmallLevelTwentySixRoot.q20.eval (u*parameter 2 m s)=(parameter 3 m s)^2) : False := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hun : ‖u‖=1 := by rcases hu with rfl|rfl <;> norm_num
  have hx0 := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hc0 : lowCurve (u*(2:ℂ)^(s-(m:ℂ))) ((9:ℂ)^(s-(m:ℂ))) 0 0 0 0 0=0 := by
    rw [SmallLevelTwentySixRoot.parameter_three_squared] at hc
    simpa only [parameter,Nat.cast_ofNat] using hc
  have he' : u*parameter 2 m s=0 ∨ u*parameter 2 m s-2=0 ∨
      u*parameter 2 m s-1=0 ∨ (u*parameter 2 m s)^2-5*(u*parameter 2 m s)+8=0 ∨
      factor6 (u*parameter 2 m s)=0 ∨ factor7 (u*parameter 2 m s)=0 ∨
      factor21 (u*parameter 2 m s)=0 := by
    rcases mul_eq_zero.mp he with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · rcases mul_eq_zero.mp h with h | h
              · exact Or.inl ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h)
              · exact Or.inr (Or.inl ((pow_eq_zero_iff (by decide : (7:ℕ)≠0)).mp h))
            · exact Or.inr (Or.inr (Or.inl ((pow_eq_zero_iff (by decide : (6:ℕ)≠0)).mp h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  rcases he' with h0|h2|h1|hq|h6|h7|hp
  · exact hx0 h0
  · exact hx2 (sub_eq_zero.mp h2)
  · exact SmallLevelTwentySixPariLinearFactorExclusion.no_signed_linear_parameters
      m s u 0 0 0 0 0 hu (Or.inl (sub_eq_zero.mp h1)) hc
  · exact QuantitativeArithmeticSmallLevelTwentySixMMPQuadratic.no_signed_parameter_quadratic
      m s u hu hq (hquad hq)
  · apply SmallLevelTwentySixFactor6Physical.no_signed_low_curve (s-(m:ℂ)) u hun
    · simpa only [parameter,Nat.cast_ofNat] using h6
    · exact hc0
  · apply SmallLevelTwentySixFactor7Physical.no_signed_low_curve (s-(m:ℂ)) u hun
    · simpa only [parameter,Nat.cast_ofNat] using h7
    · exact hc0
  · exact SmallLevelTwentySixRoot.no_signed_parameter_locus m s u hu
      (root_branch _ hp) (h21 hp)

#print axioms no_signed_factored_system
end QuantitativeArithmeticSmallLevelTwentySixMMPPhysical
