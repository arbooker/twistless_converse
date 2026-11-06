module
public import SmallLevelTwentySixFactorIndexPhysicalSeriesV4
public import SmallLevelTwentySixPariLinearFactorExclusionV1
public import SmallLevelTwentySixRootTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixPariGenericBranches
open SmallLevelPrimeRates SmallLevelTwentySixPariFirstChart
open SmallLevelTwentySixPariFinalFactors

/-- The generic eliminant and low curve leave only the certified degree21
factor. Deriving the eliminant and handling the exceptional coefficient locus
from original pole equations remain separate obligations. -/
theorem degree21_of_eliminant (m : ℕ) (s u z w a b θ : ℂ)
    (hu : u=1 ∨ u= -1) (hx2 : u*parameter 2 m s≠2)
    (hc : lowCurve (u*parameter 2 m s) ((parameter 3 m s)^2) z w a b θ=0)
    (he : SmallLevelTwentySixPariIdentity022.p4
      (u*parameter 2 m s) ((parameter 3 m s)^2) z w a b θ=0) :
    SmallLevelTwentySixRoot.p21.eval (u*parameter 2 m s)=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hun : ‖u‖=1 := by rcases hu with rfl|rfl <;> norm_num
  have hx0 : u*parameter 2 m s≠0 := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have specialize (X Y Z W A B T : ℂ) :
      lowCurve X Y Z W A B T=lowCurve X Y 0 0 0 0 0 := by
    unfold lowCurve SmallLevelTwentySixPariIdentity007.p1
    rfl
  have hc0 : lowCurve (u*parameter 2 m s) ((parameter 3 m s)^2) 0 0 0 0 0=0 :=
    (specialize _ _ _ _ _ _ _).symm.trans hc
  rcases branches _ _ _ _ _ _ _ he with h2|h1|h0|h5|h6|h7|h21
  · exact False.elim (hx2 h2)
  · exact False.elim (SmallLevelTwentySixPariLinearFactorExclusion.no_signed_linear_parameters
      m s u z w a b θ hu (Or.inl h1) hc)
  · exact False.elim (hx0 h0)
  · exact False.elim (SmallLevelTwentySixPariLinearFactorExclusion.no_signed_linear_parameters
      m s u z w a b θ hu (Or.inr h5) hc)
  · apply False.elim
    apply SmallLevelTwentySixFactor6Physical.no_signed_low_curve (s-(m:ℂ)) u hun
    · simpa only [parameter,Nat.cast_ofNat] using h6
    · rw [SmallLevelTwentySixRoot.parameter_three_squared] at hc0
      simpa only [parameter,Nat.cast_ofNat] using hc0
  · apply False.elim
    apply SmallLevelTwentySixFactor7Physical.no_signed_low_curve (s-(m:ℂ)) u hun
    · simpa only [parameter,Nat.cast_ofNat] using h7
    · rw [SmallLevelTwentySixRoot.parameter_three_squared] at hc0
      simpa only [parameter,Nat.cast_ofNat] using hc0
  · exact root_branch _ h21

#print axioms degree21_of_eliminant
end SmallLevelTwentySixPariGenericBranches
