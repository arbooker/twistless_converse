module
public import QuantitativeArithmeticSmallLevelTwentySixMMPPhysicalEndgameV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticBranchV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPDegree21TheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminantTheoryV4
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPReducedSystem
open SmallLevelPrimeRates SmallLevelTwentySixPariFirstChart

/-- The reduced MMP system has no solution at the actual signed prime-power
parameters. Deriving its three equations from the original poles is separate. -/
theorem no_signed_parameters (m : ℕ) (s u z w a b t : ℂ)
    (hu : u=1 ∨ u= -1) (hx2 : u*parameter 2 m s≠2)
    (hlow : lowCurve (u*parameter 2 m s) ((parameter 3 m s)^2) z w a b t=0)
    (hfirst : SmallLevelTwentySixMMPPariTrace019.p6
      (u*parameter 2 m s) ((parameter 3 m s)^2) z w a b t=0)
    (hsecond : SmallLevelTwentySixMMPPariTrace031.p6
      (u*parameter 2 m s) ((parameter 3 m s)^2) z w a b t=0) : False := by
  apply QuantitativeArithmeticSmallLevelTwentySixMMPPhysical.no_signed_factored_system
    m s u hu hx2 hlow
  · exact QuantitativeArithmeticSmallLevelTwentySixMMPFinalEliminant.eliminant_zero
      _ _ z w a b t hlow hfirst hsecond
  · intro hq
    exact QuantitativeArithmeticSmallLevelTwentySixMMPQuadraticBranch.y_eq_nine
      _ _ z w a b t hlow hfirst hq
  · intro hq
    exact QuantitativeArithmeticSmallLevelTwentySixMMPDegree21.root_relation_of_first
      _ _ z w a b t hlow hfirst hq

#print axioms no_signed_parameters
end QuantitativeArithmeticSmallLevelTwentySixMMPReducedSystem
