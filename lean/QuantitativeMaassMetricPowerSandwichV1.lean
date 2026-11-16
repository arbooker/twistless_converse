module

public import QuantitativeMaassMetricReconstructionExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticFiniteBranch QuantitativeHolomorphic ContinuousLinearMap

theorem sqrt_scaled_sandwich {𝔄 : Type*} [CStarAlgebra 𝔄]
    (γ : ℝ) (hγ : 0≤γ) (D R T : 𝔄) :
    (Real.sqrt γ • (D*R))*T*star (Real.sqrt γ • (D*R))=
      γ • (D*(R*T*star R)*star D) := by
  simp only [star_smul,star_trivial,star_mul,smul_mul_assoc,mul_smul_comm,smul_smul,
    Real.mul_self_sqrt hγ,mul_assoc]

/-- The same literal common metric polynomial is the power filter of the
contractive finite metric reconstruction sandwich. -/
theorem metricPowerExpression_sandwich (D R T : Expression) (m : ℕ) (x : UpperHalfPlane) :
    regularSum (metricPowerExpression D (composeExpression R (composeExpression T (adjointExpression R))) m) x=
      1-(1-regularSum (metricReconstructionExpression D R) x*regularSum T x*
        (regularSum (metricReconstructionExpression D R) x).adjoint)^m := by
  simp only [metricPowerExpression_regular,scaledMetricPowerFilter,regularSum_compose,
    regularSum_compose,regularSum_adjoint,metricReconstructionExpression_regular]
  have h := sqrt_scaled_sandwich (expressionMetricScale D) (expressionMetricScale_pos D).le
    (regularSum D x) (regularSum R x) (regularSum T x)
  simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using!
    congrArg (fun B : RegularSpace→L[ℂ]RegularSpace => 1-(1-B)^m) h.symm

#print axioms sqrt_scaled_sandwich
#print axioms metricPowerExpression_sandwich
end QuantitativeMaass
