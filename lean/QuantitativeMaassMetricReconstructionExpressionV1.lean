module

public import QuantitativeMaassMetricPowerExpressionV1
public import QuantitativeMaassTerminalPowerTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticFiniteBranch QuantitativeHolomorphic ContinuousLinearMap
open QuantitativeEulerEndpointTerminalAlgebra QuantitativeEulerEndpointRegularBase
open AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

/-- The finite metric reconstruction uses the same scale as the physical
source polynomial. -/
def metricReconstructionExpression (D R : Expression) : Expression :=
  scaleExpression (Real.sqrt (expressionMetricScale D):ℂ) (composeExpression D R)

theorem metricReconstructionExpression_regular (D R : Expression) (z : UpperHalfPlane) :
    regularSum (metricReconstructionExpression D R) z=
      Real.sqrt (expressionMetricScale D) • (regularSum D z*regularSum R z) := by
  rw [metricReconstructionExpression,regularSum_scale,regularSum_compose]
  ext x : 1
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (Real.sqrt (expressionMetricScale D))
    ((regularSum D z*regularSum R z) x)).symm

theorem metricReconstructionExpression_norm (D R : Expression)
    (hR : ∀ x,‖regularSum R x‖≤1) (x : UpperHalfPlane) :
    ‖regularSum (metricReconstructionExpression D R) x‖≤1 := by
  rw [metricReconstructionExpression_regular,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hn : ‖regularSum D x*regularSum R x‖≤expressionBound D :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (hR x) (norm_nonneg _)).trans
      (by simpa only [mul_one] using regularSum_norm_le D x))
  have hs := Real.sq_sqrt (expressionMetricScale_pos D).le
  have hb := expressionMetricScale_bound D (expressionBound_nonneg D) le_rfl
  have hbound : Real.sqrt (expressionMetricScale D)*expressionBound D≤1 := by
    nlinarith [Real.sqrt_nonneg (expressionMetricScale D),expressionBound_nonneg D]
  exact (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)).trans hbound

theorem metricReconstructionExpression_right {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
    (D R : Expression)
    (hR : ∀ x,regularSum R x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum R x)
    (x : UpperHalfPlane) :
    regularSum (metricReconstructionExpression D R) x*
      AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=
        regularSum (metricReconstructionExpression D R) x := by
  rw [metricReconstructionExpression_regular]
  ext v : 1
  have hh := congrArg (fun B => B v) (hR x)
  change regularSum R x (AsymptoticOrbitDiagonal.corner (terminalRegion A P) x v)=regularSum R x v at hh
  change Real.sqrt (expressionMetricScale D) • (regularSum D x
    (regularSum R x (AsymptoticOrbitDiagonal.corner (terminalRegion A P) x v)))=_
  rw [hh]
  rfl

/-- Any contractive reconstruction with terminal input has finite regular
Gram trace, independently of its output support. -/
theorem right_terminal_gram_trace_finite {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
    (U : Expression) (hU : ∀ x,‖regularSum U x‖≤1)
    (hr : ∀ x,regularSum U x*AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=regularSum U x) :
    trace volume (fun x => (regularSum U x).adjoint.comp (regularSum U x))<∞ := by
  apply (AsymptoticOrbitDiagonal.trace_le_corner volume (terminal_measurable A P)
    (fun x => (regularSum U x).adjoint.comp (regularSum U x)) (C:=1) ?_ ?_).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (terminal_finite A P))
  · intro x
    have hh := opNorm_comp_le (regularSum U x).adjoint (regularSum U x)
    rw [ContinuousLinearMap.adjoint.norm_map] at hh
    nlinarith [hU x,norm_nonneg (regularSum U x)]
  · intro x
    change (regularSum U x).adjoint*(regularSum U x)*
      AsymptoticOrbitDiagonal.corner (terminalRegion A P) x=_
    rw [mul_assoc,hr]
    rfl

#print axioms metricReconstructionExpression_regular
#print axioms metricReconstructionExpression_norm
#print axioms metricReconstructionExpression_right
#print axioms right_terminal_gram_trace_finite
end QuantitativeMaass
