module

public import QuantitativeEulerEndpointActualUnweightedSectorTraceV1
public import QuantitativeEulerEndpointTraceMassV1
public import QuantitativeHolomorphicGrowingPeriodizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem sandwichExpression_mass (hN : 0<N) (s : ℝ) (e : Sector N) (T : Expression) :
    expressionBound (sandwichExpression A P hN s e T)=
      expressionBound (expression A P hN s e)^2*expressionBound T := by
  simp only [sandwichExpression,expressionBound_compose,expressionBound_adjoint]
  ring

theorem sandwichExpression_matrix (hN : 0<N) (s : ℝ) (e : Sector N) (T : Expression)
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hu : ExpressionMatrixBound (expression A P hN s e) C) (ht : ExpressionMatrixBound T B) :
    ExpressionMatrixBound (sandwichExpression A P hN s e T) (4*B*C^2) := by
  have hh := hu.compose (ht.compose hu.adjoint hC) (by positivity)
  have he : 2*C*(2*B*C)=4*B*C^2 := by ring
  rw [he] at hh
  exact hh

#print axioms sandwichExpression_mass
#print axioms sandwichExpression_matrix
end QuantitativeEulerEndpointCommonReconstruction

namespace QuantitativeEulerEndpointApproximateTrace
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticFiniteBranch AsymptoticUnweightedKernel AsymptoticRegularTrace
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule QuantitativeEulerEndpointCommonReconstruction
open QuantitativeEulerEndpointSector QuantitativeEulerEndpointTraceMass MeasureTheory
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- The original sector dimension is compared to the retained regular
trace of the SAME finite branch sandwich, with all analytic errors explicit.
The sole remaining finite-weight hypothesis is the displayed scalar size test. -/
theorem sector_finrank_le_retained_regular (hN : 0<N) {s : ℝ} (hs : 1≤s) (h : ℕ) (e : Sector N)
    (T : Expression) (hT : 0≤holomorphicSum T (h+1)) (hTn : ‖holomorphicSum T (h+1)‖≤1) (δ : ℝ)
    (herr : ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hN h e-
      normalizedPhysicalSectorProjection A P hN h e‖≤δ)
    {B : ℝ} (hB : 0≤B) (hm : ExpressionMatrixBound (sandwichExpression A P hN s e T) B)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(B*(Real.exp (16*s)+2))≤1) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let Y := lowerHeight A P s
    let H := Real.exp (16*s)
    let E := sandwichExpression A P hN s e T
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P'.s) e):ℝ)/(2*h+2:ℝ)≤
      signedTrace volume (regularSum (retainedExpression Y H E))/(4*Real.pi)+
        retainedTraceError A P s h+weightedTraceError A P s h+
        expressionBound E*uniformRetainedTraceError (B*(H+2)) Y H h (periodizationSet Y H).card := by
  intro P' Y H E
  have hd := sector_finrank_le_unweighted_expression A P hN hs h e T hT hTn δ herr
  have hb := retained_expression_mass_uniform_trace_bound E P'.epsilon_pos (by positivity)
    (lowerHeight_pos A P s) (Real.exp_pos (16*s)) h hsmall (periodizationSet Y H)
    (periodizationSet_far Y H) (fun b hb hne => hm.geometry hB Y H (periodizationSet Y H) b hb hne)
  have hk : (0:ℝ)<2*h+2 := by positivity
  have hd' := (div_le_div_of_nonneg_right hd hk.le)
  rw [add_div,mul_div_cancel_left₀ _ hk.ne'] at hd'
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hb
  have hl := le_abs_self (AsymptoticUnweightedKernel.liftedTrace h P'.epsilon_pos
    (holomorphicSum (retainedExpression Y H E) (h+1))/(2*h+2:ℝ)-
      signedTrace volume (regularSum (retainedExpression Y H E))/(4*Real.pi))
  linarith only [hd',hb,hl]

#print axioms sector_finrank_le_retained_regular
end QuantitativeEulerEndpointApproximateTrace
