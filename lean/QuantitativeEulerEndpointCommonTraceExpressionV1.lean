module

public import QuantitativeEulerEndpointWeightedTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticCylinder
open AsymptoticObservation AsymptoticDiagonalTrace AsymptoticFourierNorm AsymptoticCylinderModeComparison
open AsymptoticFiniteBranch QuantitativeEulerEndpointWeightedTrace
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

def lowerHeight (s : ℝ) : ℝ :=
  lowerCutoff A P 2 (Real.exp (-8*s)) (newtonDepth A P 2 (Real.exp (-8*s)))

theorem lowerHeight_pos (s : ℝ) : 0<lowerHeight A P s := (scheduled_error A P s).2.1

theorem physicalCylinder_norm (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    ‖physicalCylinder A P hN s e h‖≤1 := polynomialNormalizedReconstruction_norm_le _
      (scaledCutFiniteCountReconstruction_norm_le A hN P h e _ _ _) _

theorem physicalCylinder_left_height (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) :
    (upperProjection (lowerHeight A P s)).comp (physicalCylinder A P hN s e h)=physicalCylinder A P hN s e h :=
  Sharp.finiteNormalizedCount_left_height A hN P h e _ _ _ _

def sandwichExpression (hN : 0<N) (s : ℝ) (e : Sector N) (T : Expression) : Expression :=
  composeExpression (expression A P hN s e) (composeExpression T (adjointExpression (expression A P hN s e)))

theorem sandwichExpression_physical (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) (T : Expression) :
    holomorphicSum (sandwichExpression A P hN s e T) (h+1)=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        (((physicalCylinder A P hN s e h).comp
          ((QuantitativeEulerEndpointApproximateTrace.terminalCompression A P (holomorphicSum T (h+1))).comp
            (physicalCylinder A P hN s e h).adjoint)).comp AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint) := by
  simp only [sandwichExpression,holomorphicSum_compose,holomorphicSum_adjoint,physicalCylinder_realization,
    QuantitativeEulerEndpointApproximateTrace.terminalCompression,adjoint_comp,adjoint_adjoint,comp_assoc]

theorem sandwichExpression_lifted_trace (hN : 0<N) (s : ℝ) (e : Sector N) (h : ℕ) (T : Expression) (H : ℝ) :
    AsymptoticUnweightedKernel.liftedTrace h (AsymptoticReconstructedCount.parameters A P).epsilon_pos
      (holomorphicSum (retainedExpression (lowerHeight A P s) H (sandwichExpression A P hN s e T)) (h+1))=
      upperCutTrace (physicalCylinder A P hN s e h)
        (QuantitativeEulerEndpointApproximateTrace.terminalCompression A P (holomorphicSum T (h+1)))
        (2*h) 0 (by positivity : 0<4*Real.pi) (AsymptoticReconstructedCount.parameters A P).epsilon_pos H := by
  rw [holomorphicSum_retainedExpression,holomorphic_corner,sandwichExpression_physical,retained_lift_trace]
  rw [retained_sandwich _ _ _ _ (physicalCylinder_left_height A P hN s e h)]
  rfl

def weightedTraceError (s : ℝ) (h : ℕ) : ℝ :=
  Real.exp ((2*lowerModeCoefficient A P+|lowerInverseGrowthConstant A P 0|)*s^4)*(Real.sqrt (2*h+2:ℝ))⁻¹

theorem physicalCylinder_weighted_trace_error (hN : 0<N) {s : ℝ} (hs : 1≤s) (e : Sector N) (h : ℕ)
    (F : AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε →L[ℂ]
      AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε)
    (hF : ‖F‖≤1) (H : ℝ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ‖upperCutTrace (physicalCylinder A P hN s e h) F (2*h) (P'.s+4)
      (by positivity : 0<4*Real.pi) P'.epsilon_pos H-
      upperCutTrace (physicalCylinder A P hN s e h) F (2*h) 0
      (by positivity : 0<4*Real.pi) P'.epsilon_pos H‖/(2*h+2:ℝ)≤weightedTraceError A P s h := by
  intro P'
  have hh := upper_weighted_difference (2*h) (P'.s+4) P'.epsilon_pos (lowerHeight_pos A P s) H
    (physicalCylinder A P hN s e h) F (physicalCylinder_norm A P hN s e h) hF
    (physicalCylinder_left_height A P hN s e h)
  have he : _≤weightedTraceError A P s h := lower_mode_sharp A P hs h
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  exact hh.trans he

#print axioms sandwichExpression_physical
#print axioms sandwichExpression_lifted_trace
#print axioms physicalCylinder_weighted_trace_error
end QuantitativeEulerEndpointCommonReconstruction
