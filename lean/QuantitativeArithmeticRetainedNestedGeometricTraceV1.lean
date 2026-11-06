module

public import QuantitativeArithmeticRetainedTraceComparisonV1
public import QuantitativeArithmeticRetainedFiniteTransportV1
public import QuantitativeEulerEndpointTraceMassV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedNestedGeometricTrace
open ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder
open AsymptoticFiniteBranch AsymptoticUnweightedKernel AsymptoticRegularTrace
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteTransport QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedTraceComparison QuantitativeArithmeticRetainedWeightedTrace
open QuantitativeArithmeticRetainedPhysicalSector QuantitativeHolomorphic
open QuantitativeEulerEndpointTraceMass MeasureTheory
open QuantitativeEulerEndpointWeightedTrace QuantitativeHolomorphic.Schedule
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N) (P : Parameters A)

def sandwichExpression (τ : ℝ) (e : Sector N) (T : Expression) : Expression :=
  composeExpression (normalizedExpression A P hR₀ hN τ e)
    (composeExpression T (adjointExpression (normalizedExpression A P hR₀ hN τ e)))

theorem terminalCompression_norm_le
    (F : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space) :
    ‖terminalCompression A P F‖≤‖F‖ := by
  let S := AsymptoticCylinderTerminal.ambientLift P.ε
  have hi : ∀v,‖S v‖=‖v‖ := (norm_map_iff_adjoint_comp_self S).mpr
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
  have hn : ‖S‖≤1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    rw [hi,one_mul]
  have ha : ‖S.adjoint‖≤1 := by rwa [adjoint.norm_map]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans
  rw [one_mul]
  exact (opNorm_comp_le _ _).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg F))

theorem sandwichExpression_physical (τ : ℝ) (e : Sector N) (h : ℕ) (T : Expression) :
    holomorphicSum (sandwichExpression A hR₀ hN P τ e T) (h+1)=
      AsymptoticCylinderLift.lift.toContinuousLinearMap.comp
        (((physicalCylinder A hR₀ hN P τ e h).comp
          ((terminalCompression A P (holomorphicSum T (h+1))).comp
            (physicalCylinder A hR₀ hN P τ e h).adjoint)).comp
              AsymptoticCylinderLift.lift.toContinuousLinearMap.adjoint) := by
  simp only [sandwichExpression,holomorphicSum_compose,holomorphicSum_adjoint,
    physical_normalized,physicalCylinder,terminalCompression,adjoint_comp,adjoint_adjoint,comp_assoc]

theorem sandwichExpression_lifted_trace (τ H : ℝ) (e : Sector N) (h : ℕ) (T : Expression) :
    liftedTrace h P.epsilon_pos (holomorphicSum
      (retainedExpression (lowerHeight A P τ) H (sandwichExpression A hR₀ hN P τ e T)) (h+1))=
      upperCutTrace (physicalCylinder A hR₀ hN P τ e h)
        (terminalCompression A P (holomorphicSum T (h+1))) (2*h) 0
        (by positivity : 0<4*Real.pi) P.epsilon_pos H := by
  rw [holomorphicSum_retainedExpression,holomorphic_corner,sandwichExpression_physical,retained_lift_trace]
  rw [retained_sandwich _ _ _ _ (physicalCylinder_left_height A hR₀ hN P τ e h)]
  rfl

/-- The original coefficient-sector dimension, with its original degree,
is bounded by the trace of the same finite branch sandwich. -/
theorem sector_finrank_le_unweighted (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    {τ : ℝ} (hτ : 0<τ) (hτ1 : 2*τ≤1) {H : ℝ} (hH : 0<H)
    (h : ℕ) (e : Sector N) (T : Expression)
    (hT : 0≤holomorphicSum T (h+1)) (hTn : ‖holomorphicSum T (h+1)‖≤1) (δ : ℝ)
    (herr : ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-
      normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤δ) :
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      liftedTrace h P.epsilon_pos (holomorphicSum
        (retainedExpression (lowerHeight A P τ) H (sandwichExpression A hR₀ hN P τ e T)) (h+1))/(2*h+2:ℝ)+
      traceError A P τ H h := by
  have hd := ambient_sector_finrank_mul_le_trace A hR₀ P hdiv hbad hN h e
    (holomorphicSum T (h+1)) hT δ herr
  have ht := trace_le_unweighted A hR₀ hN P hτ hτ1 H hH h e
    (terminalCompression A P (holomorphicSum T (h+1)))
    ((terminalCompression_norm_le A P _).trans hTn)
  rw [sandwichExpression_lifted_trace]
  exact (div_le_div_of_nonneg_right hd (by positivity : (0:ℝ)≤2*h+2)).trans ht

/-- Geometric trace comparison for the literal retained-prime reconstruction.
All error terms and the finite-weight size test remain explicit. -/
theorem sector_finrank_le_retained_regular (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    {τ : ℝ} (hτ : 0<τ) (hτ1 : 2*τ≤1) {H : ℝ} (hH : 0<H)
    (h : ℕ) (e : Sector N) (T : Expression)
    (hT : 0≤holomorphicSum T (h+1)) (hTn : ‖holomorphicSum T (h+1)‖≤1) (δ : ℝ)
    (herr : ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-
      normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤δ)
    {B : ℝ} (hB : 0≤B) (hm : ExpressionMatrixBound (sandwichExpression A hR₀ hN P τ e T) B)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(B*(H+2))≤1) :
    let Y := lowerHeight A P τ
    let E := sandwichExpression A hR₀ hN P τ e T
    (1-δ)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      signedTrace volume (regularSum (retainedExpression Y H E))/(4*Real.pi)+traceError A P τ H h+
      expressionBound E*uniformRetainedTraceError (B*(H+2)) Y H h (periodizationSet Y H).card := by
  intro Y E
  have hd := sector_finrank_le_unweighted A hR₀ hN P hdiv hbad hτ hτ1 hH h e T hT hTn δ herr
  have hb := retained_expression_mass_uniform_trace_bound E P.epsilon_pos (by positivity)
    (lowerHeight_pos A P hτ) hH h hsmall (periodizationSet Y H)
    (periodizationSet_far Y H) (fun b hb hne => hm.geometry hB Y H (periodizationSet Y H) b hb hne)
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hb
  have hl := le_abs_self (liftedTrace h P.epsilon_pos
    (holomorphicSum (retainedExpression Y H E) (h+1))/(2*h+2:ℝ)-
      signedTrace volume (regularSum (retainedExpression Y H E))/(4*Real.pi))
  linarith only [hd,hb,hl]

#print axioms terminalCompression_norm_le
#print axioms sandwichExpression_physical
#print axioms sandwichExpression_lifted_trace
#print axioms sector_finrank_le_unweighted
#print axioms sector_finrank_le_retained_regular
end QuantitativeArithmeticRetainedNestedGeometricTrace
