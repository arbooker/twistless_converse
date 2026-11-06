module

public import QuantitativeArithmeticRetainedTerminalSandwichV1
public import QuantitativeArithmeticRetainedScheduledTraceV1
public import QuantitativeArithmeticRetainedCommonCostV1
public import QuantitativeEulerEndpointSandwichCostV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedNestedCountComparison
open MeasureTheory ContinuousLinearMap AsymptoticSectorSigns AsymptoticFiniteBranch
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFiniteTransport
open QuantitativeArithmeticRetainedPhysicalSector QuantitativeArithmeticRetainedNestedGeometricTrace
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeArithmeticRetainedTerminalSandwich
open QuantitativeArithmeticRetainedTraceComparison
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q}
    (A : Certificate N R₀ Q hQ) (hR₀ : ∀p∈R₀,p.Prime) (hN : 0<N) (P : Parameters A)

/-- Full original-sector rank versus the exact terminal trace, with separate
physical and regular residuals and explicit scalar geometric errors. -/
theorem sector_finrank_le_terminal (hdiv : ∀p∈R₀,p∣Q) (hbad : ∀p∈R₀,p∣N)
    {τ : ℝ} (hτ : 0<τ) (hτ1 : 2*τ≤1) {H : ℝ} (hH : 0<H)
    (h : ℕ) (e : Sector N) (T : Expression)
    (hT : 0≤holomorphicSum T (h+1)) (hTn : ‖holomorphicSum T (h+1)‖≤1)
    (a : Algebra A P) (ha : 0≤a ∧ a≤1)
    (hTr : ∀x,0≤regularSum T x ∧ regularSum T x≤1)
    (δphys δreg : ℝ)
    (herr : ‖holomorphicSum T (h+1)*normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad-
      normalizedPhysicalSectorProjection A P hR₀ hN h e hdiv hbad‖≤δphys)
    (hreg : ∀x,‖rep A P a x-regularSum T x‖≤δreg)
    {B : ℝ} (hB : 0≤B) (hm : ExpressionMatrixBound (sandwichExpression A hR₀ hN P τ e T) B)
    (hsmall : (h+1:ℝ)^(-(1/3:ℝ))*(B*(H+2))≤1) :
    let Y := lowerHeight A P τ
    let E := sandwichExpression A hR₀ hN P τ e T
    (1-δphys)*(Module.finrank ℂ (AsymptoticRamifiedSectors.sector N h (h+1+P.s) e):ℝ)/(2*h+2:ℝ)≤
      (tr A P a+δreg*P.ε⁻¹)/(4*Real.pi)+traceError A P τ H h+
      expressionBound E*uniformRetainedTraceError (B*(H+2)) Y H h (periodizationSet Y H).card := by
  intro Y E
  have hd := sector_finrank_le_retained_regular A hR₀ hN P hdiv hbad hτ hτ1 hH
    h e T hT hTn δphys herr hB hm hsmall
  have ht := normalized_sandwich_le_trace A P hR₀ hN a ha τ e T hTr δreg hreg Y H
  have ht' := div_le_div_of_nonneg_right ht (by positivity : (0:ℝ)≤4*Real.pi)
  linarith only [hd,ht']

theorem sandwichExpression_mass (τ : ℝ) (e : Sector N) (T : Expression) :
    expressionBound (sandwichExpression A hR₀ hN P τ e T)=
      expressionBound (normalizedExpression A P hR₀ hN τ e)^2*expressionBound T := by
  simp only [sandwichExpression,expressionBound_compose,expressionBound_adjoint]
  ring

theorem sandwichExpression_matrix (τ : ℝ) (e : Sector N) (T : Expression)
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hu : ExpressionMatrixBound (normalizedExpression A P hR₀ hN τ e) C)
    (ht : ExpressionMatrixBound T B) :
    ExpressionMatrixBound (sandwichExpression A hR₀ hN P τ e T) (4*B*C^2) := by
  have hh := hu.compose (ht.compose hu.adjoint hC) (by positivity)
  have he : 2*C*(2*B*C)=4*B*C^2 := by ring
  rw [he] at hh
  exact hh

/-- The complete finite sandwich has a double-exponential horizon cost,
uniform before the weight and sector are selected. -/
theorem exists_horizon_sandwich_cost {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀e : Sector N,∀T : Expression,
      expressionBound T≤Real.exp (Real.exp (a*(4:ℝ)^n)) →
      ExpressionMatrixBound T (Real.exp (Real.exp (a*(4:ℝ)^n))) →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let τ := QuantitativeArithmeticRetainedApproximationSchedule.tolerance s 0
      let E := sandwichExpression A hR₀ hN P τ e T
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨c,hc,hu⟩ := QuantitativeArithmeticRetainedCommonExpression.exists_horizon_cost A P hR₀ hN hK
  refine ⟨a+c+7,by positivity,?_⟩
  intro n e T ht htm s τ E
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hd := QuantitativeEulerEndpointCommonReconstruction.double_exp_sandwich_cost ha hc hR
  have he : QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ hN s e =
      normalizedExpression A P hR₀ hN τ e := by
    unfold QuantitativeArithmeticRetainedCommonExpression.expression
    congr 1
    dsimp only [τ,QuantitativeArithmeticRetainedApproximationSchedule.tolerance]
    norm_num
  have hu' := hu n e
  change expressionBound (QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ hN s e)≤_ ∧
    ExpressionMatrixBound (QuantitativeArithmeticRetainedCommonExpression.expression A P hR₀ hN s e) _ at hu'
  rw [he] at hu'
  have hm := sandwichExpression_matrix A hR₀ hN P τ e T
    (Real.exp_pos _).le (Real.exp_pos _).le hu'.2 htm
  refine ⟨?_,hm.mono hd⟩
  change expressionBound (sandwichExpression A hR₀ hN P τ e T)≤_
  rw [sandwichExpression_mass]
  have hmass := mul_le_mul
    (pow_le_pow_left₀ (expressionBound_nonneg _) hu'.1 2) ht
    (expressionBound_nonneg _) (by positivity : 0≤Real.exp (Real.exp (c*(4:ℝ)^n))^2)
  apply hmass.trans
  apply le_trans _ hd
  nlinarith only [mul_nonneg (Real.exp_pos (Real.exp (a*(4:ℝ)^n))).le
    (sq_nonneg (Real.exp (Real.exp (c*(4:ℝ)^n))))]

#print axioms sector_finrank_le_terminal
#print axioms sandwichExpression_mass
#print axioms sandwichExpression_matrix
#print axioms exists_horizon_sandwich_cost
end QuantitativeArithmeticRetainedNestedCountComparison
