module

public import QuantitativeMaassRawOriginalFiniteTraceV1
public import QuantitativeMaassRawReconstructionAccuracyV1
public import QuantitativeEulerEndpointSandwichCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch
variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

theorem reconstructedFilterExpression_mass (e : Sector N) (s : ℝ) (T : Expression) :
    expressionBound (reconstructedFilterExpression A P e s T)=
      expressionBound (expression A P (NeZero.pos N) s e)^2*expressionBound T := by
  simp only [reconstructedFilterExpression,expressionBound_compose,expressionBound_adjoint]
  ring

theorem reconstructedFilterExpression_matrix (e : Sector N) (s : ℝ) (T : Expression)
    {B C : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hu : ExpressionMatrixBound (expression A P (NeZero.pos N) s e) C) (ht : ExpressionMatrixBound T B) :
    ExpressionMatrixBound (reconstructedFilterExpression A P e s T) (4*B*C^2) := by
  have hh := hu.compose (ht.compose hu.adjoint hC) (by positivity)
  have he : 2*C*(2*B*C)=4*B*C^2 := by ring
  rw [he] at hh
  exact hh

/-- One horizon envelope controls both costs of the actual reconstructed
sandwich, uniformly over sectors and any finite filter within its envelope. -/
theorem exists_horizon_sandwich_cost {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,∀ e : Sector N,∀ T : Expression,
      expressionBound T≤Real.exp (Real.exp (a*(4:ℝ)^n)) →
      ExpressionMatrixBound T (Real.exp (Real.exp (a*(4:ℝ)^n))) →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let E := reconstructedFilterExpression A P e s T
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨c,hc,hu⟩ := exists_horizon_cost A P (NeZero.pos N) hK
  refine ⟨a+c+7,by positivity,?_⟩
  intro n e T ht htm s E
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hd := QuantitativeEulerEndpointCommonReconstruction.double_exp_sandwich_cost ha hc hR
  have hm := reconstructedFilterExpression_matrix A P e s T
    (Real.exp_pos _).le (Real.exp_pos _).le (hu n e).2 htm
  refine ⟨?_,hm.mono hd⟩
  change expressionBound (reconstructedFilterExpression A P e s T)≤_
  rw [reconstructedFilterExpression_mass]
  have hmass := mul_le_mul
    (pow_le_pow_left₀ (expressionBound_nonneg _) (hu n e).1 2) ht
    (expressionBound_nonneg _) (by positivity : 0≤Real.exp (Real.exp (c*(4:ℝ)^n))^2)
  apply hmass.trans
  apply le_trans _ hd
  nlinarith only [mul_nonneg (Real.exp_pos (Real.exp (a*(4:ℝ)^n))).le
    (sq_nonneg (Real.exp (Real.exp (c*(4:ℝ)^n))))]


#print axioms reconstructedFilterExpression_mass
#print axioms reconstructedFilterExpression_matrix
#print axioms exists_horizon_sandwich_cost
end QuantitativeMaass.RawCommonReconstruction
