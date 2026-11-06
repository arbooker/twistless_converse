module

public import QuantitativeEulerEndpointActualFiniteSectorComparisonV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic AsymptoticFiniteBranch

/-- Multiplying the filter cost by the squared reconstruction cost
preserves the double-exponential dependence on the block horizon. -/
theorem double_exp_sandwich_cost {a c R : ℝ} (ha : 0≤a) (hc : 0≤c) (hR : 1≤R) :
    4*Real.exp (Real.exp (a*R))*Real.exp (Real.exp (c*R))^2≤
      Real.exp (Real.exp ((a+c+7)*R)) := by
  have hR0 : 0≤R := by linarith
  have hE : 1≤Real.exp ((a+c)*R) := Real.one_le_exp (by positivity)
  have h₁ : Real.exp (a*R)≤Real.exp ((a+c)*R) := Real.exp_le_exp.mpr (by nlinarith)
  have h₂ : Real.exp (c*R)≤Real.exp ((a+c)*R) := Real.exp_le_exp.mpr (by nlinarith)
  have hs := QuantitativeEulerEndpointPolynomialGrowth.scaled_exp_le
    (a:=a+c) (by norm_num : (0:ℝ)≤7) hR
  have he : (7+(a+c))*R=(a+c+7)*R := by ring
  rw [he] at hs
  calc
    _ ≤ Real.exp 4*Real.exp (Real.exp (a*R))*Real.exp (Real.exp (c*R))^2 := by
      gcongr
      linarith [Real.add_one_le_exp (4:ℝ)]
    _ = Real.exp (4+Real.exp (a*R)+2*Real.exp (c*R)) := by
      rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- One horizon envelope controls both costs of the actual reconstructed
sandwich, uniformly over sectors and any finite filter within its envelope. -/
theorem exists_horizon_sandwich_cost (hN : 0<N) {K a : ℝ} (hK : 0≤K) (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,∀ e : Sector N,∀ T : Expression,
      expressionBound T≤Real.exp (Real.exp (a*(4:ℝ)^n)) →
      ExpressionMatrixBound T (Real.exp (Real.exp (a*(4:ℝ)^n))) →
      let s := Real.exp ((K+1)*(4:ℝ)^n)
      let E := sandwichExpression A P hN s e T
      expressionBound E≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound E (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨c,hc,hu⟩ := exists_horizon_cost A P hN hK
  refine ⟨a+c+7,by positivity,?_⟩
  intro n e T ht htm s E
  have hR : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have hd := double_exp_sandwich_cost ha hc hR
  have hm := sandwichExpression_matrix A P hN s e T
    (Real.exp_pos _).le (Real.exp_pos _).le (hu n e).2 htm
  refine ⟨?_,hm.mono hd⟩
  change expressionBound (sandwichExpression A P hN s e T)≤_
  rw [sandwichExpression_mass]
  have hmass := mul_le_mul
    (pow_le_pow_left₀ (expressionBound_nonneg _) (hu n e).1 2) ht
    (expressionBound_nonneg _) (by positivity : 0≤Real.exp (Real.exp (c*(4:ℝ)^n))^2)
  apply hmass.trans
  apply le_trans _ hd
  nlinarith only [mul_nonneg (Real.exp_pos (Real.exp (a*(4:ℝ)^n))).le
    (sq_nonneg (Real.exp (Real.exp (c*(4:ℝ)^n))))]

#print axioms double_exp_sandwich_cost
#print axioms exists_horizon_sandwich_cost
end QuantitativeEulerEndpointCommonReconstruction
