module

public import QuantitativeMaassMetricPowerExpressionCostV1
public import QuantitativeMaassRationalExpressionHeightV1
public import QuantitativeMaassRawReconstructedFilterCostV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass
open AsymptoticFiniteBranch QuantitativeHolomorphic

private theorem one_add_exp_le {z : ℝ} (hz : 0≤z) : 1+Real.exp z≤Real.exp (z+1) := by
  have h1 : 1≤Real.exp z := Real.one_le_exp hz
  have h2 : 2≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  rw [Real.exp_add]
  nlinarith

theorem double_exp_metric_power_cost {a K x : ℝ} (ha : 0≤a) (hK : 1≤K) (hx : 1≤x)
    (m : ℕ) (hm : (m:ℝ)≤x) :
    1+(K*Real.exp (Real.exp (a*x)))^m≤Real.exp (Real.exp ((a+K+3)*x)) := by
  have hk0 : 0≤K := zero_le_one.trans hK
  have hx0 : 0≤x := zero_le_one.trans hx
  have he1 : 1≤Real.exp (a*x) := Real.one_le_exp (mul_nonneg ha hx0)
  have hb : K*Real.exp (Real.exp (a*x))≤Real.exp (K+Real.exp (a*x)) := by
    rw [Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith [Real.add_one_le_exp K]
  have hp := pow_le_pow_left₀ (show 0≤K*Real.exp (Real.exp (a*x)) by positivity) hb m
  rw [←Real.exp_nat_mul] at hp
  have hz0 : 0≤(m:ℝ)*(K+Real.exp (a*x)) := by positivity
  have hbase : K+Real.exp (a*x)≤Real.exp ((a+K+1)*x) := by
    calc
      _ ≤ (K+1)*Real.exp (a*x) := by nlinarith
      _ ≤ Real.exp (K+1)*Real.exp (a*x) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (K+1)]
      _ = Real.exp (K+1+a*x) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hmx : (m:ℝ)≤Real.exp x := hm.trans (by linarith [Real.add_one_le_exp x])
  have hz : (m:ℝ)*(K+Real.exp (a*x))≤Real.exp ((a+K+2)*x) := by
    calc
      _ ≤ Real.exp x*Real.exp ((a+K+1)*x) := mul_le_mul hmx hbase (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hz1 : (m:ℝ)*(K+Real.exp (a*x))+1≤Real.exp ((a+K+3)*x) := by
    calc
      _ ≤ Real.exp ((a+K+2)*x)+1 := add_le_add hz le_rfl
      _ ≤ Real.exp ((a+K+2)*x+1) := by
        simpa only [add_comm] using one_add_exp_le (show 0≤(a+K+2)*x by positivity)
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact (add_le_add le_rfl hp).trans ((one_add_exp_le hz0).trans (Real.exp_le_exp.mpr hz1))

/-- Degree 2^n preserves the same double-exponential horizon cost for the
literal metric polynomial, including all integer-matrix heights. -/
theorem exists_metric_horizon_cost (D : Expression) {a : ℝ} (ha : 0≤a) :
    ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,∀ F : Expression,
      expressionBound F≤Real.exp (Real.exp (a*(4:ℝ)^n)) →
      ExpressionMatrixBound F (Real.exp (Real.exp (a*(4:ℝ)^n))) →
      expressionBound (metricPowerExpression D F (2^n))≤Real.exp (Real.exp (C*(4:ℝ)^n)) ∧
      ExpressionMatrixBound (metricPowerExpression D F (2^n)) (Real.exp (Real.exp (C*(4:ℝ)^n))) := by
  obtain ⟨B,hB,hD⟩ := expression_matrix_bound_exists D
  let K := 8*B^2+2
  have hK : 1≤K := by dsimp only [K]; nlinarith [sq_nonneg B]
  refine ⟨a+K+3,by positivity,?_⟩
  intro n F hF hFm
  have hm : ((2^n:ℕ):ℝ)≤(4:ℝ)^n := by
    push_cast
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hx : 1≤(4:ℝ)^n := one_le_pow₀ (by norm_num)
  have he1 : 1≤Real.exp (Real.exp (a*(4:ℝ)^n)) := Real.one_le_exp (Real.exp_pos _).le
  have hb := double_exp_metric_power_cost ha hK hx (2^n) hm
  constructor
  · apply (metricPowerExpression_mass_le D F (2^n)).trans
    apply le_trans _ hb
    apply add_le_add le_rfl
    apply pow_le_pow_left₀ (add_nonneg zero_le_one (expressionBound_nonneg F))
    have hk2 : 2≤K := by dsimp only [K]; nlinarith [sq_nonneg B]
    nlinarith
  · have hh := metricPowerExpression_matrix D F he1 hB hD hFm (2^n)
    apply hh.mono
    have hp : (8*B^2*Real.exp (Real.exp (a*(4:ℝ)^n)))^(2^n)≤
        (K*Real.exp (Real.exp (a*(4:ℝ)^n)))^(2^n) := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp only [K]
      nlinarith [Real.exp_pos (Real.exp (a*(4:ℝ)^n))]
    linarith

#print axioms double_exp_metric_power_cost
#print axioms exists_metric_horizon_cost
end QuantitativeMaass
