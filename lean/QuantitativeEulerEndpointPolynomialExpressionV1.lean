module

public import QuantitativeEulerEndpointCornerPolynomialV1
public import QuantitativeHolomorphicMatrixExpressionV1
public import QuantitativeHolomorphicNewtonPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPolynomialExpression
open AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial

/-- Algebraic polynomial expansion; it is followed by the actual corner
projection before being used for a finite-corner update. -/
def polynomialExpression (e : Expression) (q : ℝ[X]) : Expression :=
  sumExpressions q.support (fun i => scaleExpression (q.coeff i:ℂ) (powerExpression e i))

def cornerPolynomial (u e : Expression) (q : ℝ[X]) : Expression :=
  composeExpression (polynomialExpression e q) u

theorem holomorphic_polynomial (e : Expression) (q : ℝ[X]) (m : ℕ) :
    holomorphicSum (polynomialExpression e q) m=aeval (holomorphicSum e m) q := by
  rw [polynomial_aeval_sum]
  simp only [polynomialExpression,holomorphicSum_sumExpressions,holomorphicSum_scale,holomorphicSum_power]
  apply Finset.sum_congr rfl
  intro i _
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (q.coeff i) ((holomorphicSum e m)^i)).symm

theorem regular_polynomial (e : Expression) (q : ℝ[X]) (x : UpperHalfPlane) :
    regularSum (polynomialExpression e q) x=aeval (regularSum e x) q := by
  rw [polynomial_aeval_sum]
  simp only [polynomialExpression,regularSum_sumExpressions,regularSum_scale,regularSum_power]
  apply Finset.sum_congr rfl
  intro i _
  exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (q.coeff i) ((regularSum e x)^i)).symm

theorem holomorphic_cornerPolynomial (u e : Expression) (q : ℝ[X]) (m : ℕ) :
    holomorphicSum (cornerPolynomial u e q) m=
      aeval (holomorphicSum e m) q*holomorphicSum u m := by
  rw [cornerPolynomial,holomorphicSum_compose,holomorphic_polynomial]
  rfl

theorem regular_cornerPolynomial (u e : Expression) (q : ℝ[X]) (x : UpperHalfPlane) :
    regularSum (cornerPolynomial u e q) x=aeval (regularSum e x) q*regularSum u x := by
  rw [cornerPolynomial,regularSum_compose,regular_polynomial]
  rfl

theorem polynomial_mass (e : Expression) (q : ℝ[X]) :
    expressionBound (polynomialExpression e q)=∑ i∈q.support, |q.coeff i| *(expressionBound e)^i := by
  simp only [polynomialExpression,expressionBound_sumExpressions,expressionBound_scale,
    expressionBound_power,Complex.norm_real,Real.norm_eq_abs]

theorem polynomial_mass_le (e : Expression) (q : ℝ[X]) :
    expressionBound (polynomialExpression e q)≤
      (∑ i∈q.support, |q.coeff i|)*(max 1 (expressionBound e))^q.natDegree := by
  rw [polynomial_mass,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (pow_le_pow_left₀ (expressionBound_nonneg e) (le_max_right _ _) i).trans
    (pow_le_pow_right₀ (le_max_left _ _) (le_natDegree_of_ne_zero (mem_support_iff.mp hi)))

theorem corner_mass_le (u e : Expression) (q : ℝ[X]) :
    expressionBound (cornerPolynomial u e q)≤
      ((∑ i∈q.support, |q.coeff i|)*(max 1 (expressionBound e))^q.natDegree)*expressionBound u := by
  rw [cornerPolynomial,expressionBound_compose]
  exact mul_le_mul_of_nonneg_right (polynomial_mass_le e q) (expressionBound_nonneg u)

theorem polynomial_matrix {e : Expression} {B : ℝ} (hB : 0≤B)
    (he : ExpressionMatrixBound e B) (q : ℝ[X]) :
    ExpressionMatrixBound (polynomialExpression e q) ((2*max 1 B)^q.natDegree) := by
  apply expressionMatrixBound_sum
  intro i hi
  apply ((he.power hB i).scale (q.coeff i:ℂ)).mono
  have hbase : 1≤2*max 1 B := by linarith [le_max_left (1:ℝ) B]
  exact (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) B) (by norm_num)) i).trans
    (pow_le_pow_right₀ hbase (le_natDegree_of_ne_zero (mem_support_iff.mp hi)))

theorem corner_matrix {u e : Expression} {B U : ℝ} (hB : 0≤B) (hU : 0≤U)
    (he : ExpressionMatrixBound e B) (hu : ExpressionMatrixBound u U) (q : ℝ[X]) :
    ExpressionMatrixBound (cornerPolynomial u e q) (2*(2*max 1 B)^q.natDegree*U) :=
  (polynomial_matrix hB he q).compose hu hU

#print axioms holomorphic_cornerPolynomial
#print axioms regular_cornerPolynomial
#print axioms corner_mass_le
#print axioms corner_matrix
end QuantitativeEulerEndpointPolynomialExpression
