module

public import QuantitativeHolomorphicNewtonCoefficientsV1
public import QuantitativeMaassStrongNewtonScheduleV1
public import QuantitativeMaassNewtonSourceCostV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Filter QuantitativeHolomorphic
open scoped Topology

namespace QuantitativeMaass.Strong

/-- The scheduled actual Newton degree and coefficient cost both fit the
proved squared triple-logarithmic exponential compression regime. -/
theorem bandNewtonDepth_source_cost :
    ∀ᶠ t in atTop,
      ((inverseSqrtPolynomial (bandNewtonDepth t)).natDegree:ℝ)≤2*strongScale t ∧
      ((inverseSqrtPolynomial (bandNewtonDepth t)).support.card:ℝ)*
        (∑ j∈(inverseSqrtPolynomial (bandNewtonDepth t)).support,
          ((inverseSqrtPolynomial (bandNewtonDepth t)).coeff j)^2)≤
        Real.exp ((2*Real.log 48)*strongScale t) := by
  filter_upwards [bandNewtonDepth_cost_bound] with t ht
  let n := bandNewtonDepth t
  have hdeg : (inverseSqrtPolynomial n).natDegree≤4^n := by
    have hd := inverseSqrtPolynomial_degree_bound n
    have hp : (3:ℕ)^n≤4^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
    omega
  constructor
  · exact (by exact_mod_cast hdeg : ((inverseSqrtPolynomial n).natDegree:ℝ)≤(4:ℝ)^n).trans ht
  · apply (inverseSqrtPolynomial_source_cost n).trans
    have heq : (48:ℝ)^(4^n)=Real.exp (((4^n:ℕ):ℝ)*Real.log 48) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<48)]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right ht (Real.log_nonneg (by norm_num : (1:ℝ)≤48))
    push_cast
    nlinarith only [hh]


#print axioms bandNewtonDepth_source_cost
end QuantitativeMaass.Strong
