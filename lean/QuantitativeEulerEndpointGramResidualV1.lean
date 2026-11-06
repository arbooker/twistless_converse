module

public import QuantitativeEulerEndpointPolynomialResidualV1
public import QuantitativeEulerEndpointPhysicalOriginalKillsV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointResidual
open scoped Classical
variable {A : Type*} [CStarAlgebra A]

/-- Gram residuals are controlled by the original row residuals, without
requiring any row to annihilate the truncated solution exactly. -/
theorem gram_residual {ι : Type*} [Fintype ι] (P E : A) (R : ι → A)
    (hP : ‖P‖≤1) (hPE : P*E=E) :
    ‖(∑ i,star (R i*P)*(R i*P))*E‖≤∑ i,‖R i‖*‖R i*E‖ := by
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [mul_assoc,mul_assoc,hPE]
  have hrow : ‖R i*P‖≤‖R i‖ := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (R i)])
  exact (norm_mul_le _ _).trans (by rw [norm_star]; exact mul_le_mul_of_nonneg_right hrow (norm_nonneg _))

theorem weighted_gram_residual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P E : A) (R : ι → κ → A) (w : ι → ℝ) (c : ℝ)
    (hP : ‖P‖≤1) (hPE : P*E=E) :
    ‖(c • ∑ i,w i • ∑ j,star (R i j*P)*(R i j*P))*E‖≤
      |c| * ∑ i,|w i| * ∑ j,‖R i j‖*‖R i j*E‖ := by
  rw [smul_mul_assoc,norm_smul,Real.norm_eq_abs,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [smul_mul_assoc,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (gram_residual P E (R i) hP hPE) (abs_nonneg _)

#print axioms gram_residual
#print axioms weighted_gram_residual
end QuantitativeEulerEndpointResidual
namespace QuantitativeEulerEndpointPhysicalGram
open AsymptoticFiniteBranch QuantitativeHolomorphic QuantitativeEulerEndpointBandExpression
open QuantitativeEulerEndpointResidual

/-- Physical weighted original-row residual bound with explicit weights. -/
theorem physical_weighted_gram_residual (ε H : ℝ) (m : ℕ)
    (T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (E : ι → κ → Expression) (w : ι → ℝ) (c : ℝ)
    (hPT : holomorphicSum (unitExpression ε H) m*T=T) :
    ‖holomorphicSum (QuantitativeEulerEndpointWeightedExpression.weightedGram (unitExpression ε H) E w c) m*T‖≤
      |c| * ∑ i,|w i| * ∑ j,‖holomorphicSum (E i j) m‖*‖holomorphicSum (E i j) m*T‖ := by
  rw [QuantitativeEulerEndpointWeightedExpression.holomorphic_weightedGram]
  exact weighted_gram_residual _ T (fun i j => holomorphicSum (E i j) m) w c
    ((holomorphicSum_norm_le _ _).trans (le_of_eq (unit_mass ε H))) hPT

#print axioms physical_weighted_gram_residual
end QuantitativeEulerEndpointPhysicalGram
