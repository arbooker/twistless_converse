module

public import QuantitativeMaassMetricCapRegularDiagonalV1
public import QuantitativeMaassLocalRegularDifferenceV1
public import QuantitativeMaassCrossRegularIntegralV1
public import QuantitativeMaassCompactExpressionKernelTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open QuantitativeHolomorphic
open scoped ComplexConjugate ENNReal
namespace QuantitativeMaass

/-- The input corner disappears on its own region, leaving the exact
inverse-cap and inverse-metric diagonal coefficient. -/
theorem metricCappedExpression_regular_integral {N : ℕ} (M : ScalarCylinderMetric N)
    (δ : ℝ) (ν J : ℕ) (E : Expression) (S : Set ℍ) (hS : MeasurableSet S) (w : ℂ) :
    (∫ x in S,(matrix (regularSum
      (compactInputExpression S hS (metricCappedExpression M δ ν J E)) x) 1 1*w).re)=
    ∫ x in S,(metricCapCoefficient M δ ν J x*conj (metricCapCoefficient M δ ν J x)*
      matrix (regularSum E x) 1 1*w).re := by
  apply setIntegral_congr_fun hS
  intro x hx
  dsimp only
  rw [compactInputExpression,CrossCompactBranch.inputCorner_regular_diagonal S hS _ x hx,
    metricCappedExpression_regular_diagonal]

/-- The local weighted regular estimate bounds the difference of the
actual finite-expression integral and its canonical counterpart. -/
theorem metric_cap_local_regular_difference {N : ℕ} (M : ScalarCylinderMetric N)
    (δ : ℝ) (ν J : ℕ) (E : Expression) (Q : ℍ→Space→L[ℂ]Space) (err : ℝ)
    (hweighted : ∀ (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
      (∀ x,‖B x‖≤L) → |signedTrace volume (fun x => B x*(regularSum E x-Q x))|≤L*err)
    (hmQ : Measurable (fun x => matrix (Q x) 1 1))
    (A : ℝ) (hE : ∀ x,‖regularSum E x‖≤A) (hQ : ∀ x,‖Q x‖≤A)
    (S : Set ℍ) (hS : MeasurableSet S) (hSf : volume S<∞) (w : ℂ) :
    let k := metricCapCoefficient M δ ν J
    let B := (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*M.lower⁻¹
    |(∫ x in S,(matrix (regularSum
        (compactInputExpression S hS (metricCappedExpression M δ ν J E)) x) 1 1*w).re)-
      (∫ x in S,(k x*conj (k x)*matrix (Q x) 1 1*w).re)|≤B^2*‖w‖*err := by
  intro k B
  have hk : Measurable k := metricCapCoefficient_measurable M δ ν J
  have hb (x : ℍ) : ‖k x*conj (k x)*w‖≤B^2*‖w‖ := by
    rw [norm_mul,norm_mul,Complex.norm_conj,←pow_two]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (metricCapCoefficient_bound M δ ν J x) 2) (norm_nonneg w)
  have hh := RawCommonReconstruction.local_regular_difference_bound (regularSum E) Q err hweighted
    (regularSum_matrix_measurable E 1 1) hmQ A hE hQ S hS hSf
    (fun x => k x*conj (k x)*w)
    ((hk.mul (Complex.continuous_conj.measurable.comp hk)).mul measurable_const)
    (B^2*‖w‖) (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hb
  rw [metricCappedExpression_regular_integral]
  simpa only [k,mul_assoc,mul_left_comm,mul_comm] using hh

#print axioms metricCappedExpression_regular_integral
#print axioms metric_cap_local_regular_difference
end QuantitativeMaass
