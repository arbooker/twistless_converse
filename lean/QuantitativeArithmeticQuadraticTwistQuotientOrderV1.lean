module

public import QuantitativeArithmeticQuadraticTwistQuotientBoundV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistQuotient

open Complex FinitenessOriginalInput FinitenessInputBounds FinitenessFiniteOrder

/-- Entire division by an exponential-linear factor preserves finite order.
The divisor can have infinitely many zeros; no bound on the quotient is an
input. Entireness of the quotient remains an explicit hypothesis. -/
theorem finiteOrder_of_exponential_factor {a c : ℂ} (ha : a ≠ 0) {A G : ℂ → ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ z : ℂ, (1-c*exp (a*z))*G z=A z) : FiniteOrder G := by
  obtain ⟨C,hC,d,hbound⟩ := finiteOrder_bound hAc hA
  obtain ⟨K,R,hK,hR,hGR⟩ := quotient_envelope ha hG hAG hC hbound
  apply bound_finiteOrder
  refine ⟨K+C*(1+R)^d, by positivity, d, ?_⟩
  intro z
  have hz : 1 ≤ (1+‖z‖)^d := one_le_pow₀ (by linarith [norm_nonneg z])
  have hpower : (1+‖z‖+R)^d ≤ (1+R)^d*(1+‖z‖)^d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [norm_nonneg z]
  calc
    ‖G z‖ ≤ K*Real.exp (C*(1+‖z‖+R)^d) := hGR z
    _ ≤ Real.exp K * Real.exp (C*(1+‖z‖+R)^d) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp K]) (Real.exp_pos _).le
    _ = Real.exp (K+C*(1+‖z‖+R)^d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((K+C*(1+R)^d)*(1+‖z‖)^d) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpower hC,
        mul_le_mul_of_nonneg_left hz hK]

/-- The level22 denominator, with either sign (indeed any complex scalar).
The center may be any complex number. -/
theorem finiteOrder_of_two_factor (σ m : ℂ) {A G : ℂ → ℂ}
    (hAc : Continuous A) (hA : FiniteOrder A) (hG : Differentiable ℂ G)
    (hAG : ∀ z : ℂ, (1+σ*(2 : ℂ)^(m-z))*G z=A z) : FiniteOrder G := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (ne_of_gt (Real.log_pos (by norm_num)))
  apply finiteOrder_of_exponential_factor (a := -(Real.log 2 : ℂ))
    (c := -σ*exp ((Real.log 2 : ℂ)*m)) (neg_ne_zero.mpr hl) hAc hA hG
  intro z
  convert hAG z using 2
  rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    show log (2 : ℂ) = (Real.log 2 : ℂ) from
      (ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm]
  rw [show (Real.log 2 : ℂ)*(m-z)=(Real.log 2 : ℂ)*m + -(Real.log 2 : ℂ)*z by ring,
    exp_add]
  ring

#print axioms finiteOrder_of_exponential_factor
#print axioms finiteOrder_of_two_factor

end QuantitativeArithmeticQuadraticTwistQuotient
