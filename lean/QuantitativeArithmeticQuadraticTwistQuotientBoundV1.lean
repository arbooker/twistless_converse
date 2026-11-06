module

public import QuantitativeArithmeticQuadraticTwistQuotientGeometryV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticQuadraticTwistQuotient

open Complex Set Metric FinitenessFiniteOrder

private theorem quotient_norm {x y b : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hxy : x*y=b) (hx : δ ≤ ‖x‖) : ‖y‖ ≤ δ⁻¹ * ‖b‖ := by
  have hn := congrArg norm hxy
  rw [norm_mul] at hn
  have ht : δ*‖y‖ ≤ ‖b‖ := by nlinarith [norm_nonneg y]
  rw [inv_mul_eq_div, le_div_iff₀ hδ]
  nlinarith

/-- An entire quotient by one exponential-linear factor has a global
finite-order envelope. The bound across every denominator zero is supplied
by the maximum-modulus principle, not a growth assumption on the quotient. -/
theorem quotient_envelope {a c : ℂ} (ha : a ≠ 0) {A G : ℂ → ℂ}
    (hG : Differentiable ℂ G)
    (hAG : ∀ z : ℂ, (1-c*exp (a*z))*G z=A z)
    {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hA : ∀ z : ℂ, ‖A z‖ ≤ Real.exp (C*(1+‖z‖)^d)) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧ ∀ z : ℂ,
      ‖G z‖ ≤ K * Real.exp (C*(1+‖z‖+R)^d) := by
  obtain ⟨δ,hδ,hcircle⟩ := exponential_circle_lower
  let r : ℝ := ‖a‖⁻¹
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hr : 0 < r := inv_pos.mpr ha'
  let K : ℝ := 4+δ⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, 2*r, hK, by positivity, ?_⟩
  intro z
  let E : ℝ := Real.exp (C*(1+‖z‖+2*r)^d)
  have hbound : ∀ v : ℂ, ‖v‖ ≤ ‖z‖+2*r → ‖A v‖ ≤ E := by
    intro v hv
    apply (hA v).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) d) hC
  by_cases hz : ‖1-c*exp (a*z)‖ ≤ 1/4
  · obtain ⟨w, hw, hzw⟩ := nearby_zero a c z ha hz
    have hzw' : ‖z-w‖ < r := by
      change ‖z-w‖ ≤ (3/8) / ‖a‖ at hzw
      rw [div_eq_mul_inv] at hzw
      change ‖z-w‖ ≤ (3/8)*r at hzw
      linarith
    have hsphere : ∀ v ∈ frontier (ball w r), ‖G v‖ ≤ K*E := by
      intro v hv
      have hv' : ‖v-w‖ = r := by
        simpa only [mem_sphere, dist_eq_norm] using frontier_ball_subset_sphere hv
      have hunit : ‖a*(v-w)‖ = 1 := by
        rw [norm_mul,hv']
        exact mul_inv_cancel₀ ha'.ne'
      have hd : δ ≤ ‖1-c*exp (a*v)‖ := by
        rw [denominator_at_zero a c w v hw]
        exact hcircle _ hunit
      have hvz : ‖v‖ ≤ ‖z‖+2*r := by
        have ht := norm_add_le (v-w) (w-z)
        have hwz : ‖w-z‖ < r := by simpa only [norm_sub_rev] using hzw'
        have ht' := norm_add_le (v-z) z
        rw [sub_add_sub_cancel] at ht
        rw [sub_add_cancel] at ht'
        linarith
      calc
        ‖G v‖ ≤ δ⁻¹ * ‖A v‖ := quotient_norm hδ (hAG v) hd
        _ ≤ δ⁻¹ * E := mul_le_mul_of_nonneg_left (hbound v hvz) (inv_nonneg.mpr hδ.le)
        _ ≤ K*E := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
          (Real.exp_pos _).le
    exact norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG.diffContOnCl hsphere
      (subset_closure (by simpa only [mem_ball,dist_eq_norm] using hzw'))
  · have hd : (1/4 : ℝ) ≤ ‖1-c*exp (a*z)‖ := le_of_lt (lt_of_not_ge hz)
    calc
      ‖G z‖ ≤ (1/4 : ℝ)⁻¹ * ‖A z‖ := quotient_norm (by norm_num) (hAG z) hd
      _ ≤ 4*E := by
        norm_num only [one_div, inv_inv]
        exact mul_le_mul_of_nonneg_left (hbound z (by linarith)) (by norm_num)
      _ ≤ K*E := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith [inv_pos.mpr hδ])
        (Real.exp_pos _).le

#print axioms quotient_envelope

end QuantitativeArithmeticQuadraticTwistQuotient
